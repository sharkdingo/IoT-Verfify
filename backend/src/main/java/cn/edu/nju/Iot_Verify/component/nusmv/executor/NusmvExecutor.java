package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * NuSMV 执行器
 * 职责：执行 NuSMV 批处理验证 和 交互式随机模拟
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class NusmvExecutor {

    private final NusmvConfig nusmvConfig;

    private static final String TIMEOUT_ENV_KEY = "NUSMV_TIMEOUT_MS";
    private static final int PROCESS_DESTROY_TIMEOUT_SECONDS = 5;
    private static final long READER_JOIN_TIMEOUT_MS = 5000;

    // NuSMV spec result patterns
    private static final Pattern SPEC_TRUE_PATTERN = Pattern.compile(
            "-- specification (.+?) is true", Pattern.CASE_INSENSITIVE);
    private static final Pattern SPEC_FALSE_PATTERN = Pattern.compile(
            "-- specification (.+?) is false", Pattern.CASE_INSENSITIVE);

    private volatile Semaphore executionSemaphore;

    // ==================== 批处理验证 ====================

    public NusmvResult execute(File smvFile) throws InterruptedException {
        if (smvFile == null || !smvFile.exists()) {
            return NusmvResult.error("NuSMV model file does not exist or is null");
        }

        boolean permitAcquired = acquireExecutionPermit();
        if (!permitAcquired) {
            return NusmvResult.busy("NuSMV execution is busy, please retry later");
        }

        List<String> command = buildCommand(smvFile, List.of());
        log.info("Executing NuSMV command: {}", String.join(" ", command));

        ProcessBuilder processBuilder = new ProcessBuilder(command);
        processBuilder.redirectErrorStream(true);

        Process process = null;
        try {
            process = processBuilder.start();
            long timeout = getTimeoutFromEnvironment();

            final Process finalProcess = process;
            StringBuilder outputBuilder = new StringBuilder();
            Thread outputThread = new Thread(() -> {
                try (BufferedReader reader = new BufferedReader(
                        new InputStreamReader(finalProcess.getInputStream(), StandardCharsets.UTF_8))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        outputBuilder.append(line).append("\n");
                    }
                } catch (IOException e) {
                    log.warn("Error reading NuSMV output: {}", e.getMessage());
                }
            }, "nusmv-batch-output");
            outputThread.start();

            boolean finished = process.waitFor(timeout, java.util.concurrent.TimeUnit.MILLISECONDS);

            if (!finished) {
                log.warn("NuSMV execution timed out after {}ms, destroying process", timeout);
                process.destroyForcibly();
                if (!process.waitFor(PROCESS_DESTROY_TIMEOUT_SECONDS, java.util.concurrent.TimeUnit.SECONDS)) {
                    log.error("Failed to destroy NuSMV process");
                }
                // 进程销毁后流会关闭，等待输出线程结束
                reclaimReaderThread(outputThread, process.getInputStream(), "merged-output");
                return NusmvResult.error("NuSMV execution timed out after " + timeout + "ms");
            }

            // 进程已正常结束，流一定会关闭，无需超时限制
            if (!waitReaderThreadCompletion(outputThread, process.getInputStream(), "merged-output")) {
                return NusmvResult.error("NuSMV output reader did not finish in time");
            }

            int exitCode = process.exitValue();
            String output = outputBuilder.toString();
            log.debug("NuSMV exit code: {}, output length: {}", exitCode, output.length());

            // 将 NuSMV 输出保存到 smv 文件同目录下的 output.txt
            saveOutputToFile(smvFile, output);

            if (exitCode != 0) {
                return NusmvResult.error("NuSMV exited with code " + exitCode + ": " + output);
            }

            // Parse per-spec results from output
            List<SpecCheckResult> specResults = parseSpecResults(output);
            return NusmvResult.success(output, specResults);

        } catch (IOException e) {
            log.error("Failed to execute NuSMV", e);
            return NusmvResult.error("Failed to execute NuSMV: " + e.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            log.warn("NuSMV execution interrupted");
            if (process != null) {
                process.destroyForcibly();
            }
            throw e;
        } finally {
            releaseExecutionPermit();
        }
    }

    // === Private methods ===

    private void saveOutputToFile(File smvFile, String output) {
        try {
            File outputFile = new File(smvFile.getParentFile(), "output.txt");
            try (java.io.PrintWriter writer = new java.io.PrintWriter(
                    new java.io.OutputStreamWriter(new java.io.FileOutputStream(outputFile), StandardCharsets.UTF_8))) {
                writer.print(output);
            }
            log.info("NuSMV output saved to: {}", outputFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save NuSMV output to file: {}", e.getMessage());
        }
    }

    /**
     * 构建 NuSMV 命令行。
     *
     * @param smvFile   模型文件
     * @param extraArgs 额外参数（如 "-int"），插入在 nusmvPath 与 smvFile 之间
     */
    private List<String> buildCommand(File smvFile, List<String> extraArgs) {
        String nusmvPath = nusmvConfig.getPath();
        String commandPrefix = nusmvConfig.getCommandPrefix();
        List<String> command = new ArrayList<>();
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("windows");

        // SECURITY: commandPrefix is passed to sh -c / cmd.exe /c and can execute arbitrary commands.
        // It MUST only come from trusted server-side configuration (application.yaml / env vars),
        // NEVER from user input.
        if (commandPrefix != null && !commandPrefix.isEmpty()) {
            StringBuilder fullCommand = new StringBuilder();
            fullCommand.append(commandPrefix).append(" ").append(quoteForShell(nusmvPath, isWindows));
            for (String arg : extraArgs) {
                fullCommand.append(" ").append(arg);
            }
            fullCommand.append(" ").append(quoteForShell(smvFile.getAbsolutePath(), isWindows));
            if (isWindows) {
                command.add("cmd.exe");
                command.add("/c");
                command.add(fullCommand.toString());
            } else {
                command.add("sh");
                command.add("-c");
                command.add(fullCommand.toString());
            }
            return command;
        }
        // No commandPrefix: invoke the executable directly via ProcessBuilder.
        // Do NOT wrap with cmd.exe /c — its quoting rules are fragile and can
        // cause the command to be misinterpreted (e.g. opening an interactive shell).
        command.add(nusmvPath);
        command.addAll(extraArgs);
        command.add(smvFile.getAbsolutePath());
        return command;
    }

    private String quoteForShell(String value, boolean isWindows) {
        if (value == null) return "";
        if (isWindows) {
            return '"' + value.replace("\"", "\\\"") + '"';
        }
        return '\'' + value.replace("'", "'\"'\"'") + '\'';
    }

    private long getTimeoutFromEnvironment() {
        try {
            String timeoutEnv = System.getenv(TIMEOUT_ENV_KEY);
            if (timeoutEnv != null && !timeoutEnv.isEmpty()) {
                return Long.parseLong(timeoutEnv);
            }
        } catch (NumberFormatException e) {
            log.warn("Invalid NUSMV_TIMEOUT_MS value, using config default: {}", nusmvConfig.getTimeoutMs());
        }
        return nusmvConfig.getTimeoutMs();
    }

    private boolean acquireExecutionPermit() throws InterruptedException {
        long timeoutMs = Math.max(0, nusmvConfig.getAcquirePermitTimeoutMs());
        return executionSemaphore().tryAcquire(timeoutMs, TimeUnit.MILLISECONDS);
    }

    private void releaseExecutionPermit() {
        Semaphore semaphore = executionSemaphore;
        if (semaphore != null) {
            semaphore.release();
        }
    }

    private Semaphore executionSemaphore() {
        if (executionSemaphore == null) {
            synchronized (this) {
                if (executionSemaphore == null) {
                    int maxConcurrent = Math.max(1, nusmvConfig.getMaxConcurrent());
                    executionSemaphore = new Semaphore(maxConcurrent, true);
                    log.info("NuSMV global concurrency cap initialized: {}", maxConcurrent);
                }
            }
        }
        return executionSemaphore;
    }

    // ==================== 交互式模拟 ====================

    /** NuSMV 交互模式提示符，需要从输出中过滤 */
    private static final Pattern NUSMV_PROMPT_PATTERN = Pattern.compile("^\\s*NuSMV\\s*>.*$");
    private static final String TRACE_SIMULATION_MARKER = "Trace Type: Simulation";

    /**
     * 以交互模式启动 NuSMV，执行随机模拟 N 步，返回模拟轨迹文本。
     *
     * 流程：go → pick_state -r → simulate -r -k N → show_traces → quit
     */
    public SimulationOutput executeInteractiveSimulation(File smvFile, int steps) throws InterruptedException {
        if (smvFile == null || !smvFile.exists()) {
            return SimulationOutput.error("NuSMV model file does not exist or is null");
        }

        boolean permitAcquired = acquireExecutionPermit();
        if (!permitAcquired) {
            return SimulationOutput.busy("NuSMV simulation is busy, please retry later");
        }

        List<String> command = buildCommand(smvFile, List.of("-int"));
        log.info("Executing NuSMV interactive simulation: {}", String.join(" ", command));

        ProcessBuilder processBuilder = new ProcessBuilder(command);
        // 不合并 stderr，以便区分错误信息
        processBuilder.redirectErrorStream(false);

        Process process = null;
        try {
            process = processBuilder.start();
            long timeout = getTimeoutFromEnvironment();

            final Process fp = process;
            StringBuilder stdoutBuilder = new StringBuilder();
            StringBuilder stderrBuilder = new StringBuilder();

            // 独立线程读 stdout，防止管道缓冲区满导致死锁
            Thread stdoutThread = new Thread(() -> {
                try (BufferedReader reader = new BufferedReader(
                        new InputStreamReader(fp.getInputStream(), StandardCharsets.UTF_8))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        stdoutBuilder.append(line).append("\n");
                    }
                } catch (IOException e) {
                    log.warn("Error reading NuSMV stdout: {}", e.getMessage());
                }
            }, "nusmv-sim-stdout");

            // 独立线程读 stderr
            Thread stderrThread = new Thread(() -> {
                try (BufferedReader reader = new BufferedReader(
                        new InputStreamReader(fp.getErrorStream(), StandardCharsets.UTF_8))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        stderrBuilder.append(line).append("\n");
                    }
                } catch (IOException e) {
                    log.warn("Error reading NuSMV stderr: {}", e.getMessage());
                }
            }, "nusmv-sim-stderr");

            stdoutThread.start();
            stderrThread.start();

            // 向 stdin 写入交互命令，然后关闭（NuSMV 收到 EOF 后会退出）
            try (OutputStream stdin = process.getOutputStream()) {
                String commands = "go\npick_state -r\nsimulate -r -k " + steps + "\nshow_traces\nquit\n";
                stdin.write(commands.getBytes(StandardCharsets.UTF_8));
                stdin.flush();
            }

            boolean finished = process.waitFor(timeout, java.util.concurrent.TimeUnit.MILLISECONDS);
            if (!finished) {
                log.warn("NuSMV simulation timed out after {}ms, destroying process", timeout);
                process.destroyForcibly();
                process.waitFor(PROCESS_DESTROY_TIMEOUT_SECONDS, java.util.concurrent.TimeUnit.SECONDS);
                reclaimReaderThread(stdoutThread, process.getInputStream(), "stdout");
                reclaimReaderThread(stderrThread, process.getErrorStream(), "stderr");
                return SimulationOutput.error("NuSMV simulation timed out after " + timeout + "ms");
            }

            boolean stdoutReady = waitReaderThreadCompletion(stdoutThread, process.getInputStream(), "stdout");
            boolean stderrReady = waitReaderThreadCompletion(stderrThread, process.getErrorStream(), "stderr");
            if (!stdoutReady || !stderrReady) {
                return SimulationOutput.error("NuSMV simulation output reader did not finish in time");
            }

            String rawOutput = stdoutBuilder.toString();
            String stderrOutput = stderrBuilder.toString();

            // 保存原始输出到文件（与批处理模式一致）
            saveOutputToFile(smvFile, rawOutput);

            if (!stderrOutput.isBlank()) {
                log.warn("NuSMV simulation stderr: {}", stderrOutput);
            }

            // 校验进程退出码：非 0 表示 NuSMV 执行异常
            int exitCode = process.exitValue();
            if (exitCode != 0) {
                log.warn("NuSMV simulation exited with code {}", exitCode);
                String summary = "NuSMV exited with code " + exitCode + ".";
                if (!stderrOutput.isBlank()) {
                    summary += " stderr: " + stderrOutput.substring(0, Math.min(stderrOutput.length(), 1000));
                }
                if (!rawOutput.isBlank()) {
                    summary += " stdout: " + rawOutput.substring(0, Math.min(rawOutput.length(), 1000));
                }
                return SimulationOutput.error(summary);
            }

            // 从输出中提取模拟轨迹
            String traceText = extractSimulationTrace(rawOutput);
            if (traceText == null || traceText.isBlank()) {
                log.warn("No simulation trace found in NuSMV output");
                return SimulationOutput.error(
                        "No simulation trace produced. Model may have errors. Raw output: "
                                + rawOutput.substring(0, Math.min(rawOutput.length(), 2000)));
            }

            return SimulationOutput.success(traceText, rawOutput);

        } catch (IOException e) {
            log.error("Failed to execute NuSMV simulation", e);
            if (process != null) {
                process.destroyForcibly();
            }
            return SimulationOutput.error("Failed to execute NuSMV simulation: " + e.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            log.warn("NuSMV simulation interrupted");
            if (process != null) {
                process.destroyForcibly();
            }
            throw e;
        } finally {
            releaseExecutionPermit();
        }
    }

    /**
     * 带超时的线程回收：先 join(5s)，若仍存活则 interrupt + 关流 + 短暂重试，
     * 避免"主线程不卡但后台线程静默泄漏"。
     */
    private boolean waitReaderThreadCompletion(Thread thread, InputStream stream, String label) throws InterruptedException {
        thread.join(READER_JOIN_TIMEOUT_MS);
        if (!thread.isAlive()) {
            return true;
        }
        log.warn("NuSMV {} reader thread did not finish in {}ms, reclaiming", label, READER_JOIN_TIMEOUT_MS);
        reclaimReaderThread(thread, stream, label);
        return !thread.isAlive();
    }

    private void reclaimReaderThread(Thread thread, InputStream stream, String label) {
        try {
            thread.join(5000);
            if (thread.isAlive()) {
                log.warn("NuSMV {} reader thread still alive after join timeout, reclaiming", label);
                thread.interrupt();
                try { stream.close(); } catch (IOException ignored) { }
                thread.join(2000);
                if (thread.isAlive()) {
                    log.warn("NuSMV {} reader thread could not be reclaimed, may leak", label);
                }
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    /**
     * 从交互模式的完整输出中提取模拟轨迹文本。
     * 定位 "Trace Type: Simulation" 行，取其后所有内容，过滤掉 NuSMV 提示符行。
     */
    private String extractSimulationTrace(String rawOutput) {
        if (rawOutput == null || rawOutput.isEmpty()) return null;

        int markerIdx = rawOutput.indexOf(TRACE_SIMULATION_MARKER);
        if (markerIdx < 0) return null;

        String afterMarker = rawOutput.substring(markerIdx + TRACE_SIMULATION_MARKER.length());
        String[] lines = afterMarker.split("\n");
        StringBuilder trace = new StringBuilder();
        for (String line : lines) {
            if (NUSMV_PROMPT_PATTERN.matcher(line).matches()) continue;
            trace.append(line).append("\n");
        }
        String normalized = trace.toString().stripTrailing();
        return normalized.isBlank() ? null : normalized;
    }

    /**
     * 交互式模拟输出
     */
    public static class SimulationOutput {
        private final String traceText;
        private final String rawOutput;
        private final boolean success;
        private final String errorMessage;
        private final boolean busy;

        private SimulationOutput(String traceText, String rawOutput, boolean success, String errorMessage, boolean busy) {
            this.traceText = traceText;
            this.rawOutput = rawOutput;
            this.success = success;
            this.errorMessage = errorMessage;
            this.busy = busy;
        }

        public static SimulationOutput success(String traceText, String rawOutput) {
            return new SimulationOutput(traceText, rawOutput, true, null, false);
        }

        public static SimulationOutput error(String errorMessage) {
            return new SimulationOutput(null, null, false, errorMessage, false);
        }

        public static SimulationOutput busy(String errorMessage) {
            return new SimulationOutput(null, null, false, errorMessage, true);
        }

        public String getTraceText() { return traceText; }
        public String getRawOutput() { return rawOutput; }
        public boolean isSuccess() { return success; }
        public String getErrorMessage() { return errorMessage; }
        public boolean isBusy() { return busy; }
    }

    /**
     * 解析 NuSMV 输出，提取每个 spec 的独立结果。
     *
     * NuSMV 输出格式：
     *   -- specification CTLSPEC ... is true
     *   -- specification LTLSPEC ... is false
     *   -- as demonstrated by the following execution sequence
     *   Trace Description: ...
     *   Trace Type: ...
     *   State 1.1: ...
     *   ...
     */
    private List<SpecCheckResult> parseSpecResults(String output) {
        List<SpecCheckResult> results = new ArrayList<>();
        if (output == null || output.isEmpty()) {
            return results;
        }

        String[] lines = output.split("\n");
        int i = 0;
        while (i < lines.length) {
            String line = lines[i].trim();

            // Check for "-- specification ... is true"
            Matcher trueMatcher = SPEC_TRUE_PATTERN.matcher(line);
            if (trueMatcher.find()) {
                results.add(new SpecCheckResult(trueMatcher.group(1).trim(), true, null));
                i++;
                continue;
            }

            // Check for "-- specification ... is false"
            Matcher falseMatcher = SPEC_FALSE_PATTERN.matcher(line);
            if (falseMatcher.find()) {
                String specExpr = falseMatcher.group(1).trim();
                // Collect the counterexample trace that follows
                i++;
                StringBuilder traceBuilder = new StringBuilder();
                while (i < lines.length) {
                    String traceLine = lines[i];
                    // Stop when we hit the next spec result line
                    if (traceLine.trim().startsWith("-- specification ")) {
                        break;
                    }
                    traceBuilder.append(traceLine).append("\n");
                    i++;
                }
                String counterexample = extractTraceFromBlock(traceBuilder.toString());
                results.add(new SpecCheckResult(specExpr, false, counterexample));
                continue;
            }

            i++;
        }

        return results;
    }

    /**
     * 从 trace block 中提取 State 行（跳过 Trace Description/Type 等元信息）
     */
    private String extractTraceFromBlock(String block) {
        if (block == null || block.isEmpty()) {
            return null;
        }
        StringBuilder trace = new StringBuilder();
        boolean inStates = false;
        for (String line : block.split("\n")) {
            String trimmed = line.trim();
            // 兼容 NuSMV 2.7.1 格式 "-> State: 1.1 <-" 和旧格式 "State 1.1:"
            if (trimmed.startsWith("-> State:") || trimmed.startsWith("State ") || inStates) {
                inStates = true;
                trace.append(line).append("\n");
            }
        }
        String result = trace.toString().trim();
        return result.isEmpty() ? null : result;
    }

    /**
     * 单个 spec 的检查结果
     */
    public static class SpecCheckResult {
        private final String specExpression;
        private final boolean passed;
        private final String counterexample;

        public SpecCheckResult(String specExpression, boolean passed, String counterexample) {
            this.specExpression = specExpression;
            this.passed = passed;
            this.counterexample = counterexample;
        }

        public String getSpecExpression() { return specExpression; }
        public boolean isPassed() { return passed; }
        public String getCounterexample() { return counterexample; }
    }

    /**
     * NuSMV 执行结果
     */
    public static class NusmvResult {
        private final String output;
        private final boolean success;
        private final String errorMessage;
        private final List<SpecCheckResult> specResults;
        private final boolean busy;

        private NusmvResult(String output, boolean success, String errorMessage,
                            List<SpecCheckResult> specResults, boolean busy) {
            this.output = output;
            this.success = success;
            this.errorMessage = errorMessage;
            this.specResults = specResults != null ? specResults : List.of();
            this.busy = busy;
        }

        public static NusmvResult success(String output, List<SpecCheckResult> specResults) {
            return new NusmvResult(output, true, null, specResults, false);
        }

        public static NusmvResult error(String errorMessage) {
            return new NusmvResult(null, false, errorMessage, null, false);
        }

        public static NusmvResult busy(String errorMessage) {
            return new NusmvResult(null, false, errorMessage, null, true);
        }

        public String getOutput() { return output; }
        public boolean isSuccess() { return success; }
        public String getErrorMessage() { return errorMessage; }
        public List<SpecCheckResult> getSpecResults() { return specResults; }
        public boolean isBusy() { return busy; }

        public boolean hasAnyViolation() {
            return specResults.stream().anyMatch(r -> !r.isPassed());
        }
    }
}
