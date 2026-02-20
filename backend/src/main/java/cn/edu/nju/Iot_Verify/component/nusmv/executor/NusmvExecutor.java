package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * NuSMV 执行器
 * 职责：执行 NuSMV 命令并提取 per-spec 验证结果
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class NusmvExecutor {

    private final NusmvConfig nusmvConfig;

    private static final String TIMEOUT_ENV_KEY = "NUSMV_TIMEOUT_MS";
    private static final int PROCESS_DESTROY_TIMEOUT_SECONDS = 5;

    // NuSMV spec result patterns
    private static final Pattern SPEC_TRUE_PATTERN = Pattern.compile(
            "-- specification (.+?) is true", Pattern.CASE_INSENSITIVE);
    private static final Pattern SPEC_FALSE_PATTERN = Pattern.compile(
            "-- specification (.+?) is false", Pattern.CASE_INSENSITIVE);
    public NusmvResult execute(File smvFile) throws InterruptedException {
        if (smvFile == null || !smvFile.exists()) {
            return NusmvResult.error("NuSMV model file does not exist or is null");
        }

        List<String> command = buildCommand(smvFile);
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
            });
            outputThread.start();

            boolean finished = process.waitFor(timeout, java.util.concurrent.TimeUnit.MILLISECONDS);

            if (!finished) {
                log.warn("NuSMV execution timed out after {}ms, destroying process", timeout);
                process.destroyForcibly();
                if (!process.waitFor(PROCESS_DESTROY_TIMEOUT_SECONDS, java.util.concurrent.TimeUnit.SECONDS)) {
                    log.error("Failed to destroy NuSMV process");
                }
                // 进程销毁后流会关闭，等待输出线程结束
                outputThread.join();
                return NusmvResult.error("NuSMV execution timed out after " + timeout + "ms");
            }

            // 进程已正常结束，流一定会关闭，无需超时限制
            outputThread.join();

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

    private List<String> buildCommand(File smvFile) {
        String nusmvPath = nusmvConfig.getPath();
        String commandPrefix = nusmvConfig.getCommandPrefix();
        List<String> command = new ArrayList<>();
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("windows");

        // SECURITY: commandPrefix is passed to sh -c / cmd.exe /c and can execute arbitrary commands.
        // It MUST only come from trusted server-side configuration (application.yaml / env vars),
        // NEVER from user input.
        if (commandPrefix != null && !commandPrefix.isEmpty()) {
            String fullCommand = commandPrefix + " " + quoteForShell(nusmvPath, isWindows)
                    + " " + quoteForShell(smvFile.getAbsolutePath(), isWindows);
            if (isWindows) {
                command.add("cmd.exe");
                command.add("/c");
                command.add(fullCommand);
            } else {
                command.add("sh");
                command.add("-c");
                command.add(fullCommand);
            }
            return command;
        }
        // No commandPrefix: invoke the executable directly via ProcessBuilder.
        // Do NOT wrap with cmd.exe /c — its quoting rules are fragile and can
        // cause the command to be misinterpreted (e.g. opening an interactive shell).
        command.add(nusmvPath);
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

        private NusmvResult(String output, boolean success, String errorMessage,
                            List<SpecCheckResult> specResults) {
            this.output = output;
            this.success = success;
            this.errorMessage = errorMessage;
            this.specResults = specResults != null ? specResults : List.of();
        }

        public static NusmvResult success(String output, List<SpecCheckResult> specResults) {
            return new NusmvResult(output, true, null, specResults);
        }

        public static NusmvResult error(String errorMessage) {
            return new NusmvResult(null, false, errorMessage, null);
        }

        public String getOutput() { return output; }
        public boolean isSuccess() { return success; }
        public String getErrorMessage() { return errorMessage; }
        public List<SpecCheckResult> getSpecResults() { return specResults; }

        public boolean hasAnyViolation() {
            return specResults.stream().anyMatch(r -> !r.isPassed());
        }
    }
}
