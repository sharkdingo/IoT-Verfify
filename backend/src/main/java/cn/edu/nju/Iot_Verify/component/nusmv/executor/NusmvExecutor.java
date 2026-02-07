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
 * 职责：执行 NuSMV 命令并提取验证结果
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class NusmvExecutor {

    private final NusmvConfig nusmvConfig;
    
    private static final String TIMEOUT_ENV_KEY = "NUSMV_TIMEOUT_MS";
    private static final int PROCESS_DESTROY_TIMEOUT_SECONDS = 5;
    private static final long OUTPUT_THREAD_JOIN_TIMEOUT_MS = 1000;

    private static final Pattern COUNTEREXAMPLE_PATTERN = Pattern.compile(
            "(--.*?At time.*?--)[\n\r]*(.*?)(?=--.*?At time|-- End of|$)",
            Pattern.DOTALL | Pattern.CASE_INSENSITIVE
    );

    public NusmvResult execute(File smvFile) throws IOException, InterruptedException {
        if (smvFile == null || !smvFile.exists()) {
            return new NusmvResult("NuSMV model file does not exist or is null");
        }

        String nusmvPath = nusmvConfig.getPath();
        String commandPrefix = nusmvConfig.getCommandPrefix();

        List<String> command = new ArrayList<>();
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("windows");

        if (commandPrefix != null && !commandPrefix.isEmpty()) {
            if (isWindows) {
                command.add("cmd.exe");
                command.add("/c");
                command.add(commandPrefix);
                command.add(nusmvPath);
                command.add(smvFile.getAbsolutePath());
            } else {
                command.add("sh");
                command.add("-c");
                command.add(commandPrefix);
                command.add(nusmvPath);
                command.add(smvFile.getAbsolutePath());
            }
        } else {
            if (isWindows) {
                command.add("cmd.exe");
                command.add("/c");
                command.add(nusmvPath);
                command.add(smvFile.getAbsolutePath());
            } else {
                command.add(nusmvPath);
                command.add(smvFile.getAbsolutePath());
            }
        }

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
                return new NusmvResult("NuSMV execution timed out after " + timeout + "ms");
            }
            
            outputThread.join(OUTPUT_THREAD_JOIN_TIMEOUT_MS);

            int exitCode = process.exitValue();
            String output = outputBuilder.toString();

            log.debug("NuSMV exit code: {}, output length: {}", exitCode, output.length());

            if (exitCode != 0) {
                return new NusmvResult("NuSMV exited with code " + exitCode + ": " + output);
            }

            String counterexample = extractCounterexample(output);
            boolean hasCounterexample = counterexample != null && !counterexample.isEmpty();

            return new NusmvResult(output, hasCounterexample, counterexample);

        } catch (IOException e) {
            log.error("Failed to execute NuSMV", e);
            return new NusmvResult("Failed to execute NuSMV: " + e.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            log.warn("NuSMV execution interrupted");
            if (process != null) {
                process.destroyForcibly();
            }
            return new NusmvResult("NuSMV execution interrupted");
        }
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

    private String extractCounterexample(String output) {
        if (output == null || output.isEmpty()) {
            return null;
        }

        boolean hasCounterexample = output.contains("Trace Description") ||
                output.contains("counterexample") ||
                output.contains("Trace Type") ||
                (output.contains("State") && output.contains("="));

        if (!hasCounterexample) {
            return null;
        }

        Matcher matcher = COUNTEREXAMPLE_PATTERN.matcher(output);
        if (matcher.find()) {
            return matcher.group(2).trim();
        }

        return extractCounterexampleManually(output);
    }

    private String extractCounterexampleManually(String output) {
        StringBuilder counterexample = new StringBuilder();
        String[] lines = output.split("\n");
        boolean inTrace = false;

        for (String line : lines) {
            if (line.contains("Trace Description") || line.contains("Trace Type")) {
                inTrace = true;
                counterexample.append(line).append("\n");
            } else if (line.contains("End of")) {
                inTrace = false;
            } else if (inTrace) {
                counterexample.append(line).append("\n");
            }
        }

        return counterexample.length() > 0 ? counterexample.toString() : null;
    }

    public List<String> parseCounterexampleStates(String counterexample) {
        if (counterexample == null || counterexample.isEmpty()) {
            return new ArrayList<>();
        }

        List<String> states = new ArrayList<>();
        String[] lines = counterexample.split("\n");

        StringBuilder currentState = new StringBuilder();
        boolean inState = false;

        for (String line : lines) {
            if (line.startsWith("--") || line.trim().isEmpty()) {
                continue;
            }

            if (line.startsWith("State")) {
                if (currentState.length() > 0) {
                    states.add(currentState.toString().trim());
                }
                currentState = new StringBuilder();
                currentState.append(line).append("\n");
                inState = true;
            } else if (inState) {
                currentState.append(line).append("\n");
            }
        }

        if (currentState.length() > 0) {
            states.add(currentState.toString().trim());
        }

        return states;
    }

    public String extractDeviceState(String counterexample, String deviceName, int deviceNo) {
        if (counterexample == null || counterexample.isEmpty() || deviceName == null) {
            return null;
        }

        String safeDeviceName = deviceName.toLowerCase().replace(" ", "");
        String moduleName = Pattern.quote(safeDeviceName) + "_" + deviceNo;
        Pattern pattern = Pattern.compile(
                Pattern.quote(moduleName) + "\\.state\\s*=\\s*(\\w+)",
                Pattern.CASE_INSENSITIVE
        );

        Matcher matcher = pattern.matcher(counterexample);
        if (matcher.find()) {
            return matcher.group(1);
        }

        return null;
    }

    public String extractVariableValue(String counterexample, String deviceName, int deviceNo, String varName) {
        if (counterexample == null || counterexample.isEmpty() || deviceName == null) {
            return null;
        }

        String safeDeviceName = deviceName.toLowerCase().replace(" ", "");
        String moduleName = Pattern.quote(safeDeviceName) + "_" + deviceNo;
        Pattern pattern = Pattern.compile(
                Pattern.quote(moduleName) + "\\." + Pattern.quote(varName) + "\\s*=\\s*(-?\\d+|\\w+)",
                Pattern.CASE_INSENSITIVE
        );

        Matcher matcher = pattern.matcher(counterexample);
        if (matcher.find()) {
            return matcher.group(1);
        }

        return null;
    }

    public static class NusmvResult {
        private final String output;
        private final boolean hasCounterexample;
        private final String counterexample;
        private final boolean success;
        private final String errorMessage;
        
        public NusmvResult(String output, boolean hasCounterexample, String counterexample) {
            this.output = output;
            this.hasCounterexample = hasCounterexample;
            this.counterexample = counterexample;
            this.success = true;
            this.errorMessage = null;
        }
        
        public NusmvResult(String errorMessage) {
            this.output = null;
            this.hasCounterexample = false;
            this.counterexample = null;
            this.success = false;
            this.errorMessage = errorMessage;
        }
        
        public String getOutput() { return output; }
        public boolean hasCounterexample() { return hasCounterexample; }
        public String getCounterexample() { return counterexample; }
        public boolean isSuccess() { return success; }
        public String getErrorMessage() { return errorMessage; }
    }
}
