package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.service.NusmvExecutorService;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * NuSMV 执行器实现类
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class NusmvExecutorServiceImpl implements NusmvExecutorService {

    private final NusmvConfig nusmvConfig;
    
    /** NuSMV 执行超时时间（毫秒） */
    private static final long TIMEOUT_MS = 60000; // 60秒
    
    /** NuSMV 执行超时时间（环境变量覆盖） */
    private static final String TIMEOUT_ENV_KEY = "NUSMV_TIMEOUT_MS";
    private static final long DEFAULT_TIMEOUT = 60000;
    
    /** 进程强制销毁等待时间（秒） */
    private static final int PROCESS_DESTROY_TIMEOUT_SECONDS = 5;
    
    /** 输出线程 Join 超时时间（毫秒） */
    private static final long OUTPUT_THREAD_JOIN_TIMEOUT_MS = 1000;

    // Counterexample 模式
    private static final Pattern COUNTEREXAMPLE_PATTERN = Pattern.compile(
            "(--.*?At time.*?--)[\n\r]*(.*?)(?=--.*?At time|-- End of|$)",
            Pattern.DOTALL | Pattern.CASE_INSENSITIVE
    );

    // 简单的状态值模式
    private static final Pattern STATE_PATTERN = Pattern.compile(
            "(\\w+)\\.(state|\\w+)\\s*=\\s*(\\w+)",
            Pattern.CASE_INSENSITIVE
    );

    // 变量值模式
    private static final Pattern VARIABLE_PATTERN = Pattern.compile(
            "(\\w+)\\.(\\w+)\\s*=\\s*(-?\\d+|\\w+)",
            Pattern.CASE_INSENSITIVE
    );

    /**
     * 执行 NuSMV 模型验证
     * 
     * 核心流程：
     * 1. 构建 NuSMV 命令（跨平台支持）
     * 2. 启动 NuSMV 进程并读取输出
     * 3. 解析输出，提取 counterexample
     * 4. 返回验证结果
     * 
     * @param smvFile NuSMV 模型文件
     * @return 包含验证输出和 counterexample 的结果对象
     * @throws IOException 文件不存在或读取失败时抛出
     * @throws InterruptedException 进程被中断时抛出
     */
    @Override
    public NusmvResult execute(File smvFile) throws IOException, InterruptedException {
        if (smvFile == null || !smvFile.exists()) {
            return new NusmvResult("NuSMV model file does not exist or is null");
        }

        String nusmvPath = nusmvConfig.getPath();
        String commandPrefix = nusmvConfig.getCommandPrefix();

        // 跨平台命令构建 - 使用 ProcessBuilder 列表形式避免路径空格和引号问题
        List<String> command = new ArrayList<>();
        boolean isWindows = System.getProperty("os.name").toLowerCase().contains("windows");

        if (commandPrefix != null && !commandPrefix.isEmpty()) {
            // 使用 shell 命令前缀
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
            // 直接执行 NuSMV - 使用列表形式避免路径空格问题
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
            
            // 获取超时时间（支持环境变量覆盖）
            long timeout = getTimeoutFromEnvironment();

            // 读取输出（带超时）- 使用 final 副本供 lambda 使用
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
            
            // 等待进程完成，带超时
            boolean finished = process.waitFor(timeout, java.util.concurrent.TimeUnit.MILLISECONDS);
            
            if (!finished) {
                // 超时：销毁进程
                log.warn("NuSMV execution timed out after {}ms, destroying process", timeout);
                process.destroyForcibly();
                // 等待进程终止
                if (!process.waitFor(PROCESS_DESTROY_TIMEOUT_SECONDS, java.util.concurrent.TimeUnit.SECONDS)) {
                    log.error("Failed to destroy NuSMV process");
                }
                return new NusmvResult("NuSMV execution timed out after " + timeout + "ms");
            }
            
            outputThread.join(OUTPUT_THREAD_JOIN_TIMEOUT_MS); // 等待输出线程完成

            int exitCode = process.exitValue();
            String output = outputBuilder.toString();

            log.debug("NuSMV exit code: {}, output length: {}", exitCode, output.length());

            if (exitCode != 0) {
                return new NusmvResult("NuSMV exited with code " + exitCode + ": " + output);
            }

            // 解析输出，提取 counterexample
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
    
    /**
     * 从环境变量获取超时时间
     * 
     * 支持通过环境变量 NUSMV_TIMEOUT_MS 自定义超时时间（毫秒）
     * 如果环境变量无效或未设置，返回默认值 DEFAULT_TIMEOUT
     * 
     * @return 超时时间（毫秒）
     */
    private long getTimeoutFromEnvironment() {
        try {
            String timeoutEnv = System.getenv(TIMEOUT_ENV_KEY);
            if (timeoutEnv != null && !timeoutEnv.isEmpty()) {
                return Long.parseLong(timeoutEnv);
            }
        } catch (NumberFormatException e) {
            log.warn("Invalid NUSMV_TIMEOUT_MS value, using default: {}", DEFAULT_TIMEOUT);
        }
        return DEFAULT_TIMEOUT;
    }

    /**
     * 从 NuSMV 输出中提取 counterexample
     * 
     * 识别 Counterexample 的特征：
     * - 包含 "Trace Description" 或 "Trace Type"
     * - 包含 "counterexample" 关键字
     * - 包含多个 "State" 行（表示状态序列）
     * 
     * @param output NuSMV 的完整输出
     * @return counterexample 部分文本，如果不存在则返回 null
     */
    private String extractCounterexample(String output) {
        if (output == null || output.isEmpty()) {
            return null;
        }

        // 查找 "Trace Description" 或 "Trace Type" 来确定有 counterexample
        boolean hasCounterexample = output.contains("Trace Description") ||
                output.contains("counterexample") ||
                output.contains("Trace Type") ||
                (output.contains("State") && output.contains("="));

        if (!hasCounterexample) {
            return null;
        }

        // 尝试提取 counterexample 部分
        Matcher matcher = COUNTEREXAMPLE_PATTERN.matcher(output);
        if (matcher.find()) {
            return matcher.group(2).trim();
        }

        // 如果正则匹配失败，尝试手动提取
        return extractCounterexampleManually(output);
    }

    /**
     * 手动提取 counterexample（备选方案）
     */
    private String extractCounterexampleManually(String output) {
        StringBuilder counterexample = new StringBuilder();

        // 查找 "State" 或 "At time" 开始的部分
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

    /**
     * 解析 counterexample 为状态列表
     * 
     * 将 counterexample 文本解析为状态序列，每个状态包含完整的变量赋值信息
     * 状态以 "State" 关键字开头，不同状态之间用空行分隔
     * 
     * @param counterexample counterexample 文本
     * @return 状态列表，每个元素是一个状态的完整描述
     */
    public List<String> parseCounterexampleStates(String counterexample) {
        if (counterexample == null || counterexample.isEmpty()) {
            return new ArrayList<>();
        }

        List<String> states = new ArrayList<>();
        String[] lines = counterexample.split("\n");

        StringBuilder currentState = new StringBuilder();
        boolean inState = false;

        for (String line : lines) {
            // 跳过注释行和空行
            if (line.startsWith("--") || line.trim().isEmpty()) {
                continue;
            }

            // 检测新状态开始
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

        // 添加最后一个状态
        if (currentState.length() > 0) {
            states.add(currentState.toString().trim());
        }

        return states;
    }

    /**
     * 从 counterexample 中提取特定设备的状态值
    /**
     * 从 counterexample 中提取特定设备的状态值
     * 
     * 使用正则表达式匹配 "moduleName.state = value" 格式的输出
     * 模块名称格式为: {deviceName}_{deviceNo}
     * 
     * @param counterexample counterexample 文本
     * @param deviceName 设备名称
     * @param deviceNo 设备编号
     * @return 状态名称，如果未找到则返回 null
     */
    public String extractDeviceState(String counterexample, String deviceName, int deviceNo) {
        if (counterexample == null || counterexample.isEmpty()) {
            return null;
        }

        if (deviceName == null) {
            return null;
        }

        // 安全构造模块名：仅对设备名部分进行转义，设备号保持原样
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

    /**
     * 从 counterexample 中提取特定变量的值
     * 
     * 使用正则表达式匹配 "moduleName.varName = value" 格式的输出
     * 用于提取设备在特定状态下的变量赋值
     * 
     * @param counterexample counterexample 文本
     * @param deviceName 设备名称
     * @param deviceNo 设备编号
     * @param varName 变量名称
     * @return 变量值，如果未找到则返回 null
     */
    public String extractVariableValue(String counterexample, String deviceName, int deviceNo, String varName) {
        if (counterexample == null || counterexample.isEmpty()) {
            return null;
        }

        if (deviceName == null) {
            return null;
        }

        // 安全构造模块名：仅对设备名部分进行转义，设备号保持原样
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
}
