package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.repository.VerificationTaskRepository;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import cn.edu.nju.Iot_Verify.util.mapper.VerificationTaskMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.scheduling.annotation.Async;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.io.*;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

/**
 * 验证服务实现类
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class VerificationServiceImpl implements VerificationService {

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final VerificationTaskRepository taskRepository;
    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final SpecificationMapper specificationMapper;
    private final VerificationTaskMapper verificationTaskMapper;
    private final ObjectMapper objectMapper;

    private static final int MAX_OUTPUT_LENGTH = 10000;

    private final ConcurrentHashMap<Long, Thread> runningTasks = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<Long, Integer> taskProgress = new ConcurrentHashMap<>();

    /**
     * 执行形式化验证（支持攻击模式）
     * 
     * 核心流程：
     * 1. 验证输入参数有效性
     * 2. 生成 NuSMV 模型文件
     * 3. 执行 NuSMV 验证
     * 4. 解析验证结果，生成 Trace
     * 5. 自动持久化违规 Trace（检测到违规时自动保存）
     * 
     * @param userId 用户ID
     * @param devices 设备节点列表
     * @param rules 规则列表
     * @param specs 规格列表
     * @param isAttack 是否启用攻击模式（参考 MEDIC-test isAttack）
     * @param intensity 攻击强度 0-50（参考 MEDIC-test intensity）
     * @return 验证结果 DTO，包含验证输出、Trace 列表、规格检查结果
     */
    @Override
    @Transactional
    public VerificationResultDto verify(Long userId, 
                                        List<DeviceNodeDto> devices,
                                        List<RuleDto> rules,
                                        List<SpecificationDto> specs,
                                        boolean isAttack,
                                        int intensity) {
        // 请求验证
        if (devices == null || devices.isEmpty()) {
            log.warn("Verification rejected: devices list is empty for user {}", userId);
            return VerificationResultDto.builder()
                    .safe(false)
                    .traces(Collections.emptyList())
                    .specResults(Collections.emptyList())
                    .checkLogs(Collections.singletonList("Error: devices list cannot be empty"))
                    .nusmvOutput("")
                    .build();
        }
        if (specs == null || specs.isEmpty()) {
            log.warn("Verification rejected: specs list is empty for user {}", userId);
            return VerificationResultDto.builder()
                    .safe(true)
                    .traces(Collections.emptyList())
                    .specResults(Collections.emptyList())
                    .checkLogs(Collections.singletonList("Error: specs list cannot be empty"))
                    .nusmvOutput("")
                    .build();
        }
        if (intensity < 0 || intensity > 50) {
            log.warn("Verification rejected: invalid intensity {} for user {}", intensity, userId);
        }

        log.info("Starting verification for user {}, devices: {}, rules: {}, specs: {}, isAttack: {}, intensity: {}",
                userId, devices.size(), rules.size(), specs.size(), isAttack, intensity);

        List<String> checkLogs = new ArrayList<>();
        List<Boolean> specResults = new ArrayList<>();
        List<TraceDto> traces = new ArrayList<>();
        String nusmvOutput = "";

        try {
            // 1. 生成 NuSMV 模型文件（支持攻击模式）
            checkLogs.add("Generating NuSMV model...");
            File smvFile = smvGenerator.generate(userId, devices, rules, specs, isAttack, intensity);
            
            // 验证生成的 SMV 文件
            if (smvFile == null || !smvFile.exists()) {
                checkLogs.add("Failed to generate NuSMV model file");
                return buildErrorResult("", checkLogs);
            }
            
            checkLogs.add("Model generated: " + smvFile.getAbsolutePath());

            // 2. 执行 NuSMV 验证
            checkLogs.add("Executing NuSMV verification...");
            NusmvExecutor.NusmvResult result = nusmvExecutor.execute(smvFile);
            nusmvOutput = result.getOutput();

            if (!result.isSuccess()) {
                checkLogs.add("NuSMV execution failed: " + result.getErrorMessage());
                return buildErrorResult(nusmvOutput, checkLogs);
            }

            checkLogs.add("NuSMV execution completed successfully.");

            // 3. 解析验证结果
            if (result.hasCounterexample()) {
                checkLogs.add("Specification violation detected!");
                
                // 为每个违反的规格生成 Trace
                String counterexample = result.getCounterexample();
                List<TraceDto> violationTraces = generateTracesFromCounterexample(
                        counterexample, devices, specs, userId);
                
                traces.addAll(violationTraces);
                checkLogs.add("Generated " + violationTraces.size() + " violation trace(s).");

                // 所有规格检查结果为 false（因为有反例）
                for (int i = 0; i < specs.size(); i++) {
                    specResults.add(false);
                }
            } else {
                checkLogs.add("All specifications satisfied (no counterexample).");
                // 所有规格检查结果为 true
                for (int i = 0; i < specs.size(); i++) {
                    specResults.add(true);
                }
            }

            // 4. 自动持久化违规 Trace
            if (!traces.isEmpty()) {
                log.debug("Auto-saving {} violation trace(s) for user {}", traces.size(), userId);
                saveTraces(traces, userId);
                checkLogs.add("Auto-saved " + traces.size() + " violation trace(s) to database.");
            }

            // 清理临时文件
            cleanupTempFile(smvFile);

        } catch (IOException e) {
            log.error("IO error during verification", e);
            checkLogs.add("IO Error: " + e.getMessage());
            return buildErrorResult(nusmvOutput, checkLogs);
        } catch (InterruptedException e) {
            log.error("NuSMV execution interrupted", e);
            Thread.currentThread().interrupt();
            checkLogs.add("Execution interrupted: " + e.getMessage());
            return buildErrorResult(nusmvOutput, checkLogs);
        } catch (Exception e) {
            log.error("Verification failed", e);
            checkLogs.add("Verification failed: " + e.getMessage());
            throw new InternalServerException("Verification failed: " + e.getMessage());
        }

        // 构建结果
        return VerificationResultDto.builder()
                .safe(traces.isEmpty())
                .traces(traces)
                .specResults(specResults)
                .checkLogs(checkLogs)
                .nusmvOutput(truncateOutput(nusmvOutput))
                .build();
    }

    /**
     * 异步验证（通过任务ID回调）
     * 
     * 核心流程：
     * 1. 更新任务状态为 RUNNING
     * 2. 执行验证（同同步方法）
     * 3. 更新任务状态为 COMPLETED 或 FAILED
     * 4. 更新任务结果
     * 
     * @param userId 用户ID
     * @param taskId 任务ID
     * @param devices 设备节点列表
     * @param rules 规则列表
     * @param specs 规格列表
     * @param isAttack 是否启用攻击模式
     * @param intensity 攻击强度 0-50
     */
    @Override
    @Async("verificationTaskExecutor")
    @Transactional
    public void verifyAsync(Long userId, Long taskId,
                             List<DeviceNodeDto> devices,
                             List<RuleDto> rules,
                             List<SpecificationDto> specs,
                             boolean isAttack, int intensity) {
        log.info("Starting async verification task: {} for user: {}", taskId, userId);
        LocalDateTime startTime = LocalDateTime.now();

        runningTasks.put(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        VerificationTaskPo task = null;
        File smvFile = null;
        boolean smvFileCreated = false;

        try {
            if (Thread.currentThread().isInterrupted()) {
                log.info("Task {} was cancelled before start", taskId);
                return;
            }

            task = taskRepository.findByIdAndUserId(taskId, userId).orElse(null);
            if (task == null) {
                log.warn("Async verification task not found or unauthorized: taskId={}, userId={}", taskId, userId);
                return;
            }

            task.setStatus(VerificationTaskPo.TaskStatus.RUNNING);
            task.setStartedAt(startTime);
            List<String> initLogs = new ArrayList<>();
            initLogs.add("Starting verification task: " + taskId);
            initLogs.add("Devices: " + (devices != null ? devices.size() : 0));
            initLogs.add("Rules: " + (rules != null ? rules.size() : 0));
            initLogs.add("Specifications: " + (specs != null ? specs.size() : 0));
            initLogs.add("Attack mode: " + isAttack + ", Intensity: " + intensity);
            writeCheckLogs(task, initLogs);
            taskRepository.save(task);

            if (devices == null || devices.isEmpty()) {
                completeTask(taskId, task, false, 0, Arrays.asList("Error: devices list cannot be empty"), "Invalid input");
                return;
            }
            if (specs == null || specs.isEmpty()) {
                completeTask(taskId, task, true, 0, Arrays.asList("Error: specs list cannot be empty"), "No specifications");
                return;
            }

            updateTaskProgress(taskId, 20, "Generating NuSMV model");
            addLog(task, "Generating NuSMV model...");
            smvFile = smvGenerator.generate(userId, devices, rules, specs, isAttack, intensity);
            smvFileCreated = true;

            if (Thread.currentThread().isInterrupted()) {
                handleCancellation(taskId, task);
                return;
            }

            if (smvFile == null || !smvFile.exists()) {
                completeTask(taskId, task, false, 0,
                    addLog(task, "Failed to generate NuSMV model file"),
                    "Generation failed");
                return;
            }

            addLog(task, "Model generated: " + smvFile.getAbsolutePath());

            updateTaskProgress(taskId, 50, "Executing NuSMV verification");
            addLog(task, "Executing NuSMV verification...");
            NusmvExecutor.NusmvResult result = nusmvExecutor.execute(smvFile);
            String nusmvOutput = result.getOutput();

            if (Thread.currentThread().isInterrupted()) {
                handleCancellation(taskId, task);
                return;
            }

            if (!result.isSuccess()) {
                completeTask(taskId, task, false, 0,
                    addLog(task, "NuSMV execution failed: " + result.getErrorMessage()),
                    "Execution failed");
                return;
            }

            addLog(task, "NuSMV execution completed successfully.");

            updateTaskProgress(taskId, 80, "Parsing results");
            List<String> checkLogs = new ArrayList<>(readCheckLogs(task));
            List<Boolean> specResults = new ArrayList<>();
            List<TraceDto> traces = new ArrayList<>();

            if (result.hasCounterexample()) {
                addLog(task, "Specification violation detected!");

                String counterexample = result.getCounterexample();
                List<TraceDto> violationTraces = generateTracesFromCounterexample(
                        counterexample, devices, specs, userId);

                traces.addAll(violationTraces);
                addLog(task, "Generated " + violationTraces.size() + " violation trace(s).");

                for (int i = 0; i < specs.size(); i++) {
                    specResults.add(false);
                }
            } else {
                addLog(task, "All specifications satisfied (no counterexample).");

                for (int i = 0; i < specs.size(); i++) {
                    specResults.add(true);
                }
            }

            if (!traces.isEmpty()) {
                addLog(task, "Auto-saving " + traces.size() + " violation trace(s) to database.");
                saveTraces(traces, userId, taskId);
            }

            updateTaskProgress(taskId, 100, "Verification completed");
            completeTask(taskId, task, traces.isEmpty(), traces.size(), checkLogs, nusmvOutput);

        } catch (Exception e) {
            log.error("Async verification failed for task: {}", taskId, e);
            completeTask(taskId, task, false, 0, 
                addLog(task, "Error: " + e.getMessage()), 
                "Verification failed: " + e.getMessage());
        } finally {
            if (smvFileCreated && smvFile != null) {
                cleanupTempFile(smvFile);
            }
            runningTasks.remove(taskId);
            taskProgress.remove(taskId);
        }
    }

    private void handleCancellation(Long taskId, VerificationTaskPo task) {
        log.info("Handling cancellation for task: {}", taskId);
        if (task != null) {
            task.setStatus(VerificationTaskPo.TaskStatus.CANCELLED);
            task.setCompletedAt(LocalDateTime.now());
            taskRepository.save(task);
        }
        runningTasks.remove(taskId);
        taskProgress.remove(taskId);
    }

    /**
     * 完成任务
     */
    private void completeTask(Long taskId, VerificationTaskPo task, boolean isSafe, int traceCount, 
                             List<String> checkLogs, String nusmvOutput) {
        try {
            if (task != null) {
                task.setStatus(isSafe ? VerificationTaskPo.TaskStatus.COMPLETED : VerificationTaskPo.TaskStatus.FAILED);
                task.setCompletedAt(LocalDateTime.now());
                task.setIsSafe(isSafe);
                task.setViolatedSpecCount(traceCount);
                if (task.getStartedAt() != null && task.getCompletedAt() != null) {
                    long duration = java.time.Duration.between(task.getStartedAt(), task.getCompletedAt()).toMillis();
                    task.setProcessingTimeMs(duration);
                }
                if (nusmvOutput != null && nusmvOutput.length() > 10000) {
                    nusmvOutput = nusmvOutput.substring(0, 10000) + "\n... (truncated)";
                }
                task.setNusmvOutput(nusmvOutput);
                writeCheckLogs(task, checkLogs);
                task.setCheckLogs(checkLogs);
                if (!isSafe) {
                    String err = (checkLogs != null && !checkLogs.isEmpty())
                            ? checkLogs.get(checkLogs.size() - 1)
                            : "Verification failed";
                    task.setErrorMessage(err);
                } else {
                    task.setErrorMessage(null);
                }
                taskRepository.save(task);
            }
            log.info("Completed verification task: {}, safe: {}, traces: {}", taskId, isSafe, traceCount);
        } catch (Exception e) {
            log.error("Failed to complete task: {}", taskId, e);
        }
    }

    /**
     * 添加日志
     */
    private List<String> addLog(VerificationTaskPo task, String message) {
        List<String> logs = task != null ? new ArrayList<>(readCheckLogs(task)) : new ArrayList<>();
        logs.add(message);
        if (task != null) {
            writeCheckLogs(task, logs);
            try {
                taskRepository.save(task);
            } catch (Exception e) {
                log.warn("Failed to save task logs: {}", e.getMessage());
            }
        }
        return logs;
    }

    private List<String> readCheckLogs(VerificationTaskPo task) {
        if (task == null || task.getCheckLogsJson() == null || task.getCheckLogsJson().isBlank()) {
            return new ArrayList<>();
        }
        try {
            return objectMapper.readValue(task.getCheckLogsJson(), new TypeReference<List<String>>() {});
        } catch (Exception e) {
            log.warn("Failed to parse checkLogsJson for task {}", task.getId(), e);
            return new ArrayList<>();
        }
    }

    private void writeCheckLogs(VerificationTaskPo task, List<String> logs) {
        if (task == null) return;
        try {
            String json = objectMapper.writeValueAsString(logs == null ? Collections.emptyList() : logs);
            task.setCheckLogsJson(json);
        } catch (Exception e) {
            log.warn("Failed to serialize check logs for task {}", task.getId(), e);
        }
    }

    @Override
    public VerificationTaskDto getTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId).orElse(null);
        if (task != null) {
            task.setCheckLogs(readCheckLogs(task));
        }
        return verificationTaskMapper.toDto(task);
    }

    @Override
    public List<TraceDto> getUserTraces(Long userId) {
        log.debug("Getting traces for user {}", userId);
        List<TracePo> traces = traceRepository.findByUserIdOrderByCreatedAtDesc(userId);
        return traceMapper.toDtoList(traces);
    }

    @Override
    public TraceDto getTrace(Long userId, Long traceId) {
        log.debug("Getting trace {} for user {}", traceId, userId);
        return traceRepository.findByIdAndUserId(traceId, userId)
                .map(traceMapper::toDto)
                .orElse(null);
    }

    /**
     * 删除 Trace
     * 
     * @param userId 用户ID
     * @param traceId Trace ID
     */
    @Override
    @Transactional
    public void deleteTrace(Long userId, Long traceId) {
        log.debug("Deleting trace {} for user {}", traceId, userId);
        traceRepository.findByIdAndUserId(traceId, userId)
                .ifPresent(traceRepository::delete);
    }

    @Override
    public boolean cancelTask(Long userId, Long taskId) {
        log.info("Attempting to cancel task {} for user {}", taskId, userId);

        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId).orElse(null);
        if (task == null) {
            log.warn("Task not found or unauthorized: taskId={}, userId={}", taskId, userId);
            return false;
        }

        if (task.getStatus() != VerificationTaskPo.TaskStatus.RUNNING &&
            task.getStatus() != VerificationTaskPo.TaskStatus.PENDING) {
            log.warn("Task cannot be cancelled, status: {}", task.getStatus());
            return false;
        }

        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) {
            taskThread.interrupt();
            log.info("Interrupted task thread: {}", taskId);
        }

        task.setStatus(VerificationTaskPo.TaskStatus.CANCELLED);
        task.setCompletedAt(LocalDateTime.now());
        taskRepository.save(task);

        runningTasks.remove(taskId);
        taskProgress.remove(taskId);

        log.info("Task {} cancelled successfully", taskId);
        return true;
    }

    @Override
    public void updateTaskProgress(Long taskId, int progress, String message) {
        taskProgress.put(taskId, Math.min(100, Math.max(0, progress)));
        log.debug("Task {} progress: {}% - {}", taskId, progress, message);
    }

    public int getTaskProgress(Long taskId) {
        return taskProgress.getOrDefault(taskId, 0);
    }

    /**
     * 从 counterexample 生成 Trace 列表
     * 
     * @param counterexample NuSMV 输出的 counterexample
     * @param devices 设备节点列表
     * @param specs 规格列表
     * @param userId 用户ID
     * @return Trace 列表
     */
    private List<TraceDto> generateTracesFromCounterexample(String counterexample,
                                                            List<DeviceNodeDto> devices,
                                                            List<SpecificationDto> specs,
                                                            Long userId) {
        List<TraceDto> traces = new ArrayList<>();

        if (counterexample == null || counterexample.isEmpty()) {
            return traces;
        }

        // 简化处理：假设所有规格共享同一个 counterexample
        // 实际项目中可能需要为每个规格分别运行 NuSMV

        // 生成状态序列
        Map<String, DeviceSmvData> deviceSmvMap = buildDeviceSmvMap(devices);

        for (SpecificationDto spec : specs) {
            List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(counterexample, deviceSmvMap);

            if (!states.isEmpty()) {
                try {
                    TraceDto trace = TraceDto.builder()
                            .userId(userId)
                            .violatedSpecId(spec.getId())
                            .violatedSpecJson(specificationMapper.toJson(spec))
                            .states(states)
                            .createdAt(LocalDateTime.now())
                            .build();

                    traces.add(trace);
                } catch (Exception e) {
                    log.error("Failed to create trace for spec {}", spec.getId(), e);
                }
            }
        }

        return traces;
    }

    /**
     * 保存 Trace 到数据库
     */
    private void saveTraces(List<TraceDto> traces, Long userId) {
        for (TraceDto trace : traces) {
            trace.setUserId(userId);
            TracePo po = traceMapper.toPo(trace);
            if (po != null) {
                traceRepository.save(po);
            }
        }
    }

    private void saveTraces(List<TraceDto> traces, Long userId, Long taskId) {
        for (TraceDto trace : traces) {
            trace.setUserId(userId);
            trace.setVerificationTaskId(taskId);
            TracePo po = traceMapper.toPo(trace);
            if (po != null) {
                traceRepository.save(po);
            }
        }
    }

    /**
     * 构建错误结果
     */
    private VerificationResultDto buildErrorResult(String nusmvOutput, List<String> checkLogs) {
        return VerificationResultDto.builder()
                .safe(false)
                .traces(Collections.emptyList())
                .specResults(Collections.emptyList())
                .checkLogs(checkLogs)
                .nusmvOutput(truncateOutput(nusmvOutput))
                .build();
    }

    /**
     * 截断过长的输出
     */
    private String truncateOutput(String output) {
        if (output == null) {
            return null;
        }
        if (output.length() > MAX_OUTPUT_LENGTH) {
            return output.substring(0, MAX_OUTPUT_LENGTH) + "\n... (output truncated)";
        }
        return output;
    }

    /**
     * 构建设备 SMV 数据映射（用于解析 counterexample）
     */
    private Map<String, DeviceSmvData> buildDeviceSmvMap(List<DeviceNodeDto> devices) {
        Map<String, DeviceSmvData> map = new HashMap<>();
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = new DeviceSmvData();
            smv.id = device.getId();
            smv.name = device.getTemplateName();
            smv.deviceNo = extractDeviceNo(device.getId());
            smv.currentState = device.getState();
            map.put(device.getId(), smv);
        }
        return map;
    }

    private int extractDeviceNo(String deviceId) {
        if (deviceId == null) return 0;
        int lastUnderscore = deviceId.lastIndexOf('_');
        if (lastUnderscore >= 0 && lastUnderscore < deviceId.length() - 1) {
            try {
                return Integer.parseInt(deviceId.substring(lastUnderscore + 1));
            } catch (NumberFormatException e) {
                return 0;
            }
        }
        return 0;
    }

    /**
     * 清理临时文件
     */
    private void cleanupTempFile(File file) {
        if (file != null && file.exists()) {
            try {
                // 删除父目录
                File parentDir = file.getParentFile();
                if (parentDir != null && parentDir.isDirectory()) {
                    File[] files = parentDir.listFiles();
                    if (files != null) {
                        for (File f : files) {
                            f.delete();
                        }
                    }
                    parentDir.delete();
                }
                file.delete();
            } catch (Exception e) {
                log.warn("Failed to cleanup temp file: {}", file.getAbsolutePath(), e);
            }
        }
    }
}
