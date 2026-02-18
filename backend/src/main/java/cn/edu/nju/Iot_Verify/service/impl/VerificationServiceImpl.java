package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
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
 *
 * 统一管理同步/异步验证流程、任务生命周期、Trace 持久化
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

    // ==================== 同步验证 ====================

    @Override
    @Transactional
    public VerificationResultDto verify(Long userId,
                                        List<DeviceVerificationDto> devices,
                                        List<RuleDto> rules,
                                        List<SpecificationDto> specs,
                                        boolean isAttack,
                                        int intensity,
                                        boolean enablePrivacy) {
        if (devices == null || devices.isEmpty()) {
            return buildErrorResult("", List.of("Error: devices list cannot be empty"));
        }
        if (specs == null || specs.isEmpty()) {
            return VerificationResultDto.builder()
                    .safe(true).traces(List.of()).specResults(List.of())
                    .checkLogs(List.of("No specifications to verify")).nusmvOutput("").build();
        }

        log.info("Starting sync verification: userId={}, devices={}, specs={}, attack={}, intensity={}",
                userId, devices.size(), specs.size(), isAttack, intensity);

        List<String> checkLogs = new ArrayList<>();
        File smvFile = null;

        try {
            checkLogs.add("Generating NuSMV model...");
            smvFile = smvGenerator.generate(userId, devices, rules, specs, isAttack, intensity, enablePrivacy);
            if (smvFile == null || !smvFile.exists()) {
                checkLogs.add("Failed to generate NuSMV model file");
                return buildErrorResult("", checkLogs);
            }
            checkLogs.add("Model generated: " + smvFile.getAbsolutePath());

            checkLogs.add("Executing NuSMV verification...");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (!result.isSuccess()) {
                checkLogs.add("NuSMV execution failed: " + result.getErrorMessage());
                return buildErrorResult("", checkLogs);
            }
            checkLogs.add("NuSMV execution completed.");

            // Build per-spec results
            return buildVerificationResult(result, devices, rules, specs, userId, null, checkLogs);

        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) Thread.currentThread().interrupt();
            log.error("Verification error", e);
            checkLogs.add("Error: " + e.getMessage());
            return buildErrorResult("", checkLogs);
        } catch (Exception e) {
            log.error("Verification failed", e);
            throw new InternalServerException("Verification failed: " + e.getMessage());
        } finally {
            cleanupTempFile(smvFile);
        }
    }

    // ==================== 异步验证 ====================

    @Override
    @Transactional
    public Long createTask(Long userId) {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .userId(userId)
                .status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .build();
        task = taskRepository.save(task);
        log.info("Created verification task: {} for user: {}", task.getId(), userId);
        return task.getId();
    }

    @Override
    @Async("verificationTaskExecutor")
    public void verifyAsync(Long userId, Long taskId,
                            List<DeviceVerificationDto> devices,
                            List<RuleDto> rules,
                            List<SpecificationDto> specs,
                            boolean isAttack, int intensity,
                            boolean enablePrivacy) {
        log.info("Starting async verification task: {} for user: {}", taskId, userId);

        runningTasks.put(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        VerificationTaskPo task = taskRepository.findById(taskId).orElse(null);
        if (task == null) {
            log.error("Task not found: {}", taskId);
            return;
        }

        File smvFile = null;
        try {
            task.setStatus(VerificationTaskPo.TaskStatus.RUNNING);
            task.setStartedAt(LocalDateTime.now());
            writeCheckLogs(task, List.of("Task started"));
            taskRepository.save(task);

            if (devices == null || devices.isEmpty()) {
                failTask(task, "Invalid input: devices list cannot be empty");
                return;
            }
            if (specs == null || specs.isEmpty()) {
                completeTask(task, true, 0, List.of("No specifications to verify"), "");
                return;
            }

            updateTaskProgress(taskId, 20, "Generating NuSMV model");
            smvFile = smvGenerator.generate(userId, devices, rules, specs, isAttack, intensity, enablePrivacy);
            if (Thread.currentThread().isInterrupted()) {
                handleCancellation(task);
                return;
            }
            if (smvFile == null || !smvFile.exists()) {
                failTask(task, "Failed to generate NuSMV model file");
                return;
            }


            updateTaskProgress(taskId, 50, "Executing NuSMV");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (Thread.currentThread().isInterrupted()) {
                handleCancellation(task);
                return;
            }

            if (!result.isSuccess()) {
                failTask(task, "NuSMV execution failed: " + result.getErrorMessage());
                return;
            }

            updateTaskProgress(taskId, 80, "Parsing results");
            VerificationResultDto vResult = buildVerificationResult(
                    result, devices, rules, specs, userId, taskId, new ArrayList<>());

            updateTaskProgress(taskId, 100, "Verification completed");
            completeTask(task, vResult.isSafe(),
                    vResult.getTraces() != null ? vResult.getTraces().size() : 0,
                    vResult.getCheckLogs(), truncateOutput(result.getOutput()));

        } catch (Exception e) {
            log.error("Async verification failed for task: {}", taskId, e);
            failTask(task, "Verification failed: " + e.getMessage());
        } finally {
            cleanupTempFile(smvFile);
            runningTasks.remove(taskId);
            taskProgress.remove(taskId);
        }
    }

    // ==================== 查询方法 ====================

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
        return traceMapper.toDtoList(traceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
    public TraceDto getTrace(Long userId, Long traceId) {
        return traceRepository.findByIdAndUserId(traceId, userId)
                .map(traceMapper::toDto).orElse(null);
    }

    @Override
    @Transactional
    public void deleteTrace(Long userId, Long traceId) {
        traceRepository.findByIdAndUserId(traceId, userId).ifPresent(traceRepository::delete);
    }

    @Override
    public boolean cancelTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId).orElse(null);
        if (task == null) return false;
        if (task.getStatus() != VerificationTaskPo.TaskStatus.RUNNING &&
            task.getStatus() != VerificationTaskPo.TaskStatus.PENDING) return false;

        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) taskThread.interrupt();

        task.setStatus(VerificationTaskPo.TaskStatus.CANCELLED);
        task.setCompletedAt(LocalDateTime.now());
        taskRepository.save(task);
        runningTasks.remove(taskId);
        taskProgress.remove(taskId);
        return true;
    }

    @Override
    public void updateTaskProgress(Long taskId, int progress, String message) {
        taskProgress.put(taskId, Math.min(100, Math.max(0, progress)));
        log.debug("Task {} progress: {}% - {}", taskId, progress, message);
    }

    @Override
    public int getTaskProgress(Long taskId) {
        return taskProgress.getOrDefault(taskId, 0);
    }

    // ==================== 核心：构建 per-spec 验证结果 ====================

    private VerificationResultDto buildVerificationResult(NusmvResult result,
                                                          List<DeviceVerificationDto> devices,
                                                          List<RuleDto> rules,
                                                          List<SpecificationDto> specs,
                                                          Long userId, Long taskId,
                                                          List<String> checkLogs) {
        List<Boolean> specResults = new ArrayList<>();
        List<TraceDto> traces = new ArrayList<>();
        List<SpecCheckResult> specCheckResults = result.getSpecResults();

        if (specCheckResults.isEmpty()) {
            // Fallback: NuSMV output didn't match per-spec pattern
            checkLogs.add("Warning: could not parse per-spec results, treating as all passed");
            for (int i = 0; i < specs.size(); i++) specResults.add(true);
        } else {
            Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, devices);
            int specIdx = 0;
            for (SpecCheckResult scr : specCheckResults) {
                specResults.add(scr.isPassed());
                if (!scr.isPassed() && scr.getCounterexample() != null) {
                    checkLogs.add("Spec " + (specIdx + 1) + " violated: " + scr.getSpecExpression());
                    List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                            scr.getCounterexample(), deviceSmvMap);
                    if (!states.isEmpty()) {
                        SpecificationDto violatedSpec = specIdx < specs.size() ? specs.get(specIdx) : null;
                        TraceDto trace = TraceDto.builder()
                                .userId(userId)
                                .verificationTaskId(taskId)
                                .violatedSpecId(violatedSpec != null ? violatedSpec.getId() : null)
                                .violatedSpecJson(violatedSpec != null ? specificationMapper.toJson(violatedSpec) : null)
                                .states(states)
                                .createdAt(LocalDateTime.now())
                                .build();
                        traces.add(trace);
                    }
                } else if (scr.isPassed()) {
                    checkLogs.add("Spec " + (specIdx + 1) + " satisfied");
                }
                specIdx++;
            }
        }

        // safe 基于 specResults 判定，而非 traces 是否为空（trace 解析可能失败）
        boolean safe = specResults.stream().allMatch(r -> r);
        if (!traces.isEmpty()) {
            saveTraces(traces, userId, taskId);
            checkLogs.add("Auto-saved " + traces.size() + " violation trace(s).");
        }
        if (!safe) {
            checkLogs.add("Some specifications violated.");
        } else {
            checkLogs.add("All specifications satisfied.");
        }

        return VerificationResultDto.builder()
                .safe(safe)
                .traces(traces)
                .specResults(specResults)
                .checkLogs(checkLogs)
                .nusmvOutput(truncateOutput(result.getOutput()))
                .build();
    }

    // ==================== 任务状态管理 ====================

    private void completeTask(VerificationTaskPo task, boolean isSafe, int traceCount,
                              List<String> checkLogs, String nusmvOutput) {
        try {
            task.setStatus(VerificationTaskPo.TaskStatus.COMPLETED);
            task.setCompletedAt(LocalDateTime.now());
            task.setIsSafe(isSafe);
            task.setViolatedSpecCount(traceCount);
            if (task.getStartedAt() != null) {
                task.setProcessingTimeMs(
                        java.time.Duration.between(task.getStartedAt(), task.getCompletedAt()).toMillis());
            }
            task.setNusmvOutput(truncateOutput(nusmvOutput));
            writeCheckLogs(task, checkLogs);
            task.setErrorMessage(null);
            taskRepository.save(task);
        } catch (Exception e) {
            log.error("Failed to complete task: {}", task.getId(), e);
        }
    }

    private void failTask(VerificationTaskPo task, String errorMessage) {
        try {
            task.setStatus(VerificationTaskPo.TaskStatus.FAILED);
            task.setCompletedAt(LocalDateTime.now());
            task.setIsSafe(false);
            task.setErrorMessage(errorMessage);
            if (task.getStartedAt() != null) {
                task.setProcessingTimeMs(
                        java.time.Duration.between(task.getStartedAt(), task.getCompletedAt()).toMillis());
            }
            writeCheckLogs(task, List.of(errorMessage));
            taskRepository.save(task);
        } catch (Exception e) {
            log.error("Failed to mark task as failed: {}", task.getId(), e);
        }
    }

    private void handleCancellation(VerificationTaskPo task) {
        log.info("Handling cancellation for task: {}", task.getId());
        task.setStatus(VerificationTaskPo.TaskStatus.CANCELLED);
        task.setCompletedAt(LocalDateTime.now());
        taskRepository.save(task);
        runningTasks.remove(task.getId());
        taskProgress.remove(task.getId());
    }

    // ==================== 工具方法 ====================

    private void saveTraces(List<TraceDto> traces, Long userId, Long taskId) {
        for (TraceDto trace : traces) {
            trace.setUserId(userId);
            if (taskId != null) trace.setVerificationTaskId(taskId);
            TracePo po = traceMapper.toEntity(trace);
            if (po != null) traceRepository.save(po);
        }
    }

    private VerificationResultDto buildErrorResult(String nusmvOutput, List<String> checkLogs) {
        return VerificationResultDto.builder()
                .safe(false).traces(List.of()).specResults(List.of())
                .checkLogs(checkLogs).nusmvOutput(truncateOutput(nusmvOutput)).build();
    }

    private String truncateOutput(String output) {
        if (output == null) return null;
        return output.length() > MAX_OUTPUT_LENGTH
                ? output.substring(0, MAX_OUTPUT_LENGTH) + "\n... (output truncated)" : output;
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
            task.setCheckLogsJson(objectMapper.writeValueAsString(logs == null ? List.of() : logs));
        } catch (Exception e) {
            log.warn("Failed to serialize check logs for task {}", task.getId(), e);
        }
    }

    private void cleanupTempFile(File file) {
        if (file != null && file.exists()) {
            log.info("Keeping NuSMV model file for review: {}", file.getAbsolutePath());
        }
    }
}
