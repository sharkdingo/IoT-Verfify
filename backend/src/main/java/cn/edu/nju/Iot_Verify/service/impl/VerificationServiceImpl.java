package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
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
import jakarta.annotation.PostConstruct;
import jakarta.annotation.PreDestroy;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.scheduling.annotation.Async;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.io.*;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.*;

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
    private final NusmvConfig nusmvConfig;
    private final VerificationTaskRepository taskRepository;
    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final SpecificationMapper specificationMapper;
    private final VerificationTaskMapper verificationTaskMapper;
    private final ObjectMapper objectMapper;

    private static final int MAX_OUTPUT_LENGTH = 10000;
    private static final String UNKNOWN_VIOLATED_SPEC_ID = "__UNKNOWN_SPEC__";

    private final ConcurrentHashMap<Long, Thread> runningTasks = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<Long, Integer> taskProgress = new ConcurrentHashMap<>();
    private final Set<Long> cancelledTasks = ConcurrentHashMap.newKeySet();
    private final ExecutorService syncVerificationExecutor = Executors.newFixedThreadPool(
            4, r -> { Thread t = new Thread(r, "sync-verify"); return t; });

    @PostConstruct
    void cleanupStaleTasks() {
        List<VerificationTaskPo> staleTasks = taskRepository.findByStatusIn(
                List.of(VerificationTaskPo.TaskStatus.RUNNING, VerificationTaskPo.TaskStatus.PENDING));
        if (!staleTasks.isEmpty()) {
            log.warn("Found {} stale tasks on startup, marking as FAILED", staleTasks.size());
            String msg = "Server restarted while task was in progress";
            for (VerificationTaskPo task : staleTasks) {
                task.setStatus(VerificationTaskPo.TaskStatus.FAILED);
                task.setCompletedAt(LocalDateTime.now());
                task.setIsSafe(false);
                task.setErrorMessage(msg);
                writeCheckLogs(task, List.of(msg));
                taskRepository.save(task);
            }
        }
    }

    @PreDestroy
    void shutdownSyncExecutor() {
        syncVerificationExecutor.shutdown();
        try {
            if (!syncVerificationExecutor.awaitTermination(30, TimeUnit.SECONDS)) {
                syncVerificationExecutor.shutdownNow();
            }
        } catch (InterruptedException e) {
            syncVerificationExecutor.shutdownNow();
            Thread.currentThread().interrupt();
        }
    }

    // ==================== 同步验证 ====================

    @Override
    public VerificationResultDto verify(Long userId,
                                        List<DeviceVerificationDto> devices,
                                        List<RuleDto> rules,
                                        List<SpecificationDto> specs,
                                        boolean isAttack,
                                        int intensity,
                                        boolean enablePrivacy) {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
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

        long timeoutMs = nusmvConfig.getTimeoutMs() * 2; // generate + execute 总超时
        Future<VerificationResultDto> future = syncVerificationExecutor.submit(() ->
                doVerify(userId, devices, safeRules, specs, isAttack, intensity, enablePrivacy));

        try {
            return future.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            future.cancel(true);
            log.warn("Sync verification timed out after {}ms", timeoutMs);
            return buildErrorResult("", List.of("Verification timed out"));
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            log.error("Sync verification failed", cause);
            throw new InternalServerException("Verification failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return buildErrorResult("", List.of("Verification interrupted"));
        }
    }

    private VerificationResultDto doVerify(Long userId,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           List<SpecificationDto> specs,
                                           boolean isAttack, int intensity,
                                           boolean enablePrivacy) {
        List<String> checkLogs = new ArrayList<>();
        File smvFile = null;
        Map<String, DeviceSmvData> deviceSmvMap = null;
        VerificationResultDto finalResult = null;

        try {
            checkLogs.add("Generating NuSMV model...");
            SmvGenerator.GenerateResult genResult = smvGenerator.generate(userId, devices, rules, specs, isAttack, intensity, enablePrivacy);
            smvFile = genResult.smvFile();
            deviceSmvMap = genResult.deviceSmvMap();
            if (smvFile == null || !smvFile.exists()) {
                checkLogs.add("Failed to generate NuSMV model file");
                finalResult = buildErrorResult("", checkLogs);
                return finalResult;
            }
            checkLogs.add("Model generated: " + smvFile.getAbsolutePath());

            checkLogs.add("Executing NuSMV verification...");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (!result.isSuccess()) {
                checkLogs.add("NuSMV execution failed: " + result.getErrorMessage());
                finalResult = buildErrorResult("", checkLogs);
                return finalResult;
            }
            checkLogs.add("NuSMV execution completed.");

            // Build per-spec results — 复用 generate 阶段的 deviceSmvMap
            finalResult = buildVerificationResult(result, devices, rules, specs, userId, null, checkLogs, deviceSmvMap);
            return finalResult;

        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) Thread.currentThread().interrupt();
            log.error("Verification error", e);
            checkLogs.add("Error: " + e.getMessage());
            finalResult = buildErrorResult("", checkLogs);
            return finalResult;
        } catch (Exception e) {
            log.error("Verification failed", e);
            throw new InternalServerException("Verification failed: " + e.getMessage());
        } finally {
            // 只要 tempDir 存在就保存 result.json（成功/失败均保存，方便调试）
            if (finalResult != null) {
                saveResultJson(smvFile, finalResult);
            }
            cleanupTempFile(smvFile);
        }
    }

    private void saveResultJson(File smvFile, VerificationResultDto verificationResult) {
        if (smvFile == null || smvFile.getParentFile() == null) return;
        try {
            File jsonFile = new File(smvFile.getParentFile(), "result.json");
            Result<VerificationResultDto> wrapped = Result.success(verificationResult);
            objectMapper.writerWithDefaultPrettyPrinter().writeValue(jsonFile, wrapped);
            log.info("Verification result JSON saved to: {}", jsonFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save result JSON: {}", e.getMessage());
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
        VerificationTaskPo saved = taskRepository.save(Objects.requireNonNull(task));
        log.info("Created verification task: {} for user: {}", saved.getId(), userId);
        return Objects.requireNonNull(saved.getId());
    }

    @Override
    @Transactional
    public void failTaskById(Long taskId, String errorMessage) {
        taskRepository.findById(Objects.requireNonNull(taskId, "taskId must not be null"))
                .ifPresent(task -> failTask(task, errorMessage));
    }

    @Override
    @Async("verificationTaskExecutor")
    public void verifyAsync(Long userId, Long taskId,
                            List<DeviceVerificationDto> devices,
                            List<RuleDto> rules,
                            List<SpecificationDto> specs,
                            boolean isAttack, int intensity,
                            boolean enablePrivacy) {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
        log.info("Starting async verification task: {} for user: {}", taskId, userId);

        runningTasks.put(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        File smvFile = null;
        VerificationTaskPo task = null;
        try {
            task = taskRepository.findById(Objects.requireNonNull(taskId)).orElse(null);
            if (task == null) {
                log.error("Task not found: {}", taskId);
                return;
            }

            // 在设置 RUNNING 之前检查是否已被取消（PENDING 状态下被 cancelTask 直接写了 CANCELLED）
            if (cancelledTasks.contains(taskId)) {
                return;
            }

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
            SmvGenerator.GenerateResult genResult = smvGenerator.generate(userId, devices, safeRules, specs, isAttack, intensity, enablePrivacy);
            smvFile = genResult.smvFile();
            Map<String, DeviceSmvData> deviceSmvMap = genResult.deviceSmvMap();
            if (cancelledTasks.contains(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }
            if (smvFile == null || !smvFile.exists()) {
                failTask(task, "Failed to generate NuSMV model file");
                return;
            }


            updateTaskProgress(taskId, 50, "Executing NuSMV");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (cancelledTasks.contains(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }

            if (!result.isSuccess()) {
                failTask(task, "NuSMV execution failed: " + result.getErrorMessage());
                return;
            }

            updateTaskProgress(taskId, 80, "Parsing results");
            VerificationResultDto vResult = buildVerificationResult(
                    result, devices, safeRules, specs, userId, taskId, new ArrayList<>(), deviceSmvMap);

            updateTaskProgress(taskId, 100, "Verification completed");
            completeTask(task, vResult.isSafe(),
                    vResult.getTraces() != null ? vResult.getTraces().size() : 0,
                    vResult.getCheckLogs(), truncateOutput(result.getOutput()));

        } catch (Exception e) {
            if (cancelledTasks.contains(taskId)) {
                // 被取消导致的异常，由 finally 统一处理状态
                log.info("Async verification cancelled for task: {}", taskId);
            } else {
                log.error("Async verification failed for task: {}", taskId, e);
                failTask(task, "Verification failed: " + e.getMessage());
            }
        } finally {
            cleanupTempFile(smvFile);
            // 统一处理取消状态
            if (cancelledTasks.remove(taskId)) {
                if (task != null) handleCancellation(task);
            }
            runningTasks.remove(taskId);
            taskProgress.remove(taskId);
        }
    }

    // ==================== 查询方法 ====================

    @Override
    public VerificationTaskDto getTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("Task", taskId));
        task.setCheckLogs(readCheckLogs(task));
        return verificationTaskMapper.toDto(task);
    }

    @Override
    public List<TraceDto> getUserTraces(Long userId) {
        return traceMapper.toDtoList(traceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
    public TraceDto getTrace(Long userId, Long traceId) {
        return traceRepository.findByIdAndUserId(traceId, userId)
                .map(traceMapper::toDto)
                .orElseThrow(() -> new ResourceNotFoundException("Trace", traceId));
    }

    @Override
    @Transactional
    public void deleteTrace(Long userId, Long traceId) {
        traceRepository.findByIdAndUserId(traceId, userId).ifPresent(traceRepository::delete);
    }

    @Override
    @Transactional
    public boolean cancelTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId).orElse(null);
        if (task == null) return false;
        if (task.getStatus() != VerificationTaskPo.TaskStatus.RUNNING &&
            task.getStatus() != VerificationTaskPo.TaskStatus.PENDING) return false;

        cancelledTasks.add(taskId);
        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) {
            // 任务正在执行，interrupt 后由 verifyAsync 的 finally 统一处理状态
            taskThread.interrupt();
        } else {
            // 任务尚未开始（PENDING 在队列中），直接更新数据库状态
            task.setStatus(VerificationTaskPo.TaskStatus.CANCELLED);
            task.setCompletedAt(LocalDateTime.now());
            taskRepository.save(task);
        }

        return true;
    }

    @Override
    public void updateTaskProgress(Long taskId, int progress, String message) {
        taskProgress.put(taskId, Math.min(100, Math.max(0, progress)));
        log.debug("Task {} progress: {}% - {}", taskId, progress, message);
    }

    @Override
    public int getTaskProgress(Long userId, Long taskId) {
        // 校验任务归属
        taskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("Task", taskId));
        return taskProgress.getOrDefault(taskId, 0);
    }

    // ==================== 核心：构建 per-spec 验证结果 ====================

    private VerificationResultDto buildVerificationResult(NusmvResult result,
                                                          List<DeviceVerificationDto> devices,
                                                          List<RuleDto> rules,
                                                          List<SpecificationDto> specs,
                                                          Long userId, Long taskId,
                                                          List<String> checkLogs,
                                                          Map<String, DeviceSmvData> deviceSmvMap) {
        List<Boolean> specResults = new ArrayList<>();
        List<TraceDto> traces = new ArrayList<>();
        List<SpecCheckResult> specCheckResults = result.getSpecResults();

        // 过滤掉空 spec，与 SmvSpecificationBuilder 的跳过逻辑保持一致
        List<SpecificationDto> effectiveSpecs = specs.stream()
                .filter(s -> s != null)
                .filter(s -> (s.getAConditions() != null && !s.getAConditions().isEmpty()) ||
                             (s.getIfConditions() != null && !s.getIfConditions().isEmpty()))
                .toList();

        // effectiveSpecs=0：所有 spec 都被过滤掉（无 A/IF 条件），无可验证规格
        if (effectiveSpecs.isEmpty()) {
            checkLogs.add("No valid specifications to verify (all filtered out)");
            return VerificationResultDto.builder()
                    .safe(true).traces(List.of()).specResults(List.of())
                    .checkLogs(checkLogs).nusmvOutput(truncateOutput(result.getOutput())).build();
        }

        // fail-closed: 无法解析 spec 结果时标记为不安全
        boolean parseIncomplete = false;

        if (specCheckResults.isEmpty()) {
            checkLogs.add("Warning: could not parse per-spec results from NuSMV output");
            log.warn("No spec results parsed from NuSMV output, marking all {} specs as failed (fail-closed)", effectiveSpecs.size());
            for (int i = 0; i < effectiveSpecs.size(); i++) specResults.add(false);
            parseIncomplete = true;
        } else if (specCheckResults.size() != effectiveSpecs.size()) {
            // 数量不一致：结果不可信，fail-closed
            log.warn("Spec count mismatch: NuSMV returned {} results but {} specs were generated. Marking as unsafe (fail-closed).",
                    specCheckResults.size(), effectiveSpecs.size());
            checkLogs.add("Warning: spec result count mismatch (got " + specCheckResults.size()
                    + ", expected " + effectiveSpecs.size() + ")");
            // 仍然处理已有结果用于诊断，但缺失项补 false
            parseIncomplete = true;
            // 只处理 min(specCheckResults, effectiveSpecs) 个结果，多余的丢弃
            int bound = Math.min(specCheckResults.size(), effectiveSpecs.size());
            for (int specIdx = 0; specIdx < bound; specIdx++) {
                SpecCheckResult scr = specCheckResults.get(specIdx);
                specResults.add(scr.isPassed());
                SpecificationDto violatedSpec = effectiveSpecs.get(specIdx);
                if (!scr.isPassed() && scr.getCounterexample() != null) {
                    checkLogs.add("Spec " + (specIdx + 1) + " violated: " + scr.getSpecExpression());
                    List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                            scr.getCounterexample(), deviceSmvMap);
                    if (!states.isEmpty()) {
                        TraceDto trace = TraceDto.builder()
                                .userId(userId)
                                .verificationTaskId(taskId)
                                .violatedSpecId(violatedSpec.getId() != null ? violatedSpec.getId() : UNKNOWN_VIOLATED_SPEC_ID)
                                .violatedSpecJson(specificationMapper.toJson(violatedSpec))
                                .states(states)
                                .createdAt(LocalDateTime.now())
                                .build();
                        traces.add(trace);
                    }
                } else if (scr.isPassed()) {
                    checkLogs.add("Spec " + (specIdx + 1) + " satisfied");
                } else {
                    checkLogs.add("Spec " + (specIdx + 1) + " violated (no counterexample): " + scr.getSpecExpression());
                }
            }
            // 多余的 NuSMV 结果记录日志但不加入 specResults
            if (specCheckResults.size() > effectiveSpecs.size()) {
                checkLogs.add("Warning: " + (specCheckResults.size() - effectiveSpecs.size())
                        + " extra NuSMV result(s) discarded");
            }
            // 缺失的 spec 补 false
            for (int i = specCheckResults.size(); i < effectiveSpecs.size(); i++) {
                specResults.add(false);
                checkLogs.add("Spec " + (i + 1) + " result missing, treated as violated (fail-closed)");
            }
        } else {
            int specIdx = 0;
            for (SpecCheckResult scr : specCheckResults) {
                specResults.add(scr.isPassed());
                SpecificationDto violatedSpec = specIdx < effectiveSpecs.size() ? effectiveSpecs.get(specIdx) : null;
                if (!scr.isPassed() && scr.getCounterexample() != null) {
                    checkLogs.add("Spec " + (specIdx + 1) + " violated: " + scr.getSpecExpression());
                    List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                            scr.getCounterexample(), deviceSmvMap);
                    if (!states.isEmpty()) {
                        TraceDto trace = TraceDto.builder()
                                .userId(userId)
                                .verificationTaskId(taskId)
                                .violatedSpecId(violatedSpec != null ? violatedSpec.getId() : UNKNOWN_VIOLATED_SPEC_ID)
                                .violatedSpecJson(violatedSpec != null ? specificationMapper.toJson(violatedSpec) : null)
                                .states(states)
                                .createdAt(LocalDateTime.now())
                                .build();
                        traces.add(trace);
                    }
                } else if (scr.isPassed()) {
                    checkLogs.add("Spec " + (specIdx + 1) + " satisfied");
                } else {
                    checkLogs.add("Spec " + (specIdx + 1) + " violated (no counterexample): " + scr.getSpecExpression());
                }
                specIdx++;
            }
        }

        // safe 基于 specResults 判定；解析不完整时强制 unsafe
        boolean safe = !parseIncomplete && specResults.stream().allMatch(r -> r);
        if (!traces.isEmpty()) {
            saveTraces(traces, userId, taskId);
            checkLogs.add("Auto-saved " + traces.size() + " violation trace(s).");
        }
        if (parseIncomplete) {
            checkLogs.add("Verification marked unsafe because per-spec results are incomplete/unreliable (fail-closed).");
        } else if (!safe) {
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
