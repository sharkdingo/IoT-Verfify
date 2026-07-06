package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SimulationOutput;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.*;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.SimulationTaskRepository;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTaskMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTraceMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.io.File;
import java.io.IOException;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.*;

@Slf4j
@Service
public class SimulationServiceImpl extends AbstractAsyncTaskService<SimulationTaskPo> implements SimulationService {

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final NusmvConfig nusmvConfig;
    private final SimulationTraceRepository simulationTraceRepository;
    private final SimulationTaskRepository simulationTaskRepository;
    private final SimulationTraceMapper simulationTraceMapper;
    private final SimulationTaskMapper simulationTaskMapper;
    private final ThreadPoolTaskExecutor simulationTaskExecutor;
    private final ThreadPoolTaskExecutor syncSimulationExecutor;

    public SimulationServiceImpl(SmvGenerator smvGenerator,
                                 SmvTraceParser smvTraceParser,
                                 NusmvExecutor nusmvExecutor,
                                 NusmvConfig nusmvConfig,
                                 SimulationTraceRepository simulationTraceRepository,
                                 SimulationTaskRepository simulationTaskRepository,
                                 SimulationTraceMapper simulationTraceMapper,
                                 SimulationTaskMapper simulationTaskMapper,
                                 ObjectMapper objectMapper,
                                 @Qualifier("simulationTaskExecutor") ThreadPoolTaskExecutor simulationTaskExecutor,
                                 @Qualifier("syncSimulationExecutor") ThreadPoolTaskExecutor syncSimulationExecutor) {
        super(objectMapper, "SimulationTask");
        this.smvGenerator = smvGenerator;
        this.smvTraceParser = smvTraceParser;
        this.nusmvExecutor = nusmvExecutor;
        this.nusmvConfig = nusmvConfig;
        this.simulationTraceRepository = simulationTraceRepository;
        this.simulationTaskRepository = simulationTaskRepository;
        this.simulationTraceMapper = simulationTraceMapper;
        this.simulationTaskMapper = simulationTaskMapper;
        this.simulationTaskExecutor = simulationTaskExecutor;
        this.syncSimulationExecutor = syncSimulationExecutor;
    }

    @PostConstruct
    void cleanupStaleTasks() {
        List<SimulationTaskPo> staleTasks = simulationTaskRepository.findByStatusIn(
                List.of(SimulationTaskPo.TaskStatus.RUNNING, SimulationTaskPo.TaskStatus.PENDING));
        if (!staleTasks.isEmpty()) {
            log.warn("Found {} stale simulation tasks on startup, marking as FAILED", staleTasks.size());
            String msg = "Server restarted while simulation task was in progress";
            for (SimulationTaskPo task : staleTasks) {
                task.setStatus(SimulationTaskPo.TaskStatus.FAILED);
                task.setProgress(100);
                task.setCompletedAt(LocalDateTime.now());
                task.setErrorMessage(msg);
                writeCheckLogs(task, List.of(msg));
                simulationTaskRepository.save(task);
            }
        }
    }

    @Override
    public SimulationResultDto simulate(Long userId, SimulationRequestDto request) {
        SimulationInput input = validateAndNormalize(request);
        return simulateInput(userId, input);
    }

    private SimulationResultDto simulateInput(Long userId, SimulationInput input) {
        log.info("Starting simulation: userId={}, devices={}, steps={}, attack={}, intensity={}",
                userId, input.devices().size(), input.steps(), input.attack(), input.intensity());

        long timeoutMs = nusmvConfig.getTimeoutMs() * 2;
        Future<SimulationResultDto> future;
        try {
            future = syncSimulationExecutor.submit(() ->
                    doSimulate(userId, input.devices(), input.rules(), input.steps(), input.attack(),
                            input.intensity(), input.enablePrivacy()));
        } catch (RejectedExecutionException e) {
            log.warn("Simulation request rejected: executor is saturated ({})", syncSimulationExecutorSnapshot());
            throw new ServiceUnavailableException("Simulation service is busy, please retry later", e);
        }

        try {
            return future.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            future.cancel(true);
            purgeCancelledSyncTasks();
            log.warn("Simulation timed out after {}ms", timeoutMs);
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(input.steps())
                    .logs(List.of("Simulation timed out")).build();
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            if (cause instanceof ServiceUnavailableException sue) throw sue;
            if (cause instanceof SmvGenerationException sge) throw sge;
            log.error("Simulation failed", cause);
            throw new InternalServerException("Simulation failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(input.steps())
                    .logs(List.of("Simulation interrupted")).build();
        }
    }

    private SimulationInput validateAndNormalize(SimulationRequestDto request) {
        if (request == null) {
            throw new ValidationException("request", "Simulation request cannot be null");
        }
        SimulationRequestDto snapshot = snapshotRequest(request);
        List<DeviceVerificationDto> devices = copyRequiredList(
                snapshot.getDevices(), "devices", "Devices list cannot be empty");
        List<RuleDto> rules = copyOptionalList(snapshot.getRules(), "rules");
        int steps = snapshot.getSteps();
        if (steps < 1 || steps > 100) {
            throw new ValidationException("steps", "Steps must be between 1 and 100");
        }
        int intensity = snapshot.getIntensity();
        if (intensity < 0 || intensity > 50) {
            throw new ValidationException("intensity", "Intensity must be between 0 and 50");
        }

        snapshot.setDevices(devices);
        snapshot.setRules(rules);
        snapshot.setSteps(steps);
        snapshot.setIntensity(intensity);

        Map<String, String> errors = NusmvRequestValidator.newErrors();
        NusmvRequestValidator.validateDevices(devices, errors);
        NusmvRequestValidator.validateRules(rules, errors);
        NusmvRequestValidator.throwIfErrors(errors);

        return new SimulationInput(devices, rules, steps, snapshot.isAttack(), intensity,
                snapshot.isEnablePrivacy(), snapshot);
    }

    private SimulationRequestDto snapshotRequest(SimulationRequestDto request) {
        try {
            return objectMapper.convertValue(request, SimulationRequestDto.class);
        } catch (IllegalArgumentException e) {
            throw new ValidationException("request", "Simulation request cannot be snapshotted");
        }
    }

    private <T> List<T> copyRequiredList(List<T> values, String field, String emptyMessage) {
        if (values == null || values.isEmpty()) {
            throw new ValidationException(field, emptyMessage);
        }
        return copyList(values, field);
    }

    private <T> List<T> copyOptionalList(List<T> values, String field) {
        if (values == null || values.isEmpty()) {
            return List.of();
        }
        return copyList(values, field);
    }

    private <T> List<T> copyList(List<T> values, String field) {
        List<T> copy = new ArrayList<>(values);
        for (int i = 0; i < copy.size(); i++) {
            if (copy.get(i) == null) {
                throw new ValidationException(field + "[" + i + "]", "must not be null");
            }
        }
        return copy;
    }

    // Service-internal: task creation is only reachable through submitSimulation and
    // the package-private async path below; it is no longer part of the public interface.
    @Transactional
    Long createTask(Long userId, int requestedSteps) {
        SimulationTaskPo task = SimulationTaskPo.builder()
                .userId(userId)
                .status(SimulationTaskPo.TaskStatus.PENDING)
                .requestedSteps(requestedSteps)
                .createdAt(LocalDateTime.now())
                .build();
        SimulationTaskPo saved = simulationTaskRepository.save(Objects.requireNonNull(task));
        log.info("Created simulation task: {} for user: {}", saved.getId(), userId);
        return saved.getId();
    }

    // Service-internal failure compensation, reachable only from the submit/async paths below.
    @Transactional
    void failTaskById(Long taskId, String errorMessage) {
        simulationTaskRepository.findById(Objects.requireNonNull(taskId, "taskId must not be null"))
                .ifPresent(task -> failTask(task, errorMessage, List.of(errorMessage)));
    }

    // Package-private async entry: assumes the caller already created the task and passes a
    // non-null taskId. Production code goes through submitSimulation; retained at this
    // visibility so same-package tests can drive the "execute with a fixed taskId" path.
    void simulateAsync(Long userId, Long taskId, SimulationRequestDto request) {
        Long requiredTaskId = requireTaskId(taskId);
        SimulationInput input;
        try {
            input = validateAndNormalize(request);
        } catch (ValidationException e) {
            failTaskById(requiredTaskId, e.getMessage());
            throw e;
        }
        try {
            enqueueSimulationTask(userId, requiredTaskId, input);
        } catch (TaskRejectedException e) {
            failTaskById(requiredTaskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later", e);
        }
    }

    @Override
    public Long submitSimulation(Long userId, SimulationRequestDto request) {
        SimulationInput input = validateAndNormalize(request);
        Long taskId = createTask(userId, input.steps());
        try {
            enqueueSimulationTask(userId, taskId, input);
        } catch (TaskRejectedException e) {
            log.warn("Simulation task {} rejected: thread pool full", taskId);
            failTaskById(taskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later", e);
        }
        return taskId;
    }

    private void enqueueSimulationTask(Long userId, Long taskId, SimulationInput input) {
        Long requiredTaskId = requireTaskId(taskId);
        SimulationInput requiredInput = Objects.requireNonNull(input, "simulation input must not be null");
        simulationTaskExecutor.execute(() -> runSimulationTask(userId, requiredTaskId, requiredInput));
    }

    private Long requireTaskId(Long taskId) {
        if (taskId == null) {
            throw new ValidationException("taskId", "Task id cannot be null");
        }
        return taskId;
    }

    private void runSimulationTask(Long userId, Long taskId, SimulationInput input) {
        String requestJson = buildRequestSnapshot(input.request());

        registerRunningTask(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        SimulationTaskPo task = null;
        try {
            // Check in-memory cancellation marker (fast path for same-instance cancellation).
            if (isTaskCancelled(taskId)) {
                return;
            }

            // Atomically transition PENDING → RUNNING to close the cancel-vs-start race window.
            // A plain findById + save was vulnerable to TOCTOU: a concurrent cancel could set
            // CANCELLED between the read and the save, and the save would overwrite it back to RUNNING.
            LocalDateTime startedAt = LocalDateTime.now();
            String startCheckLogs = serializeCheckLogs(List.of("Task started"));
            int updated = simulationTaskRepository.startTaskIfStillPending(
                    taskId,
                    SimulationTaskPo.TaskStatus.RUNNING,
                    startedAt, 0, startCheckLogs,
                    SimulationTaskPo.TaskStatus.PENDING);
            if (updated == 0) {
                log.info("Simulation task {} is no longer PENDING (cancelled or already started), aborting", taskId);
                return;
            }

            // Load entity for subsequent use (failTask/completeTask only need id and startedAt).
            task = simulationTaskRepository.findById(Objects.requireNonNull(taskId)).orElse(null);
            if (task == null) {
                log.error("Simulation task not found after atomic start: {}", taskId);
                return;
            }

            updateTaskProgress(taskId, 20, "Executing simulation");
            SimulationResultDto result = doSimulate(userId, input.devices(), input.rules(), input.steps(),
                    input.attack(), input.intensity(), input.enablePrivacy());

            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }

            if (result.getStates() == null || result.getStates().isEmpty()) {
                failTask(task, deriveFailureMessage(result), result.getLogs());
                return;
            }

            updateTaskProgress(taskId, 90, "Persisting simulation trace");
            SimulationTracePo savedTrace = persistSimulationTrace(
                    userId,
                    result,
                    requestJson);

            updateTaskProgress(taskId, 100, "Simulation completed");
            completeTask(task, savedTrace.getId(), result.getSteps(), result.getLogs());

        } catch (Exception e) {
            if (isTaskCancelled(taskId)) {
                log.info("Async simulation cancelled for task: {}", taskId);
            } else {
                log.error("Async simulation failed for task: {}", taskId, e);
                failTask(task, "Simulation failed: " + e.getMessage(), List.of("Simulation failed: " + e.getMessage()));
            }
        } finally {
            if (removeCancelledMark(taskId)) {
                if (task != null) handleCancellation(task);
            }
            removeRunningTask(taskId);
            removeTaskProgress(taskId);
        }
    }

    private record SimulationInput(List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules,
                                   int steps,
                                   boolean attack,
                                   int intensity,
                                   boolean enablePrivacy,
                                   SimulationRequestDto request) {}

    @Override
    @Transactional(readOnly = true)
    public SimulationTaskDto getTask(Long userId, Long taskId) {
        SimulationTaskPo task = simulationTaskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTask", taskId));
        task.setCheckLogs(readCheckLogs(task));
        return simulationTaskMapper.toDto(task);
    }

    @Override
    @Transactional(readOnly = true)
    public List<SimulationTaskSummaryDto> getTasks(Long userId, List<Long> excludedTaskIds) {
        List<Long> normalizedExcludedIds = normalizeExcludedTaskIds(excludedTaskIds);
        List<SimulationTaskPo> tasks = normalizedExcludedIds.isEmpty()
                ? simulationTaskRepository.findByUserIdOrderByCreatedAtDesc(userId)
                : simulationTaskRepository.findByUserIdAndIdNotInOrderByCreatedAtDesc(userId, normalizedExcludedIds);
        return simulationTaskMapper.toSummaryDtoList(
                tasks);
    }

    private static List<Long> normalizeExcludedTaskIds(List<Long> excludedTaskIds) {
        if (excludedTaskIds == null || excludedTaskIds.isEmpty()) {
            return List.of();
        }
        return excludedTaskIds.stream()
                .filter(Objects::nonNull)
                .distinct()
                .toList();
    }

    @Override
    @Transactional(readOnly = true)
    public int getTaskProgress(Long userId, Long taskId) {
        return super.getTaskProgress(userId, taskId);
    }

    @Override
    @Transactional
    public boolean cancelTask(Long userId, Long taskId) {
        return super.cancelTask(userId, taskId);
    }

    @Override
    @Transactional
    public SimulationTraceDto simulateAndSave(Long userId, SimulationRequestDto request) {
        SimulationInput input = validateAndNormalize(request);
        SimulationResultDto result = simulateInput(userId, input);

        if (result.getStates() == null || result.getStates().isEmpty()) {
            throw new InternalServerException("Simulation produced no states, nothing to save");
        }

        SimulationTracePo saved = persistSimulationTrace(userId, result, buildRequestSnapshot(input.request()));
        log.info("Saved simulation trace: id={}, userId={}, steps={}", saved.getId(), userId, saved.getSteps());
        return simulationTraceMapper.toDto(saved);
    }

    @Override
    @Transactional(readOnly = true)
    public List<SimulationTraceSummaryDto> getUserSimulations(Long userId) {
        return simulationTraceMapper.toSummaryDtoList(
                simulationTraceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
    @Transactional(readOnly = true)
    public SimulationTraceDto getSimulation(Long userId, Long id) {
        return simulationTraceRepository.findByIdAndUserId(id, userId)
                .map(simulationTraceMapper::toDto)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTrace", id));
    }

    @Override
    @Transactional
    public void deleteSimulation(Long userId, Long id) {
        SimulationTracePo po = simulationTraceRepository.findByIdAndUserId(id, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTrace", id));
        simulationTraceRepository.delete(Objects.requireNonNull(po));
    }

    private SimulationResultDto doSimulate(Long userId,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           int steps,
                                           boolean isAttack,
                                           int intensity,
                                           boolean enablePrivacy) {
        List<String> logs = new ArrayList<>();
        File smvFile = null;
        SimulationResultDto finalResult = null;
        String requestJson = buildRequestSnapshot(devices, rules, steps, isAttack, intensity, enablePrivacy);

        try {
            logs.add("Generating NuSMV model (simulation mode)...");
            SmvGenerator.GenerateResult genResult = smvGenerator.generate(
                    userId, devices, rules, List.of(), isAttack, intensity, enablePrivacy, SmvGenerator.GeneratePurpose.SIMULATION);
            smvFile = genResult.smvFile();
            Map<String, DeviceSmvData> deviceSmvMap = genResult.deviceSmvMap();

            if (smvFile == null || !smvFile.exists()) {
                logs.add("Failed to generate NuSMV model file");
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
                return finalResult;
            }
            logs.add("Model generated: " + smvFile.getAbsolutePath());
            saveRequestJson(smvFile, requestJson);

            logs.add("Executing NuSMV interactive simulation (" + steps + " steps)...");
            SimulationOutput simOutput = nusmvExecutor.executeInteractiveSimulation(smvFile, steps);

            if (!simOutput.isSuccess()) {
                if (simOutput.isBusy()) {
                    logs.add("Simulation busy: " + simOutput.getErrorMessage());
                    finalResult = SimulationResultDto.builder()
                            .states(List.of()).steps(0).requestedSteps(steps).logs(logs)
                            .nusmvOutput(truncateOutput(simOutput.getErrorMessage())).build();
                    throw new ServiceUnavailableException("NuSMV simulation service is busy, please retry later");
                }
                logs.add("Simulation failed: " + simOutput.getErrorMessage());
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs)
                        .nusmvOutput(truncateOutput(simOutput.getErrorMessage())).build();
                return finalResult;
            }
            logs.add("Simulation completed.");

            List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                    simOutput.getTraceText(), deviceSmvMap);
            logs.add("Parsed " + states.size() + " states from simulation trace.");

            if (states.isEmpty()) {
                logs.add("No valid states parsed from simulation trace.");
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps)
                        .nusmvOutput(truncateOutput(simOutput.getRawOutput()))
                        .logs(logs).build();
                return finalResult;
            }

            int actualSteps = Math.max(states.size() - 1, 0);

            finalResult = SimulationResultDto.builder()
                    .states(states)
                    .steps(actualSteps)
                    .requestedSteps(steps)
                    .nusmvOutput(truncateOutput(simOutput.getRawOutput()))
                    .logs(logs)
                    .build();
            return finalResult;

        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) {
                Thread.currentThread().interrupt();
                log.info("Simulation interrupted");
                logs.add("Simulation interrupted");
            } else {
                log.error("Simulation error", e);
                logs.add("Error: " + e.getMessage());
            }
            finalResult = SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
            return finalResult;
        } catch (ServiceUnavailableException e) {
            throw e;
        } catch (SmvGenerationException e) {
            log.error("SMV generation failed", e);
            if (finalResult == null) {
                logs.add("Error: " + e.getMessage());
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
            }
            throw e;
        } catch (Exception e) {
            log.error("Simulation failed", e);
            if (finalResult == null) {
                logs.add("Error: " + e.getMessage());
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
            }
            throw new InternalServerException("Simulation failed: " + e.getMessage());
        } finally {
            if (finalResult != null) {
                saveResultJson(smvFile, finalResult);
            }
            cleanupTempFile(smvFile);
        }
    }

    private void completeTask(SimulationTaskPo task, Long simulationTraceId, int steps, List<String> logs) {
        if (task == null) return;
        try {
            LocalDateTime completedAt = LocalDateTime.now();
            Long processingTimeMs = task.getStartedAt() != null
                    ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
            String checkLogsJson = serializeCheckLogs(logs);
            int updated = simulationTaskRepository.completeTaskIfNotCancelled(
                    task.getId(),
                    SimulationTaskPo.TaskStatus.COMPLETED,
                    completedAt, steps, simulationTraceId,
                    null, checkLogsJson, processingTimeMs,
                    SimulationTaskPo.TaskStatus.CANCELLED);
            if (updated == 0) {
                log.info("Simulation task {} was already cancelled, skipping completion", task.getId());
            }
        } catch (Exception e) {
            log.error("Failed to complete simulation task: {}", task.getId(), e);
        }
    }

    private void failTask(SimulationTaskPo task, String errorMessage, List<String> logs) {
        if (task == null) return;
        try {
            LocalDateTime completedAt = LocalDateTime.now();
            Long processingTimeMs = task.getStartedAt() != null
                    ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
            String checkLogsJson = serializeCheckLogs(logs == null || logs.isEmpty() ? List.of(errorMessage) : logs);
            int updated = simulationTaskRepository.failTaskIfNotCancelled(
                    task.getId(),
                    SimulationTaskPo.TaskStatus.FAILED,
                    completedAt, errorMessage,
                    checkLogsJson, processingTimeMs,
                    SimulationTaskPo.TaskStatus.CANCELLED);
            if (updated == 0) {
                log.info("Simulation task {} was already cancelled, skipping fail", task.getId());
            }
        } catch (Exception e) {
            log.error("Failed to mark simulation task as failed: {}", task.getId(), e);
        }
    }

    private SimulationTracePo persistSimulationTrace(Long userId, SimulationResultDto result, String requestJson) {
        SimulationTracePo po = SimulationTracePo.builder()
                .userId(userId)
                .requestedSteps(result.getRequestedSteps())
                .steps(result.getSteps())
                .statesJson(JsonUtils.toJson(result.getStates()))
                .logsJson(JsonUtils.toJsonOrEmpty(result.getLogs()))
                .nusmvOutput(result.getNusmvOutput())
                .requestJson(requestJson)
                .build();
        return simulationTraceRepository.save(Objects.requireNonNull(po));
    }

    private String buildRequestSnapshot(List<DeviceVerificationDto> devices,
                                        List<RuleDto> rules,
                                        int steps,
                                        boolean isAttack,
                                        int intensity,
                                        boolean enablePrivacy) {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setDevices(devices);
        request.setRules(rules != null ? rules : List.of());
        request.setSteps(steps);
        request.setAttack(isAttack);
        request.setIntensity(intensity);
        request.setEnablePrivacy(enablePrivacy);
        return JsonUtils.toJson(request);
    }

    private String buildRequestSnapshot(SimulationRequestDto request) {
        return JsonUtils.toJson(request);
    }

    private String deriveFailureMessage(SimulationResultDto result) {
        if (result == null) {
            return "Simulation failed";
        }
        List<String> logs = result.getLogs();
        if (logs == null || logs.isEmpty()) {
            return "Simulation failed";
        }
        return logs.get(logs.size() - 1);
    }

    private void saveResultJson(File smvFile, SimulationResultDto simulationResult) {
        if (smvFile == null || smvFile.getParentFile() == null || simulationResult == null) return;
        try {
            File jsonFile = new File(smvFile.getParentFile(), "result.json");
            Result<SimulationResultDto> wrapped = wrapResultForDebugFile(simulationResult);
            objectMapper.writerWithDefaultPrettyPrinter().writeValue(jsonFile, wrapped);
            log.info("Simulation result JSON saved to: {}", jsonFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save simulation result JSON: {}", e.getMessage());
        }
    }

    private void saveRequestJson(File smvFile, String requestJson) {
        if (smvFile == null || smvFile.getParentFile() == null || requestJson == null || requestJson.isBlank()) return;
        try {
            File jsonFile = new File(smvFile.getParentFile(), "request.json");
            objectMapper.writerWithDefaultPrettyPrinter()
                    .writeValue(jsonFile, objectMapper.readTree(requestJson));
            log.info("Simulation request JSON saved to: {}", jsonFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save simulation request JSON: {}", e.getMessage());
        }
    }

    private Result<SimulationResultDto> wrapResultForDebugFile(SimulationResultDto simulationResult) {
        Result<SimulationResultDto> wrapped = new Result<>();
        wrapped.setData(simulationResult);
        if (isSimulationFailureResult(simulationResult)) {
            wrapped.setCode(inferSimulationErrorCode(simulationResult));
            wrapped.setMessage(inferSimulationErrorMessage(simulationResult));
        } else {
            wrapped.setCode(200);
            wrapped.setMessage("success");
        }
        return wrapped;
    }

    private boolean isSimulationFailureResult(SimulationResultDto result) {
        if (result == null) return true;
        return result.getStates() == null || result.getStates().isEmpty();
    }

    private int inferSimulationErrorCode(SimulationResultDto result) {
        List<String> logs = result != null ? result.getLogs() : null;
        if (logs != null) {
            for (String logLine : logs) {
                if (logLine == null) continue;
                String lower = logLine.toLowerCase();
                if (lower.contains("busy")) return 503;
                if (lower.contains("timed out")) return 504;
            }
        }
        return 500;
    }

    private String inferSimulationErrorMessage(SimulationResultDto result) {
        List<String> logs = result != null ? result.getLogs() : null;
        if (logs != null && !logs.isEmpty()) {
            String last = logs.get(logs.size() - 1);
            if (last != null && !last.isBlank()) {
                return last;
            }
        }
        return "simulation failed";
    }

    private void cleanupTempFile(File file) {
        // Keeping NuSMV model file for review: model.smv, request.json, output.txt, result.json
        // Temp directories (nusmv_*) are retained for post-mortem debugging.
    }

    private String syncSimulationExecutorSnapshot() {
        try {
            ThreadPoolExecutor nativeExecutor = syncSimulationExecutor.getThreadPoolExecutor();
            return "poolSize=" + nativeExecutor.getPoolSize()
                    + ", active=" + nativeExecutor.getActiveCount()
                    + ", queueSize=" + nativeExecutor.getQueue().size()
                    + ", remainingCapacity=" + nativeExecutor.getQueue().remainingCapacity();
        } catch (IllegalStateException ignored) {
            return "executor=uninitialized";
        }
    }

    private void purgeCancelledSyncTasks() {
        try {
            syncSimulationExecutor.getThreadPoolExecutor().purge();
        } catch (IllegalStateException ignored) {
            // executor may not be initialized yet
        }
    }

    // ── AbstractAsyncTaskService hooks ─────────────────────────────────

    @Override
    protected Optional<SimulationTaskPo> findTaskByIdAndUserId(Long id, Long userId) {
        return simulationTaskRepository.findByIdAndUserId(id, userId);
    }

    @Override
    protected int atomicCancelTask(Long taskId, LocalDateTime completedAt) {
        return simulationTaskRepository.cancelTaskIfStillActive(
                taskId,
                SimulationTaskPo.TaskStatus.CANCELLED,
                completedAt,
                List.of(SimulationTaskPo.TaskStatus.PENDING,
                        SimulationTaskPo.TaskStatus.RUNNING));
    }

    @Override
    protected int atomicUpdateProgress(Long taskId, int progress) {
        return simulationTaskRepository.updateProgressIfActive(taskId, progress);
    }
}
