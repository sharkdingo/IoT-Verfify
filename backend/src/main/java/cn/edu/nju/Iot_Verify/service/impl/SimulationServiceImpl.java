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
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.SimulationTaskRepository;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTaskMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTraceMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.scheduling.annotation.Async;
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
public class SimulationServiceImpl implements SimulationService {

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final NusmvConfig nusmvConfig;
    private final SimulationTraceRepository simulationTraceRepository;
    private final SimulationTaskRepository simulationTaskRepository;
    private final SimulationTraceMapper simulationTraceMapper;
    private final SimulationTaskMapper simulationTaskMapper;
    private final ObjectMapper objectMapper;
    private final ThreadPoolTaskExecutor syncSimulationExecutor;

    private static final int MAX_OUTPUT_LENGTH = 10000;

    private final ConcurrentHashMap<Long, Thread> runningTasks = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<Long, Integer> taskProgress = new ConcurrentHashMap<>();
    private final Set<Long> cancelledTasks = ConcurrentHashMap.newKeySet();

    public SimulationServiceImpl(SmvGenerator smvGenerator,
                                 SmvTraceParser smvTraceParser,
                                 NusmvExecutor nusmvExecutor,
                                 NusmvConfig nusmvConfig,
                                 SimulationTraceRepository simulationTraceRepository,
                                 SimulationTaskRepository simulationTaskRepository,
                                 SimulationTraceMapper simulationTraceMapper,
                                 SimulationTaskMapper simulationTaskMapper,
                                 ObjectMapper objectMapper,
                                 @Qualifier("syncSimulationExecutor") ThreadPoolTaskExecutor syncSimulationExecutor) {
        this.smvGenerator = smvGenerator;
        this.smvTraceParser = smvTraceParser;
        this.nusmvExecutor = nusmvExecutor;
        this.nusmvConfig = nusmvConfig;
        this.simulationTraceRepository = simulationTraceRepository;
        this.simulationTaskRepository = simulationTaskRepository;
        this.simulationTraceMapper = simulationTraceMapper;
        this.simulationTaskMapper = simulationTaskMapper;
        this.objectMapper = objectMapper;
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
                task.setCompletedAt(LocalDateTime.now());
                task.setErrorMessage(msg);
                writeCheckLogs(task, List.of(msg));
                simulationTaskRepository.save(task);
            }
        }
    }

    @Override
    public SimulationResultDto simulate(Long userId,
                                        List<DeviceVerificationDto> devices,
                                        List<RuleDto> rules,
                                        int steps,
                                        boolean isAttack,
                                        int intensity,
                                        boolean enablePrivacy) {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
        if (devices == null || devices.isEmpty()) {
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Error: devices list cannot be empty")).build();
        }

        log.info("Starting simulation: userId={}, devices={}, steps={}, attack={}, intensity={}",
                userId, devices.size(), steps, isAttack, intensity);

        long timeoutMs = nusmvConfig.getTimeoutMs() * 2;
        Future<SimulationResultDto> future;
        try {
            future = syncSimulationExecutor.submit(() ->
                    doSimulate(userId, devices, safeRules, steps, isAttack, intensity, enablePrivacy));
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
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Simulation timed out")).build();
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            if (cause instanceof ServiceUnavailableException sue) throw sue;
            log.error("Simulation failed", cause);
            throw new InternalServerException("Simulation failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Simulation interrupted")).build();
        }
    }

    @Override
    @Transactional
    public Long createTask(Long userId, int requestedSteps) {
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

    @Override
    @Transactional
    public void failTaskById(Long taskId, String errorMessage) {
        simulationTaskRepository.findById(Objects.requireNonNull(taskId, "taskId must not be null"))
                .ifPresent(task -> failTask(task, errorMessage, List.of(errorMessage)));
    }

    @Override
    @Async("simulationTaskExecutor")
    public void simulateAsync(Long userId, Long taskId,
                              List<DeviceVerificationDto> devices,
                              List<RuleDto> rules,
                              int steps,
                              boolean isAttack,
                              int intensity,
                              boolean enablePrivacy) {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();

        runningTasks.put(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        SimulationTaskPo task = null;
        try {
            task = simulationTaskRepository.findById(Objects.requireNonNull(taskId)).orElse(null);
            if (task == null) {
                log.error("Simulation task not found: {}", taskId);
                return;
            }
            if (cancelledTasks.contains(taskId)) {
                return;
            }

            task.setStatus(SimulationTaskPo.TaskStatus.RUNNING);
            task.setStartedAt(LocalDateTime.now());
            writeCheckLogs(task, List.of("Task started"));
            simulationTaskRepository.save(task);

            if (devices == null || devices.isEmpty()) {
                failTask(task, "Invalid input: devices list cannot be empty", List.of("Invalid input: devices list cannot be empty"));
                return;
            }

            updateTaskProgress(taskId, 20, "Executing simulation");
            SimulationResultDto result = doSimulate(userId, devices, safeRules, steps, isAttack, intensity, enablePrivacy);

            if (cancelledTasks.contains(taskId) || Thread.currentThread().isInterrupted()) {
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
                    buildRequestSnapshot(devices, safeRules, steps, isAttack, intensity, enablePrivacy));

            updateTaskProgress(taskId, 100, "Simulation completed");
            completeTask(task, savedTrace.getId(), result.getSteps(), result.getLogs());

        } catch (Exception e) {
            if (cancelledTasks.contains(taskId)) {
                log.info("Async simulation cancelled for task: {}", taskId);
            } else {
                log.error("Async simulation failed for task: {}", taskId, e);
                failTask(task, "Simulation failed: " + e.getMessage(), List.of("Simulation failed: " + e.getMessage()));
            }
        } finally {
            if (cancelledTasks.remove(taskId)) {
                if (task != null) handleCancellation(task);
            }
            runningTasks.remove(taskId);
            taskProgress.remove(taskId);
        }
    }

    @Override
    public SimulationTaskDto getTask(Long userId, Long taskId) {
        SimulationTaskPo task = simulationTaskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTask", taskId));
        task.setCheckLogs(readCheckLogs(task));
        return simulationTaskMapper.toDto(task);
    }

    @Override
    public int getTaskProgress(Long userId, Long taskId) {
        SimulationTaskPo task = simulationTaskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTask", taskId));

        Integer progress = taskProgress.get(taskId);
        if (progress != null) {
            return progress;
        }
        if (task.getStatus() == SimulationTaskPo.TaskStatus.COMPLETED
                || task.getStatus() == SimulationTaskPo.TaskStatus.FAILED
                || task.getStatus() == SimulationTaskPo.TaskStatus.CANCELLED) {
            return 100;
        }
        return 0;
    }

    @Override
    @Transactional
    public boolean cancelTask(Long userId, Long taskId) {
        SimulationTaskPo task = simulationTaskRepository.findByIdAndUserId(taskId, userId).orElse(null);
        if (task == null) return false;
        if (task.getStatus() != SimulationTaskPo.TaskStatus.RUNNING
                && task.getStatus() != SimulationTaskPo.TaskStatus.PENDING) {
            return false;
        }

        cancelledTasks.add(taskId);
        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) {
            taskThread.interrupt();
        } else {
            task.setStatus(SimulationTaskPo.TaskStatus.CANCELLED);
            task.setCompletedAt(LocalDateTime.now());
            simulationTaskRepository.save(task);
        }
        return true;
    }

    @Override
    @Transactional
    public SimulationTraceDto simulateAndSave(Long userId, SimulationRequestDto request) {
        SimulationResultDto result = simulate(userId,
                request.getDevices(), request.getRules(), request.getSteps(),
                request.isAttack(), request.getIntensity(), request.isEnablePrivacy());

        if (result.getStates() == null || result.getStates().isEmpty()) {
            throw new InternalServerException("Simulation produced no states, nothing to save");
        }

        SimulationTracePo saved = persistSimulationTrace(userId, result, JsonUtils.toJson(request));
        log.info("Saved simulation trace: id={}, userId={}, steps={}", saved.getId(), userId, saved.getSteps());
        return simulationTraceMapper.toDto(saved);
    }

    @Override
    public List<SimulationTraceSummaryDto> getUserSimulations(Long userId) {
        return simulationTraceMapper.toSummaryDtoList(
                simulationTraceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
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
            if (e instanceof InterruptedException) Thread.currentThread().interrupt();
            log.error("Simulation error", e);
            logs.add("Error: " + e.getMessage());
            finalResult = SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
            return finalResult;
        } catch (ServiceUnavailableException e) {
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
            task.setStatus(SimulationTaskPo.TaskStatus.COMPLETED);
            task.setCompletedAt(LocalDateTime.now());
            task.setSteps(steps);
            task.setSimulationTraceId(simulationTraceId);
            task.setErrorMessage(null);
            if (task.getStartedAt() != null) {
                task.setProcessingTimeMs(java.time.Duration.between(task.getStartedAt(), task.getCompletedAt()).toMillis());
            }
            writeCheckLogs(task, logs);
            simulationTaskRepository.save(task);
        } catch (Exception e) {
            log.error("Failed to complete simulation task: {}", task.getId(), e);
        }
    }

    private void failTask(SimulationTaskPo task, String errorMessage, List<String> logs) {
        if (task == null) return;
        try {
            task.setStatus(SimulationTaskPo.TaskStatus.FAILED);
            task.setCompletedAt(LocalDateTime.now());
            task.setErrorMessage(errorMessage);
            if (task.getStartedAt() != null) {
                task.setProcessingTimeMs(java.time.Duration.between(task.getStartedAt(), task.getCompletedAt()).toMillis());
            }
            writeCheckLogs(task, logs == null || logs.isEmpty() ? List.of(errorMessage) : logs);
            simulationTaskRepository.save(task);
        } catch (Exception e) {
            log.error("Failed to mark simulation task as failed: {}", task.getId(), e);
        }
    }

    private void handleCancellation(SimulationTaskPo task) {
        task.setStatus(SimulationTaskPo.TaskStatus.CANCELLED);
        task.setCompletedAt(LocalDateTime.now());
        simulationTaskRepository.save(task);
    }

    private void updateTaskProgress(Long taskId, int progress, String message) {
        taskProgress.put(taskId, Math.min(100, Math.max(0, progress)));
        log.debug("Simulation task {} progress: {}% - {}", taskId, progress, message);
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

    private List<String> readCheckLogs(SimulationTaskPo task) {
        if (task == null || task.getCheckLogsJson() == null || task.getCheckLogsJson().isBlank()) {
            return new ArrayList<>();
        }
        try {
            return objectMapper.readValue(task.getCheckLogsJson(), new TypeReference<List<String>>() {});
        } catch (Exception e) {
            log.warn("Failed to parse checkLogsJson for simulation task {}", task.getId(), e);
            return new ArrayList<>();
        }
    }

    private void writeCheckLogs(SimulationTaskPo task, List<String> logs) {
        if (task == null) return;
        try {
            task.setCheckLogsJson(objectMapper.writeValueAsString(logs == null ? List.of() : logs));
        } catch (Exception e) {
            log.warn("Failed to serialize check logs for simulation task {}", task.getId(), e);
        }
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
        if (file != null && file.exists()) {
            log.info("Keeping NuSMV model file for review: {}", file.getAbsolutePath());
        }
    }

    private String truncateOutput(String output) {
        if (output == null) return null;
        return output.length() > MAX_OUTPUT_LENGTH
                ? output.substring(0, MAX_OUTPUT_LENGTH) + "\n... (output truncated)" : output;
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
}
