package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SimulationOutput;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.AsyncTaskAdmissionConfig;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.*;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.AsyncTaskQuotaExceededException;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SimulationExecutionException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.SimulationTaskRepository;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.service.FormalOperationAdmission;
import cn.edu.nju.Iot_Verify.service.ChatExecutionLeaseGuard;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTaskMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTraceMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.annotation.PostConstruct;
import jakarta.annotation.PreDestroy;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.data.domain.PageRequest;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.io.File;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicReference;

@Slf4j
@Service
public class SimulationServiceImpl extends AbstractAsyncTaskService<SimulationTaskPo> implements SimulationService {

    private static final Duration TASK_LEASE_DURATION = Duration.ofMinutes(2);
    private static final long LEASE_MAINTENANCE_SECONDS = 10L;
    private static final List<SimulationTaskPo.TaskStatus> ACTIVE_STATUSES = List.of(
            SimulationTaskPo.TaskStatus.PENDING,
            SimulationTaskPo.TaskStatus.RUNNING);

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final NusmvConfig nusmvConfig;
    private final SimulationTraceRepository simulationTraceRepository;
    private final SimulationTaskRepository simulationTaskRepository;
    private final UserRepository userRepository;
    private final SimulationTraceMapper simulationTraceMapper;
    private final SimulationTaskMapper simulationTaskMapper;
    private final ThreadPoolTaskExecutor simulationTaskExecutor;
    private final ThreadPoolTaskExecutor syncSimulationExecutor;
    private final TransactionTemplate transactionTemplate;
    private final ChatExecutionLeaseGuard chatExecutionLeaseGuard;
    private final FormalOperationAdmission formalOperationAdmission;
    private final AsyncTaskAdmissionConfig.Limits taskAdmissionLimits;
    private final String workerId = UUID.randomUUID().toString();
    private final ScheduledExecutorService leaseMaintenanceExecutor =
            Executors.newSingleThreadScheduledExecutor(runnable -> {
                Thread thread = new Thread(runnable, "simulation-task-lease-maintenance");
                thread.setDaemon(true);
                return thread;
            });
    private final ConcurrentHashMap<Long, LocalSimulationExecution> localExecutions =
            new ConcurrentHashMap<>();

    @Autowired
    public SimulationServiceImpl(SmvGenerator smvGenerator,
                                 SmvTraceParser smvTraceParser,
                                 NusmvExecutor nusmvExecutor,
                                 NusmvConfig nusmvConfig,
                                 SimulationTraceRepository simulationTraceRepository,
                                 SimulationTaskRepository simulationTaskRepository,
                                 UserRepository userRepository,
                                 SimulationTraceMapper simulationTraceMapper,
                                 SimulationTaskMapper simulationTaskMapper,
                                 ObjectMapper objectMapper,
                                 @Qualifier("simulationTaskExecutor") ThreadPoolTaskExecutor simulationTaskExecutor,
                                 @Qualifier("syncSimulationExecutor") ThreadPoolTaskExecutor syncSimulationExecutor,
                                 TransactionTemplate transactionTemplate,
                                 ChatExecutionLeaseGuard chatExecutionLeaseGuard,
                                 FormalOperationAdmission formalOperationAdmission,
                                 AsyncTaskAdmissionConfig taskAdmissionConfig) {
        super(objectMapper, "SimulationTask");
        this.smvGenerator = smvGenerator;
        this.smvTraceParser = smvTraceParser;
        this.nusmvExecutor = nusmvExecutor;
        this.nusmvConfig = nusmvConfig;
        this.simulationTraceRepository = simulationTraceRepository;
        this.simulationTaskRepository = simulationTaskRepository;
        this.userRepository = userRepository;
        this.simulationTraceMapper = simulationTraceMapper;
        this.simulationTaskMapper = simulationTaskMapper;
        this.simulationTaskExecutor = simulationTaskExecutor;
        this.syncSimulationExecutor = syncSimulationExecutor;
        this.transactionTemplate = transactionTemplate;
        this.chatExecutionLeaseGuard = chatExecutionLeaseGuard;
        this.formalOperationAdmission = formalOperationAdmission;
        this.taskAdmissionLimits = taskAdmissionConfig.getSimulation();
    }

    SimulationServiceImpl(SmvGenerator smvGenerator,
                          SmvTraceParser smvTraceParser,
                          NusmvExecutor nusmvExecutor,
                          NusmvConfig nusmvConfig,
                          SimulationTraceRepository simulationTraceRepository,
                          SimulationTaskRepository simulationTaskRepository,
                          UserRepository userRepository,
                          SimulationTraceMapper simulationTraceMapper,
                          SimulationTaskMapper simulationTaskMapper,
                          ObjectMapper objectMapper,
                          ThreadPoolTaskExecutor simulationTaskExecutor,
                          ThreadPoolTaskExecutor syncSimulationExecutor,
                          TransactionTemplate transactionTemplate,
                          ChatExecutionLeaseGuard chatExecutionLeaseGuard,
                          FormalOperationAdmission formalOperationAdmission) {
        this(smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig,
                simulationTraceRepository, simulationTaskRepository, userRepository,
                simulationTraceMapper, simulationTaskMapper, objectMapper,
                simulationTaskExecutor, syncSimulationExecutor, transactionTemplate, chatExecutionLeaseGuard,
                formalOperationAdmission,
                new AsyncTaskAdmissionConfig());
    }

    private void requireChatExecutionLease() {
        chatExecutionLeaseGuard.requireCurrentExecutionLease();
    }

    @PostConstruct
    void initializeTaskLeaseMaintenance() {
        maintainTaskLeases();
        leaseMaintenanceExecutor.scheduleWithFixedDelay(
                this::maintainTaskLeases,
                LEASE_MAINTENANCE_SECONDS,
                LEASE_MAINTENANCE_SECONDS,
                TimeUnit.SECONDS);
    }

    @PreDestroy
    void stopTaskLeaseMaintenance() {
        leaseMaintenanceExecutor.shutdownNow();
    }

    void maintainTaskLeases() {
        List<LocalSimulationExecution> executions = List.copyOf(localExecutions.values());
        try {
            databaseNow();
        } catch (RuntimeException e) {
            stopSimulationExecutionsWithExpiredConfirmation(executions);
            log.warn("Could not read database time while maintaining simulation task leases", e);
            return;
        }
        for (LocalSimulationExecution execution : executions) {
            try {
                boolean renewed = TaskLeaseRenewal.renew(
                        transactionTemplate,
                        () -> simulationTaskRepository.findByIdForUpdate(execution.taskId),
                        this::databaseNow,
                        simulationTaskRepository::saveAndFlush,
                        workerId,
                        TASK_LEASE_DURATION);
                if (!renewed) {
                    execution.requestStop();
                } else {
                    execution.leaseConfirmation.confirm();
                }
            } catch (RuntimeException e) {
                if (execution.leaseConfirmation.isUnconfirmedFor(TASK_LEASE_DURATION)) {
                    execution.requestStop();
                    log.warn("Stopped local simulation task {} after its lease could not be confirmed for a full TTL",
                            execution.taskId);
                } else {
                    log.warn("Could not renew simulation task lease {}; the next cycle will retry",
                            execution.taskId, e);
                }
            }
        }
        try {
            LocalDateTime recoveryTime = databaseNow();
            String message = "The simulation worker stopped before the task completed";
            int recovered = simulationTaskRepository.failExpiredActiveTasks(
                    SimulationTaskPo.TaskStatus.FAILED,
                    recoveryTime,
                    message,
                    serializeCheckLogs(List.of(message)),
                    ACTIVE_STATUSES,
                    recoveryTime);
            if (recovered > 0) {
                log.warn("Recovered {} expired simulation task lease(s)", recovered);
            }
        } catch (RuntimeException e) {
            log.warn("Could not recover expired simulation task leases; the next cycle will retry", e);
        }
    }

    private void stopSimulationExecutionsWithExpiredConfirmation(
            List<LocalSimulationExecution> executions) {
        for (LocalSimulationExecution execution : executions) {
            if (execution.leaseConfirmation.isUnconfirmedFor(TASK_LEASE_DURATION)) {
                execution.requestStop();
                log.warn("Stopped local simulation task {} after the database could not confirm its lease for a full TTL",
                        execution.taskId);
            }
        }
    }

    @Override
    public SimulationResultDto simulate(Long userId, SimulationRequestDto request) {
        return formalOperationAdmission.execute(userId, () -> simulateWithoutAdmission(userId, request));
    }

    private SimulationResultDto simulateWithoutAdmission(Long userId, SimulationRequestDto request) {
        SimulationInput input = validateAndNormalize(userId, request);
        SimulationResultDto result = simulateInput(userId, input, SmvGenerator.TempModelContext.sync());
        result.setHistoryPersistence(RunPersistenceDto.notRequested());
        return result;
    }

    @Override
    public SimulationResultDto simulateWithTemplateSnapshot(
            Long userId,
            SimulationRequestDto request,
            Map<String, DeviceManifest> templateManifests) {
        return formalOperationAdmission.execute(userId, () -> {
            SimulationInput input = validateAndNormalize(userId, request, templateManifests);
            SimulationResultDto result = simulateInput(userId, input, SmvGenerator.TempModelContext.sync());
            result.setHistoryPersistence(RunPersistenceDto.notRequested());
            return result;
        });
    }

    private SimulationResultDto simulateInput(Long userId, SimulationInput input,
                                              SmvGenerator.TempModelContext tempModelContext) {
        log.info("Starting simulation: userId={}, devices={}, steps={}, attack={}, attackBudget={}",
                userId, input.devices().size(), input.steps(), input.attack(), input.attackBudget());

        long timeoutMs = nusmvConfig.getTimeoutMs() * 2;
        Future<SimulationResultDto> future;
        try {
            future = syncSimulationExecutor.submit(() ->
                    doSimulate(userId, input.devices(), input.rules(), input.steps(), input.attack(),
                            input.attackBudget(), input.enablePrivacy(), input.request(), input.deviceSmvMap(),
                            input.modelSnapshot(), tempModelContext));
        } catch (RejectedExecutionException e) {
            log.warn("Simulation request rejected: executor is saturated ({})", syncSimulationExecutorSnapshot());
            throw new ServiceUnavailableException("Simulation service is busy, please retry later", e);
        }

        try {
            SimulationResultDto result = future.get(timeoutMs, TimeUnit.MILLISECONDS);
            if (result == null || result.getStates() == null || result.getStates().isEmpty()) {
                throw SimulationExecutionException.fromResult(result);
            }
            return result;
        } catch (TimeoutException e) {
            future.cancel(true);
            purgeCancelledSyncTasks();
            log.warn("Simulation timed out after {}ms", timeoutMs);
            throw SimulationExecutionException.timedOut();
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            if (cause instanceof ServiceUnavailableException sue) throw sue;
            if (cause instanceof SmvGenerationException sge) throw sge;
            if (cause instanceof SimulationExecutionException see) throw see;
            log.error("Simulation failed", cause);
            throw new InternalServerException("Simulation failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            future.cancel(true);
            purgeCancelledSyncTasks();
            Thread.currentThread().interrupt();
            throw SimulationExecutionException.interrupted();
        }
    }

    private SimulationInput validateAndNormalize(Long userId, SimulationRequestDto request) {
        return validateAndNormalize(userId, request, null);
    }

    private SimulationInput validateAndNormalize(
            Long userId,
            SimulationRequestDto request,
            Map<String, DeviceManifest> suppliedTemplateManifests) {
        if (request == null) {
            throw new ValidationException("request", "Simulation request cannot be null");
        }
        if (request.getAttackScenario() != null && request.hasLegacyAttackFields()) {
            throw new ValidationException("attackScenario",
                    "Use attackScenario only; it cannot be combined with legacy isAttack/attackBudget fields");
        }
        AttackScenarioDto attackScenario = AttackScenarioValidator.canonicalizeForSimulation(
                request.resolvedAttackScenario());
        SimulationRequestDto snapshot = snapshotRequest(request, attackScenario);
        List<DeviceVerificationDto> devices = copyRequiredList(
                snapshot.getDevices(), "devices", "Devices list cannot be empty");
        List<RuleDto> rules = copyOptionalList(snapshot.getRules(), "rules");
        List<BoardEnvironmentVariableDto> environmentVariables = copyOptionalList(
                snapshot.getEnvironmentVariables(), "environmentVariables");
        int steps = snapshot.getSteps();
        if (steps < 1 || steps > 100) {
            throw new ValidationException("steps", "Steps must be between 1 and 100");
        }
        int effectiveAttackBudget = attackScenario.effectiveBudget();

        snapshot.setDevices(devices);
        snapshot.setRules(rules);
        snapshot.setEnvironmentVariables(environmentVariables);
        snapshot.setSteps(steps);
        snapshot.setAttackScenario(attackScenario);

        Map<String, String> errors = NusmvRequestValidator.newErrors();
        NusmvRequestValidator.validateDevices(devices, errors);
        NusmvRequestValidator.validateRules(rules, devices, errors);
        ModelBoundaryInput modelInput = validateModelSemantics(
                userId, devices, rules, environmentVariables, snapshot.isAttack(),
                suppliedTemplateManifests, errors);
        snapshot.setEnvironmentVariables(modelInput.environmentVariables());
        NusmvRequestValidator.throwIfErrors(errors);

        AttackSurface attackSurface = modelInput.attackSurface();
        AttackScenarioValidator.validateAgainstSurface(attackScenario, attackSurface, rules);

        return new SimulationInput(modelInput.devices(), rules, steps, snapshot.isAttack(), effectiveAttackBudget,
                snapshot.isEnablePrivacy(), attackSurface.deviceCount(), attackSurface.automationLinkCount(),
                attackSurface.falsifiableReadingDeviceCount(), attackScenario, snapshot, modelInput.deviceSmvMap(),
                modelInput.templateManifests(), modelInput.modelSnapshot(), attackSurface);
    }

    private ModelBoundaryInput validateModelSemantics(Long userId,
                                                      List<DeviceVerificationDto> devices,
                                                      List<RuleDto> rules,
                                                      List<BoardEnvironmentVariableDto> environmentVariables,
                                                      boolean isAttack,
                                                      Map<String, DeviceManifest> suppliedTemplateManifests,
                                                      Map<String, String> errors) {
        if (!errors.isEmpty()) {
            return new ModelBoundaryInput(devices, environmentVariables, new AttackSurface(Set.of(), 0, 0),
                    Map.of(), Map.of(), null);
        }
        try {
            SmvGenerator.CapturedDeviceModel capturedDeviceModel = suppliedTemplateManifests == null
                    ? smvGenerator.captureDeviceModel(userId, devices)
                    : smvGenerator.captureDeviceModelFromTemplateSnapshots(
                            devices, suppliedTemplateManifests);
            Map<String, DeviceSmvData> deviceSmvMap = capturedDeviceModel.deviceSmvMap();
            LocalDateTime capturedAt = LocalDateTime.now();
            NusmvRequestValidator.validateDeviceSemantics(devices, deviceSmvMap, errors);
            NusmvRequestValidator.validateEnvironmentVariableOverrides(
                    environmentVariables, deviceSmvMap, errors);
            List<BoardEnvironmentVariableDto> mergedEnvironmentVariables =
                    NusmvEnvironmentPool.mergeWithDefaults(environmentVariables, deviceSmvMap);
            NusmvRequestValidator.validateEnvironmentVariables(mergedEnvironmentVariables, deviceSmvMap, errors);
            NusmvRequestValidator.validateMainNamespace(devices, rules, deviceSmvMap, isAttack, errors);
            NusmvRequestValidator.validateRuleSemantics(rules, deviceSmvMap, errors);
            NusmvRequestValidator.validateAttackHasModeledEffect(isAttack, rules, deviceSmvMap, errors);
            AttackSurface attackSurface = AttackSurface.analyze(rules, deviceSmvMap);
            if (!errors.isEmpty()) {
                return new ModelBoundaryInput(devices, mergedEnvironmentVariables, attackSurface,
                        Map.of(), capturedDeviceModel.templateManifests(), null);
            }
            List<DeviceVerificationDto> expandedDevices = NusmvEnvironmentPool.expandDevices(
                    devices, mergedEnvironmentVariables, deviceSmvMap);
            Map<String, DeviceSmvData> expandedDeviceSmvMap =
                    smvGenerator.buildDeviceSmvMapFromTemplateSnapshots(
                            expandedDevices, capturedDeviceModel.templateManifests());
            ModelRunSnapshotDto modelSnapshot = ModelRunSnapshotDto.captured(
                    capturedAt,
                    expandedDevices.size(),
                    rules != null ? rules.size() : 0,
                    0,
                    mergedEnvironmentVariables.size(),
                    capturedDeviceModel.templateManifests().size());
            return new ModelBoundaryInput(expandedDevices, mergedEnvironmentVariables, attackSurface,
                    expandedDeviceSmvMap, capturedDeviceModel.templateManifests(), modelSnapshot);
        } catch (SmvGenerationException e) {
            errors.putIfAbsent("devices", e.getMessage());
            return new ModelBoundaryInput(devices, environmentVariables, new AttackSurface(Set.of(), 0, 0),
                    Map.of(), Map.of(), null);
        }
    }

    private SimulationRequestDto snapshotRequest(SimulationRequestDto request,
                                                 AttackScenarioDto attackScenario) {
        try {
            SimulationRequestDto snapshot = objectMapper.convertValue(request, SimulationRequestDto.class);
            ModelRequestSnapshotSupport.preserveDeviceMetadata(
                    request.getDevices(), snapshot.getDevices());
            snapshot.setAttackScenario(attackScenario);
            return snapshot;
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
    Long createTask(Long userId, int requestedSteps,
                    boolean isAttack, int attackBudget, boolean enablePrivacy,
                    int devicePointCount, int linkPointCount,
                    int falsifiableReadingDeviceCount,
                    ModelRunSnapshotDto modelSnapshot) {
        return createTask(userId, requestedSteps, isAttack, attackBudget, enablePrivacy,
                devicePointCount, linkPointCount, falsifiableReadingDeviceCount, modelSnapshot,
                JsonUtils.toJson(ModelSemanticsDto.forRun(
                        isAttack, enablePrivacy, devicePointCount, linkPointCount,
                        falsifiableReadingDeviceCount)));
    }

    private Long createTask(Long userId, int requestedSteps,
                            boolean isAttack, int attackBudget, boolean enablePrivacy,
                            int devicePointCount, int linkPointCount,
                            int falsifiableReadingDeviceCount,
                            ModelRunSnapshotDto modelSnapshot,
                            String modelSemanticsJson) {
        return transactionTemplate.execute(status -> {
            requireActiveUserForPersistence(userId);
            requireChatExecutionLease();
            long storedTaskCount = storedSimulationRunCount(userId);
            if (storedTaskCount >= taskAdmissionLimits.getMaxStoredTasksPerUser()) {
                throw new AsyncTaskQuotaExceededException(
                        "simulation", AsyncTaskQuotaExceededException.QuotaType.STORED,
                        storedTaskCount, taskAdmissionLimits.getMaxStoredTasksPerUser());
            }
            long activeTaskCount = simulationTaskRepository.countByUserIdAndStatusIn(
                    userId, List.of(SimulationTaskPo.TaskStatus.PENDING, SimulationTaskPo.TaskStatus.RUNNING));
            if (activeTaskCount >= taskAdmissionLimits.getMaxActiveTasksPerUser()) {
                throw new AsyncTaskQuotaExceededException(
                        "simulation", AsyncTaskQuotaExceededException.QuotaType.ACTIVE,
                        activeTaskCount, taskAdmissionLimits.getMaxActiveTasksPerUser());
            }
            LocalDateTime createdAt = databaseNow();
            SimulationTaskPo task = SimulationTaskPo.builder()
                    .userId(userId)
                    .status(SimulationTaskPo.TaskStatus.PENDING)
                    .requestedSteps(requestedSteps)
                    .isAttack(isAttack)
                    .attackBudget(attackBudget)
                    .modeledDeviceAttackPointCount(devicePointCount)
                    .modeledFalsifiableReadingDeviceCount(falsifiableReadingDeviceCount)
                    .modeledAutomationLinkAttackPointCount(linkPointCount)
                    .enablePrivacy(enablePrivacy)
                    .modelSnapshotJson(JsonUtils.toJson(modelSnapshot))
                    .modelSemanticsJson(modelSemanticsJson)
                    .createdAt(createdAt)
                    .progress(0)
                    .progressStage(TaskProgressStage.QUEUED)
                    .workerId(workerId)
                    .leaseExpiresAt(createdAt.plus(TASK_LEASE_DURATION))
                    .build();
            SimulationTaskPo saved = simulationTaskRepository.save(Objects.requireNonNull(task));
            log.info("Created simulation task: {} for user: {}", saved.getId(), userId);
            return saved.getId();
        });
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
            input = validateAndNormalize(userId, request);
        } catch (ValidationException e) {
            failTaskById(requiredTaskId, e.getMessage());
            throw e;
        }
        try {
            persistTaskModelContext(requiredTaskId, input.attack(), input.attackBudget(), input.enablePrivacy(),
                    input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                    input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(),
                    JsonUtils.toJson(ModelSemanticsDto.forRun(
                            input.attackScenario(), input.enablePrivacy(), input.attackSurface())));
            enqueueSimulationTask(userId, requiredTaskId, input);
        } catch (TaskRejectedException e) {
            failTaskById(requiredTaskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later", e);
        }
    }

    @Override
    public Long submitSimulation(Long userId, SimulationRequestDto request) {
        return submitSimulationInput(userId, validateAndNormalize(userId, request));
    }

    @Override
    public Long submitSimulationWithTemplateSnapshot(
            Long userId,
            SimulationRequestDto request,
            Map<String, DeviceManifest> templateManifests) {
        return submitSimulationInput(userId, validateAndNormalize(userId, request, templateManifests));
    }

    private Long submitSimulationInput(Long userId, SimulationInput input) {
        Long taskId = createTask(userId, input.steps(),
                input.attack(), input.attackBudget(), input.enablePrivacy(),
                input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(),
                JsonUtils.toJson(ModelSemanticsDto.forRun(
                        input.attackScenario(), input.enablePrivacy(), input.attackSurface())));
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
        LocalSimulationExecution execution =
                new LocalSimulationExecution(userId, requiredTaskId, requiredInput);
        if (localExecutions.putIfAbsent(requiredTaskId, execution) != null) {
            throw new IllegalStateException("Duplicate local simulation task execution " + requiredTaskId);
        }
        try {
            simulationTaskExecutor.execute(execution.futureTask);
        } catch (RuntimeException e) {
            execution.requestStop();
            throw e;
        }
    }

    private LocalDateTime databaseNow() {
        return Objects.requireNonNull(
                simulationTaskRepository.currentDatabaseTime(),
                "Database current timestamp must not be null");
    }

    private void purgeCancelledSimulationTasks() {
        try {
            ThreadPoolExecutor executor = simulationTaskExecutor.getThreadPoolExecutor();
            if (executor != null) executor.purge();
        } catch (RuntimeException e) {
            log.warn("Could not purge cancelled simulation tasks from the local executor queue", e);
        }
    }

    private void persistTaskModelContext(Long taskId,
                                         boolean isAttack,
                                         int attackBudget,
                                         boolean enablePrivacy,
                                         int devicePointCount,
                                         int linkPointCount,
                                         int falsifiableReadingDeviceCount,
                                         ModelRunSnapshotDto modelSnapshot,
                                         String modelSemanticsJson) {
        simulationTaskRepository.updateModelContext(
                taskId, isAttack, isAttack ? attackBudget : 0, enablePrivacy,
                devicePointCount, falsifiableReadingDeviceCount, linkPointCount,
                JsonUtils.toJson(modelSnapshot), modelSemanticsJson);
    }

    private Long requireTaskId(Long taskId) {
        if (taskId == null) {
            throw new ValidationException("taskId", "Task id cannot be null");
        }
        return taskId;
    }

    private void runSimulationTask(Long userId, Long taskId, SimulationInput input) {
        String requestJson = buildRequestSnapshot(input.request());
        String templateSnapshotsJson = JsonUtils.toJson(input.templateManifests());

        registerRunningTask(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, TaskProgressStage.STARTING);

        SimulationTaskPo task = null;
        try {
            // Check in-memory cancellation marker (fast path for same-instance cancellation).
            if (isTaskCancelled(taskId)) {
                return;
            }

            // Atomically transition PENDING → RUNNING to close the cancel-vs-start race window.
            // A plain findById + save was vulnerable to TOCTOU: a concurrent cancel could set
            // CANCELLED between the read and the save, and the save would overwrite it back to RUNNING.
            LocalDateTime currentTime = databaseNow();
            LocalDateTime startedAt = currentTime;
            String startCheckLogs = serializeCheckLogs(List.of("Task started"));
            int updated = simulationTaskRepository.startTaskIfStillPending(
                    taskId,
                    SimulationTaskPo.TaskStatus.RUNNING,
                    startedAt, 0, startCheckLogs,
                    SimulationTaskPo.TaskStatus.PENDING,
                    workerId,
                    currentTime,
                    currentTime.plus(TASK_LEASE_DURATION));
            if (updated == 0) {
                log.info("Simulation task {} is no longer PENDING (cancelled or already started), aborting", taskId);
                return;
            }
            LocalSimulationExecution localExecution = localExecutions.get(taskId);
            if (localExecution != null) localExecution.leaseConfirmation.confirm();

            // Load entity for subsequent use (failTask/completeTask only need id and startedAt).
            task = simulationTaskRepository.findById(Objects.requireNonNull(taskId)).orElse(null);
            if (task == null) {
                log.error("Simulation task not found after atomic start: {}", taskId);
                return;
            }

            updateTaskProgress(taskId, 20, TaskProgressStage.RUNNING_SIMULATION);
            SimulationResultDto result = doSimulate(userId, input.devices(), input.rules(), input.steps(),
                    input.attack(), input.attackBudget(), input.enablePrivacy(), input.request(),
                    input.deviceSmvMap(), input.modelSnapshot(), SmvGenerator.TempModelContext.task(taskId));

            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }

            if (result.getStates() == null || result.getStates().isEmpty()) {
                failTask(task, deriveFailureMessage(result), result.getLogs());
                return;
            }

            updateTaskProgress(taskId, 90, TaskProgressStage.PERSISTING_RESULT);
            boolean completed = completeTaskAndSaveTrace(task, userId, result, requestJson, templateSnapshotsJson);
            if (!completed && !isCompletionCancelled(taskId)) {
                failTask(task,
                        "RESULT_PERSISTENCE_FAILED: Simulation finished, but its trajectory could not be saved.",
                        result.getLogs());
            }

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
            try {
                simulationTaskRepository.releaseOwnedActiveLease(
                        taskId, workerId, databaseNow().minusSeconds(1), ACTIVE_STATUSES);
            } catch (RuntimeException e) {
                log.warn("Could not release simulation task {} lease; it will expire naturally", taskId, e);
            }
        }
    }

    private record SimulationInput(List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules,
                                   int steps,
                                   boolean attack,
                                   int attackBudget,
                                   boolean enablePrivacy,
                                   int modeledDeviceAttackPointCount,
                                   int modeledAutomationLinkAttackPointCount,
                                   int modeledFalsifiableReadingDeviceCount,
                                   AttackScenarioDto attackScenario,
                                   SimulationRequestDto request,
                                   Map<String, DeviceSmvData> deviceSmvMap,
                                   Map<String, DeviceManifest> templateManifests,
                                   ModelRunSnapshotDto modelSnapshot,
                                   AttackSurface attackSurface) {}

    private record ModelBoundaryInput(List<DeviceVerificationDto> devices,
                                       List<BoardEnvironmentVariableDto> environmentVariables,
                                       AttackSurface attackSurface,
                                       Map<String, DeviceSmvData> deviceSmvMap,
                                       Map<String, DeviceManifest> templateManifests,
                                       ModelRunSnapshotDto modelSnapshot) {}

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
                ? simulationTaskRepository.findByUserIdAndStatusNotOrderByCreatedAtDesc(
                        userId, SimulationTaskPo.TaskStatus.COMPLETED)
                : simulationTaskRepository.findByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDesc(
                        userId, SimulationTaskPo.TaskStatus.COMPLETED, normalizedExcludedIds);
        return simulationTaskMapper.toSummaryDtoList(
                tasks);
    }

    @Override
    @Transactional
    public void deleteTask(Long userId, Long taskId) {
        SimulationTaskPo task = simulationTaskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTask", taskId));
        if (task.getStatus() == SimulationTaskPo.TaskStatus.PENDING
                || task.getStatus() == SimulationTaskPo.TaskStatus.RUNNING) {
            throw new BadRequestException("An active simulation task must be cancelled before it can be removed");
        }
        if (task.getStatus() == SimulationTaskPo.TaskStatus.COMPLETED) {
            throw new BadRequestException("Completed simulation results must be removed from run history");
        }
        simulationTaskRepository.delete(Objects.requireNonNull(task));
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
    public TaskCancellationResultDto cancelTask(Long userId, Long taskId) {
        chatExecutionLeaseGuard.requireCurrentExecutionLeaseAndLock();
        return super.cancelTask(userId, taskId);
    }

    @Override
    public SimulationTraceDto simulateAndSave(Long userId, SimulationRequestDto request) {
        return formalOperationAdmission.execute(userId, () -> simulateAndSaveWithoutAdmission(userId, request));
    }

    private SimulationTraceDto simulateAndSaveWithoutAdmission(Long userId, SimulationRequestDto request) {
        SimulationInput input = validateAndNormalize(userId, request);
        requireSimulationRunStorageCapacity(userId);
        SimulationResultDto result = simulateInput(userId, input, SmvGenerator.TempModelContext.savedTrace());

        if (result.getStates() == null || result.getStates().isEmpty()) {
            throw new InternalServerException("Simulation produced no states, nothing to save");
        }

        SimulationTracePo saved;
        try {
            saved = transactionTemplate.execute(status -> {
                formalOperationAdmission.registerCurrentLeaseCommitFence();
                return persistSimulationTrace(
                        userId, result, buildRequestSnapshot(input.request()),
                        JsonUtils.toJson(input.templateManifests()));
            });
        } catch (AsyncTaskQuotaExceededException e) {
            log.info("Simulation completed but run history is full for user {}", userId);
            return unsavedSimulationTrace(result, RunPersistenceDto.failed(e.getReasonCode()));
        } catch (RuntimeException e) {
            log.error("Simulation completed but its history persistence outcome is unknown for user {}", userId, e);
            return unsavedSimulationTrace(result, RunPersistenceDto.outcomeUnknown(
                    "RUN_HISTORY_SAVE_OUTCOME_UNKNOWN"));
        }
        if (saved == null || saved.getId() == null) {
            return unsavedSimulationTrace(result, RunPersistenceDto.failed("RUN_HISTORY_SAVE_FAILED"));
        }
        log.info("Saved simulation trace: id={}, userId={}, steps={}", saved.getId(), userId, saved.getSteps());
        SimulationTraceDto dto = simulationTraceMapper.toDto(saved);
        dto.setHistoryPersistence(RunPersistenceDto.saved(saved.getId()));
        return dto;
    }

    private SimulationTraceDto unsavedSimulationTrace(
            SimulationResultDto result, RunPersistenceDto persistence) {
        return SimulationTraceDto.builder()
                .requestedSteps(result.getRequestedSteps())
                .steps(result.getSteps())
                .modelComplete(result.isModelComplete())
                .disabledRuleCount(result.getDisabledRuleCount())
                .generationIssues(result.getGenerationIssues())
                .states(result.getStates())
                .logs(result.getLogs())
                .nusmvOutput(result.getNusmvOutput())
                .attack(result.getIsAttack())
                .attackBudget(result.getAttackBudget())
                .enablePrivacy(result.isEnablePrivacy())
                .modelSemantics(result.getModelSemantics())
                .modelSnapshot(result.getModelSnapshot())
                .historyPersistence(persistence)
                .createdAt(LocalDateTime.now())
                .build();
    }

    @Override
    @Transactional(readOnly = true)
    public List<SimulationTraceSummaryDto> getUserSimulations(Long userId) {
        return simulationTraceMapper.toSummaryProjectionDtoList(
                simulationTraceRepository.findByUserIdOrderByCreatedAtDescIdDesc(
                        userId, PageRequest.of(0, taskAdmissionLimits.getMaxStoredTasksPerUser())));
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
        requireChatExecutionLease();
        SimulationTracePo po = simulationTraceRepository.findByIdAndUserId(id, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTrace", id));
        simulationTaskRepository.deleteByUserIdAndSimulationTraceId(userId, id);
        simulationTraceRepository.delete(Objects.requireNonNull(po));
    }

    private SimulationResultDto doSimulate(Long userId,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           int steps,
                                           boolean isAttack,
                                           int attackBudget,
                                           boolean enablePrivacy,
                                           SimulationRequestDto request,
                                           Map<String, DeviceSmvData> resolvedDeviceSmvMap,
                                           ModelRunSnapshotDto modelSnapshot,
                                           SmvGenerator.TempModelContext tempModelContext) {
        List<String> logs = new ArrayList<>();
        File smvFile = null;
        SimulationResultDto finalResult = null;
        AttackSurface attackSurface = new AttackSurface(Set.of(), rules != null ? rules.size() : 0, 0);
        int disabledRuleCount = 0;
        List<ModelGenerationIssueDto> generationIssues = List.of();
        boolean generationCompleted = false;
        String requestJson = buildRequestSnapshot(request);

        try {
            logs.add("Generating NuSMV model (simulation mode)...");
            SmvGenerator.GenerateResult genResult = generateResolvedModel(
                    userId, devices, request.getEnvironmentVariables(), rules, List.of(),
                    request.resolvedAttackScenario(), enablePrivacy, SmvGenerator.GeneratePurpose.SIMULATION,
                    tempModelContext, resolvedDeviceSmvMap);
            smvFile = genResult.smvFile();
            Map<String, DeviceSmvData> deviceSmvMap = genResult.deviceSmvMap();
            attackSurface = AttackSurface.analyze(rules, deviceSmvMap);
            disabledRuleCount = genResult.disabledRuleCount();
            generationIssues = genResult.generationIssues() != null ? genResult.generationIssues() : List.of();
            generationCompleted = true;
            if (genResult.generationWarnings() != null) {
                logs.addAll(genResult.generationWarnings());
            }

            if (smvFile == null || !smvFile.exists()) {
                logs.add("Failed to generate NuSMV model file");
                finalResult = SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
                return finalResult;
            }
            logs.add("Model generated: " + smvFile.getName());
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
                    simOutput.getTraceText(), deviceSmvMap, rules);
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
                finalResult.setIsAttack(isAttack);
                finalResult.setAttackBudget(isAttack ? attackBudget : 0);
                finalResult.setEnablePrivacy(enablePrivacy);
                finalResult.setModelSemantics(ModelSemanticsDto.forRun(
                        request.resolvedAttackScenario(), enablePrivacy, attackSurface));
                finalResult.setModelSnapshot(modelSnapshot);
                finalResult.setDisabledRuleCount(disabledRuleCount);
                finalResult.setModelComplete(generationCompleted && disabledRuleCount == 0);
                finalResult.setGenerationIssues(generationIssues);
                saveResultJson(smvFile, finalResult);
            }
            cleanupTempFile(smvFile);
        }
    }

    private boolean completeTask(SimulationTaskPo task, Long simulationTraceId, int steps, List<String> logs,
                                 List<ModelGenerationIssueDto> generationIssues) {
        if (task == null) return false;
        try {
            simulationTaskRepository.findByIdForUpdate(task.getId());
            LocalDateTime completedAt = databaseNow();
            Long processingTimeMs = task.getStartedAt() != null
                    ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
            String checkLogsJson = serializeCheckLogs(logs);
            String generationIssuesJson = JsonUtils.toJsonOrEmpty(generationIssues);
            int updated = simulationTaskRepository.completeTaskIfRunning(
                    task.getId(),
                    SimulationTaskPo.TaskStatus.COMPLETED,
                    completedAt, steps, simulationTraceId,
                    null, checkLogsJson, generationIssuesJson, processingTimeMs,
                    SimulationTaskPo.TaskStatus.RUNNING,
                    workerId, completedAt);
            if (updated == 0) {
                log.info("Simulation task {} was not RUNNING, no longer owned, or already terminal; skipping completion",
                        task.getId());
                return false;
            }
            return true;
        } catch (Exception e) {
            log.error("Failed to complete simulation task: {}", task.getId(), e);
            return false;
        }
    }

    private void failTask(SimulationTaskPo task, String errorMessage, List<String> logs) {
        if (task == null) return;
        try {
            transactionTemplate.executeWithoutResult(status -> {
                simulationTaskRepository.findByIdForUpdate(task.getId());
                LocalDateTime completedAt = databaseNow();
                Long processingTimeMs = task.getStartedAt() != null
                        ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
                String checkLogsJson = serializeCheckLogs(
                        logs == null || logs.isEmpty() ? List.of(errorMessage) : logs);
                int updated = simulationTaskRepository.failTaskIfActive(
                        task.getId(),
                        SimulationTaskPo.TaskStatus.FAILED,
                        completedAt, errorMessage,
                        checkLogsJson, processingTimeMs,
                        List.of(SimulationTaskPo.TaskStatus.PENDING,
                                SimulationTaskPo.TaskStatus.RUNNING),
                        workerId, completedAt);
                if (updated == 0) {
                    log.info("Simulation task {} was no longer active or owned; skipping fail", task.getId());
                }
            });
        } catch (Exception e) {
            log.error("Failed to mark simulation task as failed: {}", task.getId(), e);
        }
    }

    private SimulationTracePo persistSimulationTrace(Long userId, SimulationResultDto result,
                                                     String requestJson, String templateSnapshotsJson) {
        requireActiveUserForPersistence(userId);
        enforceSimulationRunStorageCapacity(userId);
        return persistSimulationTraceForActiveUser(userId, result, requestJson, templateSnapshotsJson);
    }

    private void requireSimulationRunStorageCapacity(Long userId) {
        transactionTemplate.executeWithoutResult(status -> {
            requireActiveUserForPersistence(userId);
            requireChatExecutionLease();
            enforceSimulationRunStorageCapacity(userId);
        });
    }

    private void enforceSimulationRunStorageCapacity(Long userId) {
        long storedRunCount = storedSimulationRunCount(userId);
        if (storedRunCount >= taskAdmissionLimits.getMaxStoredTasksPerUser()) {
            throw new AsyncTaskQuotaExceededException(
                    "simulation", AsyncTaskQuotaExceededException.QuotaType.STORED,
                    storedRunCount, taskAdmissionLimits.getMaxStoredTasksPerUser());
        }
    }

    private long storedSimulationRunCount(Long userId) {
        return Math.addExact(
                simulationTaskRepository.countByUserId(userId),
                simulationTraceRepository.countStandaloneByUserId(userId));
    }

    private SimulationTracePo persistSimulationTraceForActiveUser(Long userId, SimulationResultDto result,
                                                                  String requestJson, String templateSnapshotsJson) {
        ModelSemanticsDto semantics = result.getModelSemantics();
        SimulationTracePo po = SimulationTracePo.builder()
                .userId(userId)
                .requestedSteps(result.getRequestedSteps())
                .steps(result.getSteps())
                .statesJson(JsonUtils.toJson(result.getStates()))
                .stateCount(result.getStates().size())
                .logsJson(JsonUtils.toJsonOrEmpty(result.getLogs()))
                .generationIssuesJson(JsonUtils.toJsonOrEmpty(result.getGenerationIssues()))
                .nusmvOutput(result.getNusmvOutput())
                .requestJson(requestJson)
                .templateSnapshotsJson(templateSnapshotsJson)
                .modelSnapshotJson(JsonUtils.toJson(result.getModelSnapshot()))
                .modelSemanticsJson(JsonUtils.toJson(result.getModelSemantics()))
                .isAttack(result.getIsAttack())
                .attackBudget(Boolean.TRUE.equals(result.getIsAttack()) ? result.getAttackBudget() : 0)
                .enablePrivacy(result.isEnablePrivacy())
                .modeledDeviceAttackPointCount(semantics != null
                        ? semantics.getModeledDeviceAttackPointCount() : null)
                .modeledFalsifiableReadingDeviceCount(semantics != null
                        ? semantics.getModeledFalsifiableReadingDeviceCount() : null)
                .modeledAutomationLinkAttackPointCount(semantics != null
                        ? semantics.getModeledAutomationLinkAttackPointCount() : null)
                .build();
        return simulationTraceRepository.save(Objects.requireNonNull(po));
    }

    private boolean completeTaskAndSaveTrace(SimulationTaskPo task,
                                             Long userId,
                                             SimulationResultDto result,
                                             String requestJson,
                                             String templateSnapshotsJson) {
        if (!userRepository.existsById(userId)) {
            log.info("User {} no longer exists, skipping simulation task completion/persistence", userId);
            return false;
        }
        if (isCompletionCancelled(task.getId())) {
            log.info("Simulation task {} was cancelled before trace persistence", task.getId());
            return false;
        }
        if (transactionTemplate == null) {
            throw new IllegalStateException("transactionTemplate is required to complete simulation with a trace");
        }
        return Boolean.TRUE.equals(transactionTemplate.execute(status -> {
            if (!userRepository.existsById(userId)) {
                log.info("User {} was deleted before simulation trace persistence, skipping simulation result", userId);
                status.setRollbackOnly();
                return false;
            }
            if (isCompletionCancelled(task.getId())) {
                log.info("Simulation task {} was cancelled before trace persistence", task.getId());
                status.setRollbackOnly();
                return false;
            }
            requireActiveUserForPersistence(userId);
            simulationTaskRepository.findByIdForUpdate(task.getId());
            SimulationTracePo savedTrace = persistSimulationTraceForActiveUser(
                    userId, result, requestJson, templateSnapshotsJson);
            if (isCompletionCancelled(task.getId())) {
                log.info("Simulation task {} was cancelled after trace persistence but before completion; rolling back trace", task.getId());
                status.setRollbackOnly();
                return false;
            }
            boolean completed = completeTask(task, savedTrace.getId(), result.getSteps(), result.getLogs(),
                    result.getGenerationIssues());
            if (!completed) {
                status.setRollbackOnly();
            }
            return completed;
        }));
    }

    private boolean isCompletionCancelled(Long taskId) {
        return taskId != null && (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted());
    }

    private void requireActiveUserForPersistence(Long userId) {
        if (userId == null) {
            throw new ValidationException("userId", "User id cannot be null");
        }
        if (userRepository.findByIdForUpdate(userId).isEmpty()) {
            throw ResourceNotFoundException.user(userId);
        }
    }

    private String buildRequestSnapshot(List<DeviceVerificationDto> devices,
                                        List<RuleDto> rules,
                                        int steps,
                                        boolean isAttack,
                                        int attackBudget,
                                        boolean enablePrivacy) {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setDevices(devices);
        request.setRules(rules != null ? rules : List.of());
        request.setSteps(steps);
        request.setAttack(isAttack);
        request.setAttackBudget(attackBudget);
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
            byte[] payload = objectMapper.writerWithDefaultPrettyPrinter().writeValueAsBytes(wrapped);
            java.nio.file.Files.write(jsonFile.toPath(), payload);
            log.debug("Simulation result JSON saved to: {}", jsonFile.getAbsolutePath());
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
            log.debug("Simulation request JSON saved to: {}", jsonFile.getAbsolutePath());
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

    private SmvGenerator.GenerateResult generateResolvedModel(
            Long userId,
            List<DeviceVerificationDto> devices,
            List<BoardEnvironmentVariableDto> environmentVariables,
            List<RuleDto> rules,
            List<cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto> specs,
            AttackScenarioDto attackScenario,
            boolean enablePrivacy,
            SmvGenerator.GeneratePurpose purpose,
            SmvGenerator.TempModelContext tempModelContext,
            Map<String, DeviceSmvData> resolvedDeviceSmvMap) throws IOException {
        AttackScenarioDto scenario = attackScenario != null ? attackScenario : AttackScenarioDto.none();
        if (scenario.getMode() == AttackScenarioDto.Mode.EXACT_POINTS) {
            return smvGenerator.generateWithResolvedDeviceModel(
                    userId, devices, environmentVariables, rules, specs, scenario,
                    enablePrivacy, purpose, tempModelContext, resolvedDeviceSmvMap);
        }
        return smvGenerator.generateWithResolvedDeviceModel(
                userId, devices, environmentVariables, rules, specs,
                scenario.isEnabled(), scenario.effectiveBudget(), enablePrivacy,
                purpose, tempModelContext, resolvedDeviceSmvMap);
    }

    private void cleanupTempFile(File file) {
        // The scheduled artifact cleaner bounds retained model/request/output/result directories.
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
    protected LocalDateTime currentTaskTime() {
        return databaseNow();
    }

    @Override
    protected int atomicUpdateProgress(Long taskId, int progress, TaskProgressStage stage) {
        return simulationTaskRepository.updateProgressIfActive(
                taskId, progress, stage, workerId, databaseNow());
    }

    @Override
    protected LocalExecutionStopResult stopAdditionalLocalExecution(Long taskId) {
        LocalSimulationExecution execution = localExecutions.get(taskId);
        return execution == null ? LocalExecutionStopResult.NONE : execution.requestStop();
    }

    private enum LocalExecutionState {
        QUEUED,
        RUNNING,
        CANCELLED_BEFORE_START,
        FINISHED
    }

    private final class LocalSimulationExecution implements Runnable {
        private final Long userId;
        private final Long taskId;
        private final SimulationInput input;
        private final AtomicReference<LocalExecutionState> state =
                new AtomicReference<>(LocalExecutionState.QUEUED);
        private final LeaseConfirmation leaseConfirmation = new LeaseConfirmation();
        private final FutureTask<Void> futureTask = new FutureTask<>(this, null);

        private LocalSimulationExecution(Long userId, Long taskId, SimulationInput input) {
            this.userId = userId;
            this.taskId = taskId;
            this.input = input;
        }

        @Override
        public void run() {
            if (!state.compareAndSet(LocalExecutionState.QUEUED, LocalExecutionState.RUNNING)) {
                return;
            }
            try {
                runSimulationTask(userId, taskId, input);
            } finally {
                removeCancelledMark(taskId);
                state.set(LocalExecutionState.FINISHED);
                localExecutions.remove(taskId, this);
            }
        }

        private LocalExecutionStopResult requestStop() {
            while (true) {
                LocalExecutionState current = state.get();
                if (current == LocalExecutionState.QUEUED) {
                    if (!state.compareAndSet(
                            LocalExecutionState.QUEUED,
                            LocalExecutionState.CANCELLED_BEFORE_START)) {
                        continue;
                    }
                    futureTask.cancel(false);
                    purgeCancelledSimulationTasks();
                    localExecutions.remove(taskId, this);
                    return LocalExecutionStopResult.STOPPED_BEFORE_START;
                }
                if (current == LocalExecutionState.RUNNING) {
                    futureTask.cancel(true);
                    return LocalExecutionStopResult.STOP_REQUESTED;
                }
                return LocalExecutionStopResult.NONE;
            }
        }
    }
}
