package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.fuzz.FuzzEngine;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzEngineConfig;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzEngineInput;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzEngineOutcome;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzEngineResult;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzFinding;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzInputEvent;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzInputEventSource;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzLimitationContract;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzMetadataPolicy;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzPaperDomainPreviewer;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzSpecEligibility;
import cn.edu.nju.Iot_Verify.configure.FuzzAdmissionConfig;
import cn.edu.nju.Iot_Verify.configure.ThreadPoolConfig;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzEligibilityDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzFindingDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzIneligibleSpecDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzInputEventDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDomainPreviewDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDomainPreviewRequestDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRequestDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunSummaryDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzTaskDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzWorkloadPreviewDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzWorkloadPreviewRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.FuzzTaskQuotaExceededException;
import cn.edu.nju.Iot_Verify.exception.FuzzTaskStorageQuotaExceededException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.FuzzFindingPo;
import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;
import cn.edu.nju.Iot_Verify.repository.FuzzFindingRepository;
import cn.edu.nju.Iot_Verify.repository.FuzzTaskRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzFindingSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskProgressProjection;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskSummaryProjection;
import cn.edu.nju.Iot_Verify.service.FuzzService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.util.mapper.FuzzMapper;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.MapperFeature;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.ObjectWriter;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.databind.node.ObjectNode;
import jakarta.annotation.PostConstruct;
import jakarta.annotation.PreDestroy;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.data.domain.PageRequest;
import org.springframework.data.domain.Pageable;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.time.LocalDateTime;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.Semaphore;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

@Slf4j
@Service
public class FuzzServiceImpl extends AbstractAsyncTaskService<FuzzTaskPo> implements FuzzService {

    private static final long CANCELLATION_DB_POLL_NANOS = 250_000_000L;
    private static final Duration TASK_LEASE_DURATION = Duration.ofMinutes(2);
    private static final long LEASE_MAINTENANCE_SECONDS = 10L;
    private static final long MAX_EFFECTIVE_WORK = 12_500_000L;
    private static final long MAX_MODEL_STRUCTURE_UNITS = 10_000L;
    private static final int MAX_FUZZ_COLLECTION_ITEMS = 1_000;
    private static final long MAX_MODEL_INPUT_SNAPSHOT_BYTES = 8L * 1024 * 1024;
    private static final long MAX_FINDING_EVIDENCE_BYTES = 4L * 1024 * 1024;
    private static final long MAX_RUN_EVIDENCE_BYTES = 16L * 1024 * 1024;
    static final long MAX_RUN_METADATA_BYTES = FuzzMetadataPolicy.MAX_RUN_METADATA_BYTES;
    static final int MAX_ELIGIBILITY_LABEL_CHARS = FuzzMetadataPolicy.MAX_ELIGIBILITY_LABEL_CHARS;
    static final int MAX_ELIGIBILITY_REASON_CHARS = FuzzMetadataPolicy.MAX_ELIGIBILITY_REASON_CHARS;
    private static final int MAX_STABLE_CODE_CHARS = FuzzMetadataPolicy.MAX_STABLE_CODE_CHARS;
    private static final Pattern STABLE_CODE = Pattern.compile("^[A-Z][A-Z0-9_]*$");
    private static final Pattern MODEL_FINGERPRINT = Pattern.compile("^[0-9a-f]{64}$");
    private static final List<FuzzTaskPo.TaskStatus> ACTIVE_STATUSES = List.of(
            FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING);

    private final FuzzTaskRepository taskRepository;
    private final FuzzFindingRepository findingRepository;
    private final UserRepository userRepository;
    private final BoardDataConverter boardDataConverter;
    private final FuzzEngine fuzzEngine;
    private final FuzzPaperDomainPreviewer fuzzPaperDomainPreviewer;
    private final FuzzMapper fuzzMapper;
    private final ThreadPoolTaskExecutor fuzzTaskExecutor;
    private final TransactionTemplate transactionTemplate;
    private final int maxActiveTasksPerUser;
    private final int maxStoredTasksPerUser;
    private final Semaphore globalTaskCapacity;
    private final ObjectWriter fingerprintWriter;
    private final ObjectMapper fingerprintMapper;
    private final String workerId = UUID.randomUUID().toString();
    private final ScheduledExecutorService leaseMaintenanceExecutor =
            Executors.newSingleThreadScheduledExecutor(runnable -> {
                Thread thread = new Thread(runnable, "fuzz-task-lease-maintenance");
                thread.setDaemon(true);
                return thread;
            });
    private final ConcurrentHashMap<Long, LocalFuzzExecution> localExecutions =
            new ConcurrentHashMap<>();

    public FuzzServiceImpl(FuzzTaskRepository taskRepository,
                           FuzzFindingRepository findingRepository,
                           UserRepository userRepository,
                           BoardDataConverter boardDataConverter,
                           FuzzEngine fuzzEngine,
                           FuzzPaperDomainPreviewer fuzzPaperDomainPreviewer,
                           FuzzMapper fuzzMapper,
                           @Qualifier("fuzzTaskExecutor") ThreadPoolTaskExecutor fuzzTaskExecutor,
                           FuzzAdmissionConfig fuzzAdmissionConfig,
                           ThreadPoolConfig threadPoolConfig,
                           TransactionTemplate transactionTemplate,
                           ObjectMapper objectMapper) {
        super(objectMapper, "Counterexample search task");
        this.taskRepository = taskRepository;
        this.findingRepository = findingRepository;
        this.userRepository = userRepository;
        this.boardDataConverter = boardDataConverter;
        this.fuzzEngine = fuzzEngine;
        this.fuzzPaperDomainPreviewer = fuzzPaperDomainPreviewer;
        this.fuzzMapper = fuzzMapper;
        this.fuzzTaskExecutor = fuzzTaskExecutor;
        this.transactionTemplate = transactionTemplate;
        this.maxActiveTasksPerUser = fuzzAdmissionConfig.getMaxActiveTasksPerUser();
        this.maxStoredTasksPerUser = fuzzAdmissionConfig.getMaxStoredTasksPerUser();
        this.globalTaskCapacity = new Semaphore(
                configuredTaskCapacity(threadPoolConfig.getFuzzTask()), true);
        this.fingerprintMapper = objectMapper.copy()
                .configure(MapperFeature.SORT_PROPERTIES_ALPHABETICALLY, true)
                .configure(SerializationFeature.ORDER_MAP_ENTRIES_BY_KEYS, true);
        this.fingerprintWriter = fingerprintMapper.writer();
    }

    private int configuredTaskCapacity(ThreadPoolConfig.Pool pool) {
        return Math.toIntExact(Math.addExact(
                (long) pool.getMaxPoolSize(), (long) pool.getQueueCapacity()));
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
        try {
            LocalDateTime now = databaseNow();
            LocalDateTime renewedUntil = now.plus(TASK_LEASE_DURATION);
            for (LocalFuzzExecution execution : List.copyOf(localExecutions.values())) {
                int renewed = taskRepository.renewOwnedActiveLease(
                        execution.taskId, workerId, now, renewedUntil, ACTIVE_STATUSES);
                if (renewed == 0) {
                    execution.requestStop();
                }
            }
            int recovered = taskRepository.failExpiredActiveTasks(
                    FuzzTaskPo.TaskStatus.FAILED,
                    now,
                    "The counterexample search stopped before the task completed",
                    serializeCheckLogs(List.of(
                            "Counterexample search task lease expired before completion")),
                    ACTIVE_STATUSES,
                    now);
            if (recovered > 0) {
                log.warn("Recovered {} expired fuzz task lease(s)", recovered);
            }
        } catch (RuntimeException e) {
            log.warn("Could not maintain fuzz task leases; the next cycle will retry", e);
        }
    }

    @Override
    public FuzzPaperDomainPreviewDto previewPaperDomain(
            Long userId, FuzzPaperDomainPreviewRequestDto request) {
        if (request == null) {
            throw new ValidationException("request", "Random-state input preview request cannot be null");
        }
        int pathLength = requireRange(request.getPathLength(), 1, 50,
                "pathLength", "Path length must be between 1 and 50");
        ModelInputSnapshot snapshot = boardDataConverter.getModelInputSnapshot(userId);
        modelComplexityUnits(snapshot);
        serializeFrozenSnapshot(snapshot, "board");
        try {
            return fuzzPaperDomainPreviewer.preview(
                    snapshot, pathLength, paperDomainFingerprint(snapshot, pathLength));
        } catch (IllegalArgumentException exception) {
            throw new ValidationException("board",
                    "Random-state input range cannot be built from the current Board");
        }
    }

    @Override
    public FuzzWorkloadPreviewDto previewWorkload(
            Long userId, FuzzWorkloadPreviewRequestDto request) {
        if (request == null) {
            throw new ValidationException("request", "Workload preview request cannot be null");
        }
        int maxIterations = requireRange(request.getMaxIterations(), 1, 5_000,
                "maxIterations", "Maximum iterations must be between 1 and 5000");
        int pathLength = requireRange(request.getPathLength(), 1, 50,
                "pathLength", "Path length must be between 1 and 50");
        int populationSize = requireRange(request.getPopulationSize(), 1, 50,
                "populationSize", "Population size must be between 1 and 50");
        ModelInputSnapshot snapshot = boardDataConverter.getModelInputSnapshot(userId);
        long modelComplexity = modelComplexityUnits(snapshot);
        serializeFrozenSnapshot(snapshot, "board");
        long workload = effectiveWorkload(
                maxIterations, pathLength, populationSize, modelComplexity);
        return FuzzWorkloadPreviewDto.builder()
                .maxIterations(maxIterations)
                .pathLength(pathLength)
                .populationSize(populationSize)
                .modelComplexityUnits(modelComplexity)
                .estimatedWorkload(workload)
                .workloadLimit(MAX_EFFECTIVE_WORK)
                .accepted(workload <= MAX_EFFECTIVE_WORK)
                .build();
    }

    @Override
    public String getCurrentModelFingerprint(Long userId) {
        ModelInputSnapshot snapshot = boardDataConverter.getModelInputSnapshot(userId);
        modelComplexityUnits(snapshot);
        return modelFingerprint(snapshot);
    }

    @Override
    public Long submit(Long userId, FuzzRequestDto request) {
        NormalizedRequest normalized = validateAndNormalize(request);
        SubmissionCapacityPermit capacityPermit = acquireSubmissionCapacity();
        LocalFuzzExecution localExecution = null;
        Long taskId = null;
        boolean executorAccepted = false;
        try {
            ModelInputSnapshot snapshot = boardDataConverter.getModelInputSnapshot(userId);
            modelComplexityUnits(snapshot);
            validateTargetSpecifications(normalized.targetSpecIds(), snapshot.specifications());
            validateEffectiveWorkload(normalized, snapshot);
            LocalDateTime capturedAt = LocalDateTime.now();
            ModelRunSnapshotDto modelSnapshot = ModelRunSnapshotDto.captured(
                    capturedAt,
                    snapshot.devices().size(),
                    snapshot.rules().size(),
                    snapshot.specifications().size(),
                    snapshot.environmentVariables().size(),
                    snapshot.templateManifests().size());
            modelSnapshot.setModelFingerprint(modelFingerprint(snapshot));
            taskId = createTask(userId, normalized, snapshot, modelSnapshot);
            localExecution = new LocalFuzzExecution(taskId, userId, capacityPermit);
            LocalFuzzExecution existing = localExecutions.putIfAbsent(taskId, localExecution);
            if (existing != null) {
                throw new IllegalStateException("Duplicate local fuzz task execution " + taskId);
            }
            if (taskRepository.findStatusById(taskId)
                    .filter(status -> status == FuzzTaskPo.TaskStatus.PENDING)
                    .isEmpty()
                    || !localExecution.isQueued()) {
                localExecution.requestStop();
                return taskId;
            }
            try {
                fuzzTaskExecutor.execute(localExecution.futureTask);
                executorAccepted = true;
                localExecution.purgeIfCancelledAfterDispatch();
            } catch (TaskRejectedException e) {
                localExecution.requestStop();
                throw new ServiceUnavailableException(
                        "Counterexample search is busy, please retry later", e);
            }
            return taskId;
        } catch (RuntimeException e) {
            if (taskId != null && !executorAccepted) {
                cleanupUndispatchedTask(userId, taskId, e);
            }
            throw e;
        } finally {
            if (localExecution == null) {
                capacityPermit.release();
            } else if (!executorAccepted && localExecution.isQueued()) {
                localExecution.requestStop();
            }
        }
    }

    private Long createTask(Long userId,
                            NormalizedRequest request,
                            ModelInputSnapshot snapshot,
                            ModelRunSnapshotDto modelSnapshot) {
        return transactionTemplate.execute(status -> {
            requireActiveUserForPersistence(userId);
            long storedTaskCount = taskRepository.countByUserId(userId);
            if (storedTaskCount >= maxStoredTasksPerUser) {
                throw new FuzzTaskStorageQuotaExceededException(
                        storedTaskCount, maxStoredTasksPerUser);
            }
            long activeTaskCount = taskRepository.countByUserIdAndStatusIn(userId, ACTIVE_STATUSES);
            if (activeTaskCount >= maxActiveTasksPerUser) {
                throw new FuzzTaskQuotaExceededException(
                        activeTaskCount, maxActiveTasksPerUser);
            }
            if (request.explorationMode() == FuzzExplorationMode.PAPER_COMPATIBLE
                    && !paperDomainFingerprint(snapshot, request.pathLength())
                    .equals(request.paperDomainFingerprint())) {
                throw new ValidationException(
                        "paperDomainFingerprint",
                        "Board changed after the random-state input preview; refresh the preview and retry");
            }
            String modelInputSnapshotJson = serializeFrozenSnapshot(snapshot, "request");
            LocalDateTime createdAt = databaseNow();
            FuzzTaskPo task = FuzzTaskPo.builder()
                    .userId(userId)
                    .status(FuzzTaskPo.TaskStatus.PENDING)
                    .createdAt(createdAt)
                    .progress(0)
                    .progressStage(TaskProgressStage.QUEUED)
                    .targetSpecIdsJson(JsonUtils.toJson(request.targetSpecIds()))
                    .maxIterations(request.maxIterations())
                    .pathLength(request.pathLength())
                    .populationSize(request.populationSize())
                    .seed(request.seed())
                    .explorationMode(request.explorationMode())
                    .modelInputSnapshotJson(modelInputSnapshotJson)
                    .modelSnapshotJson(JsonUtils.toJson(modelSnapshot))
                    .findingCount(0)
                    .workerId(workerId)
                    .leaseExpiresAt(createdAt.plus(TASK_LEASE_DURATION))
                    .build();
            return taskRepository.save(Objects.requireNonNull(task)).getId();
        });
    }

    private SubmissionCapacityPermit acquireSubmissionCapacity() {
        if (!globalTaskCapacity.tryAcquire()) {
            throw new ServiceUnavailableException(
                    "Counterexample search is at task capacity; retry after an active task finishes");
        }
        return new SubmissionCapacityPermit(globalTaskCapacity);
    }

    private LocalDateTime databaseNow() {
        return Objects.requireNonNull(
                taskRepository.currentDatabaseTime(),
                "Database current timestamp must not be null");
    }

    private void purgeCancelledFuzzTasks() {
        try {
            ThreadPoolExecutor executor = fuzzTaskExecutor.getThreadPoolExecutor();
            if (executor != null) executor.purge();
        } catch (RuntimeException e) {
            log.warn("Could not purge cancelled fuzz tasks from the local executor queue", e);
        }
    }

    private void cleanupUndispatchedTask(Long userId, Long taskId, RuntimeException failure) {
        try {
            int deleted = taskRepository.deleteUndispatchedTask(
                    taskId, userId, workerId, FuzzTaskPo.TaskStatus.PENDING);
            boolean pendingRowRemains = deleted == 0
                    && taskRepository.findStatusById(taskId)
                    .filter(status -> status == FuzzTaskPo.TaskStatus.PENDING)
                    .isPresent();
            if (pendingRowRemains) {
                log.error("Could not remove fuzz task {} after failure before dispatch", taskId);
            }
        } catch (RuntimeException cleanupError) {
            failure.addSuppressed(cleanupError);
            log.error("Could not remove fuzz task {} after failure before dispatch",
                    taskId, cleanupError);
        }
    }

    private void runTask(Long userId, Long taskId) {
        FuzzTaskPo task = null;
        try {
            registerRunningTask(taskId, Thread.currentThread());
            updateTaskProgress(taskId, 0, TaskProgressStage.STARTING);
            if (isTaskCancelled(taskId)) return;

            LocalDateTime currentTime = databaseNow();
            LocalDateTime startedAt = currentTime;
            LocalDateTime leaseExpiresAt = currentTime.plus(TASK_LEASE_DURATION);
            int started = taskRepository.startTaskIfStillPending(
                    taskId,
                    FuzzTaskPo.TaskStatus.RUNNING,
                    startedAt,
                    workerId,
                    currentTime,
                    leaseExpiresAt,
                    serializeCheckLogs(List.of("Counterexample search task started")),
                    FuzzTaskPo.TaskStatus.PENDING);
            if (started == 0) {
                log.info("Fuzz task {} is no longer pending; skipping execution", taskId);
                return;
            }
            task = taskRepository.findById(taskId).orElse(null);
            if (task == null) {
                log.error("Fuzz task {} disappeared after it started", taskId);
                return;
            }

            NormalizedRequest request = executionRequest(task);
            ModelInputSnapshot frozenSnapshot = JsonUtils.fromJson(
                    task.getModelInputSnapshotJson(), ModelInputSnapshot.class);
            if (frozenSnapshot == null) {
                throw new IllegalStateException("Frozen Board snapshot is missing");
            }
            FuzzEngineInput engineInput = new FuzzEngineInput(frozenSnapshot, new FuzzEngineConfig(
                    request.targetSpecIds(), request.maxIterations(), request.pathLength(),
                    request.populationSize(), request.seed(), request.explorationMode()));

            updateTaskProgress(taskId, 1, TaskProgressStage.PREPARING_EXPLORATION);
            BooleanSupplier cancelled = cancellationSignal(taskId);
            FuzzEngineResult result = fuzzEngine.run(
                    engineInput,
                    (percent, message) -> reportEngineProgress(taskId, percent, message),
                    cancelled);

            if (cancelled.getAsBoolean() || result != null
                    && result.outcome() == FuzzEngineOutcome.CANCELLED) {
                atomicCancelTask(taskId, currentTaskTime());
                return;
            }

            validateEngineResult(
                    result,
                    request.pathLength(),
                    request.maxIterations(),
                    request.populationSize());
            FuzzEligibilityDto eligibility = toEligibility(
                    result.eligibility(), request.targetSpecIds(), engineInput.snapshot().specifications());
            List<String> limitations = normalizeLimitations(
                    result.limitations(), request.explorationMode());
            FuzzOutcome outcome = toOutcome(result.outcome());
            List<FuzzFindingPo> findings = toFindingEntities(userId, taskId, result);

            updateTaskProgress(taskId, 95, TaskProgressStage.PERSISTING_RESULT);
            boolean completed = completeTaskAndFindings(
                    task, userId, result, outcome, eligibility, limitations, findings);
            if (!completed && !isCancelledOrTerminal(taskId)) {
                failTask(task,
                        "Counterexample search completed, but its result could not be saved");
            }
        } catch (Exception e) {
            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                log.info("Fuzz task {} cancelled while the engine was stopping", taskId);
            } else {
                log.error("Fuzz task {} failed", taskId, e);
                String message = "Counterexample search failed: " + publicTaskFailureMessage(e);
                markTaskFailedSafely(taskId, task, message);
            }
        } finally {
            if (removeCancelledMark(taskId) && task != null) {
                handleCancellation(task);
            }
            removeRunningTask(taskId);
            removeTaskProgress(taskId);
            try {
                taskRepository.releaseOwnedActiveLease(
                        taskId,
                        workerId,
                        databaseNow().minusSeconds(1),
                        ACTIVE_STATUSES);
            } catch (RuntimeException e) {
                log.warn("Could not release fuzz task {} lease; it will expire naturally", taskId, e);
            }
        }
    }

    private void markTaskFailedSafely(Long taskId, FuzzTaskPo task, String message) {
        try {
            if (task == null) {
                failTaskById(taskId, message);
            } else {
                failTask(task, message);
            }
        } catch (RuntimeException persistenceError) {
            log.error("Could not persist failure state for fuzz task {}; its lease will expire",
                    taskId, persistenceError);
        }
    }

    private void reportEngineProgress(Long taskId, int percent, String message) {
        if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) return;
        try {
            int bounded = Math.min(90, Math.max(1, percent));
            updateTaskProgress(taskId, bounded, TaskProgressStage.EXPLORING_CANDIDATES);
        } catch (RuntimeException e) {
            log.warn("Could not persist progress for fuzz task {}", taskId, e);
        }
    }

    BooleanSupplier cancellationSignal(Long taskId) {
        AtomicBoolean databaseCancellation = new AtomicBoolean(false);
        AtomicLong nextDatabasePoll = new AtomicLong(0L);
        return () -> {
            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()
                    || databaseCancellation.get()) {
                return true;
            }
            long now = System.nanoTime();
            long nextPoll = nextDatabasePoll.get();
            if (now < nextPoll || !nextDatabasePoll.compareAndSet(
                    nextPoll, now + CANCELLATION_DB_POLL_NANOS)) {
                return false;
            }
            boolean noLongerRunning = taskRepository.findStatusById(taskId)
                    .map(status -> status != FuzzTaskPo.TaskStatus.RUNNING)
                    .orElse(true);
            if (noLongerRunning) databaseCancellation.set(true);
            return noLongerRunning;
        };
    }

    private boolean completeTaskAndFindings(FuzzTaskPo task,
                                            Long userId,
                                            FuzzEngineResult result,
                                            FuzzOutcome outcome,
                                            FuzzEligibilityDto eligibility,
                                             List<String> limitations,
                                             List<FuzzFindingPo> findings) {
        String eligibilityJson = JsonUtils.toJson(eligibility);
        String limitationsJson = JsonUtils.toJson(limitations);
        requireBoundedRunMetadata(eligibilityJson, limitationsJson);
        return Boolean.TRUE.equals(transactionTemplate.execute(status -> {
            if (isTaskCancelled(task.getId()) || Thread.currentThread().isInterrupted()) {
                status.setRollbackOnly();
                return false;
            }
            if (userRepository.findByIdForUpdate(userId).isEmpty()) {
                status.setRollbackOnly();
                return false;
            }

            taskRepository.findByIdForUpdate(task.getId());
            LocalDateTime evidenceCreatedAt = databaseNow();
            findings.forEach(finding -> finding.setCreatedAt(evidenceCreatedAt));
            findingRepository.saveAllAndFlush(findings);
            if (isTaskCancelled(task.getId()) || Thread.currentThread().isInterrupted()) {
                status.setRollbackOnly();
                return false;
            }

            LocalDateTime completedAt = databaseNow();
            Long processingTimeMs = task.getStartedAt() == null ? null
                    : Duration.between(task.getStartedAt(), completedAt).toMillis();
            List<String> logs = List.of(
                    "Counterexample search completed",
                    "Outcome: " + outcome,
                    "Generated paths: " + result.generatedPaths(),
                    "Findings: " + findings.size());
            int updated = taskRepository.completeTaskIfRunning(
                    task.getId(),
                    FuzzTaskPo.TaskStatus.COMPLETED,
                    completedAt,
                    processingTimeMs,
                    outcome,
                    result.effectiveSeed(),
                    result.iterations(),
                    result.generatedPaths(),
                    result.elapsedMs(),
                    eligibilityJson,
                    limitationsJson,
                    findings.size(),
                    serializeCheckLogs(logs),
                    FuzzTaskPo.TaskStatus.RUNNING,
                    workerId,
                    completedAt);
            if (updated == 0) {
                status.setRollbackOnly();
                return false;
            }
            return true;
        }));
    }

    private List<FuzzFindingPo> toFindingEntities(Long userId,
                                                  Long taskId,
                                                  FuzzEngineResult result) {
        List<FuzzFindingPo> entities = new ArrayList<>();
        long aggregateEvidenceBytes = 0L;
        for (FuzzFinding finding : result.findings()) {
            SpecificationDto specification = finding.specification();
            List<FuzzInputEventDto> events = finding.inputEvents().stream()
                    .map(this::toInputEventDto)
                    .toList();
            String specificationJson = JsonUtils.toJson(specification);
            String statesJson = JsonUtils.toJson(finding.states());
            String inputEventsJson = JsonUtils.toJson(events);
            long findingEvidenceBytes;
            try {
                findingEvidenceBytes = Math.addExact(
                        Math.addExact(utf8Length(specificationJson), utf8Length(statesJson)),
                        utf8Length(inputEventsJson));
                aggregateEvidenceBytes = Math.addExact(
                        aggregateEvidenceBytes, findingEvidenceBytes);
            } catch (ArithmeticException e) {
                throw new EvidenceLimitExceededException();
            }
            if (findingEvidenceBytes > MAX_FINDING_EVIDENCE_BYTES
                    || aggregateEvidenceBytes > MAX_RUN_EVIDENCE_BYTES) {
                throw new EvidenceLimitExceededException();
            }
            entities.add(FuzzFindingPo.builder()
                    .userId(userId)
                    .fuzzTaskId(taskId)
                    .violatedSpecId(specification.getId())
                    .violatedSpecJson(specificationJson)
                    .firstViolationStep(finding.firstViolationStep())
                    .statesJson(statesJson)
                    .inputEventsJson(inputEventsJson)
                    .seed(result.effectiveSeed())
                    .stateCount(finding.states().size())
                    .build());
        }
        return entities;
    }

    private FuzzInputEventDto toInputEventDto(FuzzInputEvent event) {
        return FuzzInputEventDto.builder()
                .step(event.step())
                .kind(event.kind().name())
                .targetId(event.targetId())
                .property(event.property())
                .value(event.value())
                .source(event.source().name())
                .build();
    }

    private FuzzEligibilityDto toEligibility(List<FuzzSpecEligibility> engineEligibility,
                                             List<String> targetSpecIds,
                                             List<SpecificationDto> allSpecifications) {
        LinkedHashSet<String> eligibleIds = new LinkedHashSet<>();
        Map<String, String> eligibleLabels = new LinkedHashMap<>();
        List<FuzzIneligibleSpecDto> ineligible = new ArrayList<>();
        for (FuzzSpecEligibility item : engineEligibility) {
            SpecificationDto specification = item.specification();
            String specId = specification == null ? null : specification.getId();
            String label = boundedSingleLine(
                    specificationLabel(specification), specId, MAX_ELIGIBILITY_LABEL_CHARS);
            if (item.supported()) {
                if (specId != null && eligibleIds.add(specId)) {
                    eligibleLabels.put(specId, label);
                }
            } else {
                ineligible.add(FuzzIneligibleSpecDto.builder()
                        .specId(specId)
                        .specificationLabel(label)
                        .reasonCode(item.reasonCode())
                        .reason(boundedSingleLine(
                                item.reason(), "Unsupported for counterexample exploration",
                                MAX_ELIGIBILITY_REASON_CHARS))
                        .build());
            }
        }
        int requestedCount = targetSpecIds.isEmpty() ? allSpecifications.size() : targetSpecIds.size();
        return FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.copyOf(eligibleIds))
                .eligibleSpecLabels(Map.copyOf(eligibleLabels))
                .ineligibleSpecs(List.copyOf(ineligible))
                .requestedSpecCount(requestedCount)
                .eligibleSpecCount(eligibleIds.size())
                .build();
    }

    private String specificationLabel(SpecificationDto specification) {
        if (specification == null) return null;
        if (specification.getTemplateLabel() != null && !specification.getTemplateLabel().isBlank()) {
            return specification.getTemplateLabel();
        }
        if (specification.getFormula() != null && !specification.getFormula().isBlank()) {
            return specification.getFormula();
        }
        return specification.getId();
    }

    private FuzzOutcome toOutcome(FuzzEngineOutcome outcome) {
        return switch (outcome) {
            case FINDINGS_FOUND -> FuzzOutcome.FOUND_VIOLATION;
            case BUDGET_EXHAUSTED -> FuzzOutcome.BUDGET_EXHAUSTED;
            case NO_ELIGIBLE_SPECIFICATIONS -> FuzzOutcome.INCONCLUSIVE;
            case CANCELLED -> throw new IllegalStateException("Cancelled engine result cannot be completed");
        };
    }

    void validateEngineResult(
            FuzzEngineResult result,
            int pathLength,
            int maxIterations,
            int populationSize) {
        if (pathLength < 1 || pathLength > 50
                || maxIterations < 1 || maxIterations > 5_000
                || populationSize < 1 || populationSize > 50) {
            throw new IllegalStateException("Fuzz engine result has no valid execution budget");
        }
        if (result == null || result.outcome() == null) {
            throw new IllegalStateException("Fuzz engine returned no outcome");
        }
        if (result.effectiveSeed() < 0 || result.effectiveSeed() > FuzzRequestDto.JS_SAFE_SEED_MAX) {
            throw new IllegalStateException("Fuzz engine returned an out-of-range effective seed");
        }
        if (result.iterations() < 0 || result.generatedPaths() < 0 || result.elapsedMs() < 0) {
            throw new IllegalStateException("Fuzz engine returned negative execution statistics");
        }
        long maximumGeneratedPaths;
        try {
            maximumGeneratedPaths = Math.multiplyExact(
                    (long) result.iterations(), populationSize);
        } catch (ArithmeticException e) {
            throw new IllegalStateException("Fuzz engine returned overflowing execution statistics", e);
        }
        if (result.iterations() > maxIterations
                || (result.iterations() == 0) != (result.generatedPaths() == 0)
                || (result.iterations() > 0 && result.generatedPaths() < result.iterations())
                || result.generatedPaths() > maximumGeneratedPaths) {
            throw new IllegalStateException("Fuzz engine returned inconsistent execution statistics");
        }
        if (result.outcome() == FuzzEngineOutcome.FINDINGS_FOUND && result.findings().isEmpty()) {
            throw new IllegalStateException("Fuzz engine reported findings without finding data");
        }
        if (result.outcome() != FuzzEngineOutcome.FINDINGS_FOUND && !result.findings().isEmpty()) {
            throw new IllegalStateException("Fuzz engine returned findings for a non-finding outcome");
        }
        Set<String> findingSpecIds = new LinkedHashSet<>();
        for (FuzzFinding finding : result.findings()) {
            if (finding == null || finding.specification() == null
                    || finding.specification().getId() == null
                    || finding.specification().getId().isBlank()
                    || finding.specification().getId().length() > MAX_STABLE_CODE_CHARS) {
                throw new IllegalStateException("Fuzz engine returned a finding without a specification");
            }
            if (!findingSpecIds.add(finding.specification().getId())) {
                throw new IllegalStateException("Fuzz engine returned duplicate findings for a specification");
            }
            if (finding.firstViolationStep() < 0 || finding.states().isEmpty()
                    || finding.states().size() > pathLength
                    || finding.firstViolationStep() != finding.states().size() - 1) {
                throw new IllegalStateException("Fuzz engine returned incomplete finding trace data");
            }
            validateInputEventSequence(finding);
        }
        if (result.eligibility().stream().anyMatch(Objects::isNull)) {
            throw new IllegalStateException("Fuzz engine returned invalid eligibility data");
        }
        Set<String> eligibilitySpecIds = new LinkedHashSet<>();
        Set<String> eligibleSpecIds = new LinkedHashSet<>();
        for (FuzzSpecEligibility eligibility : result.eligibility()) {
            if (eligibility.specification() == null
                    || eligibility.specification().getId() == null
                    || eligibility.specification().getId().isBlank()
                    || eligibility.specification().getId().length() > MAX_STABLE_CODE_CHARS) {
                throw new IllegalStateException("Fuzz engine returned eligibility without a specification");
            }
            String specId = eligibility.specification().getId();
            if (!eligibilitySpecIds.add(specId)) {
                throw new IllegalStateException("Fuzz engine returned duplicate specification eligibility");
            }
            if (!eligibility.supported()
                    && (eligibility.reasonCode() == null || eligibility.reasonCode().isBlank()
                    || eligibility.reasonCode().length() > MAX_STABLE_CODE_CHARS
                    || !STABLE_CODE.matcher(eligibility.reasonCode()).matches()
                    || eligibility.reason() == null || eligibility.reason().isBlank())) {
                throw new IllegalStateException("Fuzz engine returned incomplete ineligibility details");
            }
            if (eligibility.supported()) eligibleSpecIds.add(specId);
        }
        if (result.outcome() != FuzzEngineOutcome.CANCELLED && eligibilitySpecIds.isEmpty()) {
            throw new IllegalStateException("Fuzz engine returned no specification eligibility");
        }
        if (result.outcome() == FuzzEngineOutcome.NO_ELIGIBLE_SPECIFICATIONS
                && !eligibleSpecIds.isEmpty()) {
            throw new IllegalStateException("Fuzz engine reported no eligible specifications inconsistently");
        }
        if (result.outcome() != FuzzEngineOutcome.NO_ELIGIBLE_SPECIFICATIONS
                && result.outcome() != FuzzEngineOutcome.CANCELLED
                && eligibleSpecIds.isEmpty()) {
            throw new IllegalStateException("Fuzz engine returned a search outcome without eligible specifications");
        }
        if (!eligibleSpecIds.containsAll(findingSpecIds)) {
            throw new IllegalStateException("Fuzz engine returned a finding for an ineligible specification");
        }
    }

    private void validateInputEventSequence(FuzzFinding finding) {
        int previousStep = -1;
        int previousSourceOrder = -1;
        for (FuzzInputEvent event : finding.inputEvents()) {
            if (event == null || event.kind() == null || event.source() == null
                    || !hasText(event.targetId()) || !hasText(event.property()) || !hasText(event.value())) {
                throw new IllegalStateException("Fuzz engine returned an invalid input event");
            }
            if (event.step() < 0 || event.step() > finding.firstViolationStep()) {
                throw new IllegalStateException("Fuzz engine returned an input event outside the finding prefix");
            }
            if (event.source() == FuzzInputEventSource.RANDOM_INITIAL_STATE && event.step() != 0) {
                throw new IllegalStateException("Fuzz engine returned a random initial-state event after step 0");
            }
            int sourceOrder = inputEventSourceOrder(event.source());
            if (event.step() < previousStep
                    || (event.step() == previousStep && sourceOrder < previousSourceOrder)) {
                throw new IllegalStateException("Fuzz engine returned input events out of causal order");
            }
            if (event.step() != previousStep) {
                previousSourceOrder = sourceOrder;
            } else {
                previousSourceOrder = Math.max(previousSourceOrder, sourceOrder);
            }
            previousStep = event.step();
        }
    }

    private int inputEventSourceOrder(FuzzInputEventSource source) {
        return switch (source) {
            case RANDOM_INITIAL_STATE -> 0;
            case SEED_EVENT -> 1;
            case MODEL_CHOICE -> 2;
        };
    }

    List<String> normalizeLimitations(
            Collection<String> limitations, FuzzExplorationMode explorationMode) {
        if (limitations == null) {
            throw new IllegalStateException("Fuzz engine returned no limitation data");
        }
        if (limitations.size() > FuzzMetadataPolicy.MAX_LIMITATION_CODES) {
            throw new IllegalStateException("Fuzz engine returned too many limitation codes");
        }
        List<String> normalized = new ArrayList<>(limitations.size());
        Set<String> seen = new LinkedHashSet<>();
        for (String code : limitations) {
            if (code == null || code.length() > MAX_STABLE_CODE_CHARS
                    || !STABLE_CODE.matcher(code).matches()) {
                throw new IllegalStateException("Fuzz engine returned an invalid limitation code");
            }
            if (!seen.add(code)) {
                throw new IllegalStateException("Fuzz engine returned duplicate limitation codes");
            }
            normalized.add(code);
        }
        if (explorationMode == null
                || !seen.containsAll(FuzzLimitationContract.requiredCodes(explorationMode))) {
            throw new IllegalStateException("Fuzz engine omitted required semantic limitation codes");
        }
        return List.copyOf(normalized);
    }

    private boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    private NormalizedRequest validateAndNormalize(FuzzRequestDto request) {
        if (request == null) {
            throw new ValidationException(
                    "request", "Counterexample search request cannot be null");
        }
        int maxIterations = requirePositive(request.getMaxIterations(),
                "maxIterations", "Maximum iterations must be at least 1");
        int pathLength = requirePositive(request.getPathLength(),
                "pathLength", "Path length must be at least 1");
        int populationSize = requirePositive(request.getPopulationSize(),
                "populationSize", "Population size must be at least 1");
        long searchWork;
        try {
            searchWork = Math.multiplyExact(
                    Math.multiplyExact((long) maxIterations, pathLength), populationSize);
        } catch (ArithmeticException e) {
            throw new ValidationException("request",
                    "Iteration, path length, and population budgets are too large in combination");
        }
        if (searchWork > MAX_EFFECTIVE_WORK) {
            throw new ValidationException("request",
                    "Iteration, path length, and population budgets are too large in combination");
        }
        maxIterations = requireRange(maxIterations, 1, 5_000,
                "maxIterations", "Maximum iterations must be between 1 and 5000");
        pathLength = requireRange(pathLength, 1, 50,
                "pathLength", "Path length must be between 1 and 50");
        populationSize = requireRange(populationSize, 1, 50,
                "populationSize", "Population size must be between 1 and 50");
        Long seed = request.getSeed();
        if (seed != null && (seed < 0 || seed > FuzzRequestDto.JS_SAFE_SEED_MAX)) {
            throw new ValidationException("seed", "Seed must be between 0 and "
                    + FuzzRequestDto.JS_SAFE_SEED_MAX);
        }
        List<String> targetSpecIds = normalizeTargetSpecIds(request.getTargetSpecIds());
        FuzzExplorationMode explorationMode = request.getExplorationMode() == null
                ? FuzzExplorationMode.BOARD_SNAPSHOT
                : request.getExplorationMode();
        String paperDomainFingerprint = request.getPaperDomainFingerprint();
        if (explorationMode == FuzzExplorationMode.PAPER_COMPATIBLE) {
            if (paperDomainFingerprint == null
                    || !MODEL_FINGERPRINT.matcher(paperDomainFingerprint).matches()) {
                throw new ValidationException(
                        "paperDomainFingerprint",
                        "A current random-state input-range fingerprint is required");
            }
        } else if (paperDomainFingerprint != null) {
            throw new ValidationException(
                    "paperDomainFingerprint",
                    "Input-range data is only valid with the random-state search strategy");
        }
        return new NormalizedRequest(
                targetSpecIds,
                maxIterations,
                pathLength,
                populationSize,
                seed,
                explorationMode,
                paperDomainFingerprint);
    }

    String modelFingerprint(ModelInputSnapshot snapshot) {
        return fingerprint(snapshot, null);
    }

    String paperDomainFingerprint(ModelInputSnapshot snapshot, int pathLength) {
        if (pathLength < 1 || pathLength > 50) {
            throw new IllegalArgumentException("pathLength must be between 1 and 50");
        }
        return fingerprint(snapshot, pathLength);
    }

    private String fingerprint(ModelInputSnapshot snapshot, Integer pathLength) {
        try {
            Map<String, Object> semanticModel = new LinkedHashMap<>();
            semanticModel.put("devices", snapshot.devices());
            semanticModel.put("environmentVariables", sortedForFingerprint(
                    snapshot.environmentVariables(), variable -> variable.getName()));
            semanticModel.put("rules", snapshot.rules());
            semanticModel.put("specifications", snapshot.specifications());
            semanticModel.put("templateManifests", snapshot.templateManifests());
            if (pathLength != null) semanticModel.put("pathLength", pathLength);
            JsonNode canonicalModel = fingerprintMapper.valueToTree(semanticModel);
            removePresentationFields(canonicalModel);
            byte[] canonical = fingerprintWriter.writeValueAsBytes(canonicalModel);
            byte[] digest = MessageDigest.getInstance("SHA-256").digest(canonical);
            return HexFormat.of().formatHex(digest);
        } catch (JsonProcessingException | NoSuchAlgorithmException exception) {
            throw new IllegalStateException("Cannot fingerprint the frozen Board snapshot", exception);
        }
    }

    private static <T> List<T> sortedForFingerprint(
            List<T> values, Function<T, String> identity) {
        return values.stream()
                .sorted(Comparator.comparing(value -> value == null
                        ? ""
                        : Objects.toString(identity.apply(value), "")))
                .toList();
    }

    private void removePresentationFields(JsonNode node) {
        if (node == null) return;
        if (node instanceof ObjectNode object) {
            object.remove(List.of(
                    "deviceLabel", "templateLabel", "formula", "ruleString", "createdAt",
                    "Description", "Icon", "description", "icon"));
            object.elements().forEachRemaining(this::removePresentationFields);
        } else if (node.isArray()) {
            node.elements().forEachRemaining(this::removePresentationFields);
        }
    }

    private int requireRange(Integer value, int minimum, int maximum, String field, String message) {
        if (value == null || value < minimum || value > maximum) {
            throw new ValidationException(field, message);
        }
        return value;
    }

    private int requirePositive(Integer value, String field, String message) {
        if (value == null || value < 1) {
            throw new ValidationException(field, message);
        }
        return value;
    }

    private List<String> normalizeTargetSpecIds(List<String> targetSpecIds) {
        if (targetSpecIds == null || targetSpecIds.isEmpty()) return List.of();
        if (targetSpecIds.size() > 100) {
            throw new ValidationException("targetSpecIds", "At most 100 target specifications can be selected");
        }
        List<String> normalized = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (int i = 0; i < targetSpecIds.size(); i++) {
            String value = targetSpecIds.get(i);
            String specId = value == null ? null : value.trim();
            if (specId == null || specId.isEmpty()) {
                throw new ValidationException("targetSpecIds[" + i + "]", "Target specification ID cannot be blank");
            }
            if (specId.length() > 100) {
                throw new ValidationException("targetSpecIds[" + i + "]",
                        "Target specification ID must be at most 100 characters");
            }
            if (!seen.add(specId)) {
                throw new ValidationException("targetSpecIds", "Target specification IDs must be unique");
            }
            normalized.add(specId);
        }
        return List.copyOf(normalized);
    }

    private void validateTargetSpecifications(List<String> targetSpecIds,
                                              List<SpecificationDto> specifications) {
        if (specifications == null || specifications.isEmpty()) {
            throw new ValidationException("targetSpecIds",
                    "The Board must contain at least one specification before starting a counterexample search");
        }
        if (targetSpecIds.isEmpty()) {
            if (specifications.size() > 100) {
                throw new ValidationException("targetSpecIds",
                        "The board has more than 100 specifications; select at most 100 explicitly");
            }
            return;
        }
        Set<String> available = specifications.stream()
                .filter(Objects::nonNull)
                .map(SpecificationDto::getId)
                .filter(Objects::nonNull)
                .collect(Collectors.toSet());
        List<String> missing = targetSpecIds.stream().filter(id -> !available.contains(id)).toList();
        if (!missing.isEmpty()) {
            throw new ValidationException("targetSpecIds",
                    "Unknown target specification IDs: " + String.join(", ", missing));
        }
    }

    private void validateEffectiveWorkload(
            NormalizedRequest request,
            ModelInputSnapshot snapshot) {
        long effectiveWork = effectiveWorkload(
                request.maxIterations(),
                request.pathLength(),
                request.populationSize(),
                modelComplexityUnits(snapshot));
        if (effectiveWork > MAX_EFFECTIVE_WORK) {
            throw new ValidationException("request",
                    "Counterexample search workload exceeds the 12500000 evaluation limit");
        }
    }

    private long effectiveWorkload(
            int maxIterations,
            int pathLength,
            int populationSize,
            long modelComplexity) {
        try {
            long baseWork = Math.multiplyExact(
                    Math.multiplyExact((long) maxIterations, pathLength),
                    populationSize);
            return Math.multiplyExact(baseWork, Math.max(1L, modelComplexity));
        } catch (ArithmeticException exception) {
            return Long.MAX_VALUE;
        }
    }

    long modelComplexityUnits(ModelInputSnapshot snapshot) {
        if (snapshot == null) {
            throw new ValidationException("request", "Frozen Board snapshot is missing");
        }
        StructureCounter counter = new StructureCounter();
        counter.addCollection("devices", snapshot.devices());
        counter.addCollection("environmentVariables", snapshot.environmentVariables());
        counter.addCollection("rules", snapshot.rules());
        counter.addCollection("specifications", snapshot.specifications());
        long modeTransitionUnits = 0L;
        long apiModeUnits = 0L;
        long ruleConditionUnits = 0L;
        long specificationConditionUnits = 0L;
        Map<String, Long> rulesPerTarget = new LinkedHashMap<>();

        Map<String, DeviceManifest> manifestsByName = new LinkedHashMap<>();
        for (Map.Entry<String, DeviceManifest> entry : snapshot.templateManifests().entrySet()) {
            String key = entry.getKey() == null ? null : entry.getKey().trim().toLowerCase(java.util.Locale.ROOT);
            if (key == null || key.isEmpty() || entry.getValue() == null
                    || manifestsByName.putIfAbsent(key, entry.getValue()) != null) {
                throw new ValidationException("request", "Frozen Board contains invalid template manifests");
            }
        }

        for (DeviceVerificationDto device : snapshot.devices()) {
            if (device == null || device.getTemplateName() == null || device.getTemplateName().isBlank()) {
                throw new ValidationException("request", "Frozen Board contains an invalid device");
            }
            DeviceManifest manifest = manifestsByName.get(
                    device.getTemplateName().trim().toLowerCase(java.util.Locale.ROOT));
            if (manifest == null) {
                throw new ValidationException("request",
                        "Frozen Board device references a missing template manifest");
            }
            counter.addCollection("deviceVariables", device.getVariables());
            counter.addCollection("devicePrivacies", device.getPrivacies());
            addManifestComplexity(counter, manifest);
            modeTransitionUnits = addOperationalUnits(
                    modeTransitionUnits,
                    multiplyOperationalUnits(
                            safeList(manifest.getModes()).size(),
                            safeList(manifest.getTransitions()).size()));
            apiModeUnits = addOperationalUnits(
                    apiModeUnits,
                    multiplyOperationalUnits(
                            safeList(manifest.getModes()).size(),
                            safeList(manifest.getApis()).size()));
        }

        for (RuleDto rule : snapshot.rules()) {
            if (rule == null) {
                throw new ValidationException("request", "Frozen Board contains a null rule");
            }
            counter.addCollection("ruleConditions", rule.getConditions());
            ruleConditionUnits = addOperationalUnits(
                    ruleConditionUnits, safeList(rule.getConditions()).size());
            String targetId = rule.getCommand() == null || !hasText(rule.getCommand().getDeviceName())
                    ? "<invalid>"
                    : rule.getCommand().getDeviceName().trim();
            rulesPerTarget.put(
                    targetId,
                    addOperationalUnits(rulesPerTarget.getOrDefault(targetId, 0L), 1L));
        }
        for (SpecificationDto specification : snapshot.specifications()) {
            if (specification == null) {
                throw new ValidationException("request", "Frozen Board contains a null specification");
            }
            counter.addCollection("aConditions", specification.getAConditions());
            counter.addCollection("ifConditions", specification.getIfConditions());
            counter.addCollection("thenConditions", specification.getThenConditions());
            specificationConditionUnits = addOperationalUnits(
                    specificationConditionUnits,
                    addOperationalUnits(
                            safeList(specification.getAConditions()).size(),
                            addOperationalUnits(
                                    safeList(specification.getIfConditions()).size(),
                                    safeList(specification.getThenConditions()).size())));
        }

        // The additive guard above bounds stored structure. These products account for
        // the nested loops that dominate each generated state and paper-distance pass.
        long environmentDeviceUnits = multiplyOperationalUnits(
                snapshot.environmentVariables().size(), snapshot.devices().size());
        long ruleCount = snapshot.rules().size();
        long orderedRuleArbitrationUnits = 0L;
        for (long targetRuleCount : rulesPerTarget.values()) {
            orderedRuleArbitrationUnits = addOperationalUnits(
                    orderedRuleArbitrationUnits,
                    multiplyOperationalUnits(targetRuleCount, targetRuleCount));
        }
        long predecessorRuleUnits = multiplyOperationalUnits(
                specificationConditionUnits,
                addOperationalUnits(ruleCount, ruleConditionUnits));
        long operationalUnits = counter.total();
        operationalUnits = addOperationalUnits(operationalUnits, environmentDeviceUnits);
        operationalUnits = addOperationalUnits(operationalUnits, modeTransitionUnits);
        operationalUnits = addOperationalUnits(operationalUnits, apiModeUnits);
        operationalUnits = addOperationalUnits(operationalUnits, orderedRuleArbitrationUnits);
        return addOperationalUnits(operationalUnits, predecessorRuleUnits);
    }

    private long multiplyOperationalUnits(long left, long right) {
        try {
            return Math.multiplyExact(left, right);
        } catch (ArithmeticException exception) {
            throw new ValidationException(
                    "request", "Counterexample-search operational model complexity is too large");
        }
    }

    private long addOperationalUnits(long left, long right) {
        try {
            return Math.addExact(left, right);
        } catch (ArithmeticException exception) {
            throw new ValidationException(
                    "request", "Counterexample-search operational model complexity is too large");
        }
    }

    private void addManifestComplexity(StructureCounter counter, DeviceManifest manifest) {
        counter.addCollection("templateModes", manifest.getModes());
        counter.addCollection("templateInternalVariables", manifest.getInternalVariables());
        counter.addCollection("templateEnvironmentDomains", manifest.getEnvironmentDomains());
        counter.addCollection("templateImpactedVariables", manifest.getImpactedVariables());
        counter.addCollection("templateWorkingStates", manifest.getWorkingStates());
        counter.addCollection("templateTransitions", manifest.getTransitions());
        counter.addCollection("templateApis", manifest.getApis());

        for (DeviceManifest.InternalVariable variable : safeList(manifest.getInternalVariables())) {
            if (variable == null) {
                throw new ValidationException("request", "Template contains a null internal variable");
            }
            counter.addCollection("templateVariableValues", variable.getValues());
        }
        for (DeviceManifest.EnvironmentDomain domain : safeList(manifest.getEnvironmentDomains())) {
            if (domain == null) {
                throw new ValidationException("request", "Template contains a null environment domain");
            }
            counter.addCollection("templateEnvironmentValues", domain.getValues());
        }
        for (DeviceManifest.WorkingState state : safeList(manifest.getWorkingStates())) {
            if (state == null) {
                throw new ValidationException("request", "Template contains a null working state");
            }
            counter.addCollection("templateStateDynamics", state.getDynamics());
        }
        for (DeviceManifest.Transition transition : safeList(manifest.getTransitions())) {
            if (transition == null) {
                throw new ValidationException("request", "Template contains a null transition");
            }
            counter.addCollection("templateTransitionAssignments", transition.getAssignments());
        }
    }

    private <T> List<T> safeList(List<T> values) {
        return values == null ? List.of() : values;
    }

    private static final class StructureCounter {
        private long total;

        private void addCollection(String field, Collection<?> values) {
            int size = values == null ? 0 : values.size();
            if (size > MAX_FUZZ_COLLECTION_ITEMS) {
                throw new ValidationException("request",
                        field + " exceeds the counterexample-search collection limit of "
                                + MAX_FUZZ_COLLECTION_ITEMS);
            }
            try {
                total = Math.addExact(total, size);
            } catch (ArithmeticException e) {
                throw new ValidationException(
                        "request", "Counterexample-search model structure is too large");
            }
            if (total > MAX_MODEL_STRUCTURE_UNITS) {
                throw new ValidationException("request",
                        "Counterexample-search model structure exceeds the "
                                + MAX_MODEL_STRUCTURE_UNITS + " unit limit");
            }
        }

        private long total() {
            return total;
        }
    }

    @Override
    @Transactional(readOnly = true)
    public FuzzTaskDto getTask(Long userId, Long taskId) {
        FuzzTaskSummaryProjection task = taskRepository.findSummaryByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(
                        "Counterexample search task", taskId));
        return fuzzMapper.toTaskDtoProjection(task);
    }

    @Override
    @Transactional(readOnly = true)
    public List<FuzzTaskSummaryDto> getTasks(
            Long userId, List<Long> excludedTaskIds, int page, int size) {
        List<Long> exclusions = normalizeExcludedTaskIds(excludedTaskIds);
        Pageable pageable = pageRequest(page, size, 200);
        List<FuzzTaskSummaryProjection> tasks = exclusions.isEmpty()
                ? taskRepository.findSummaryByUserIdAndStatusNotOrderByCreatedAtDescIdDesc(
                        userId, FuzzTaskPo.TaskStatus.COMPLETED, pageable)
                : taskRepository.findSummaryByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDescIdDesc(
                        userId, FuzzTaskPo.TaskStatus.COMPLETED, exclusions, pageable);
        return tasks.stream().map(fuzzMapper::toTaskSummaryDtoProjection).toList();
    }

    @Override
    @Transactional(readOnly = true)
    public int getTaskProgress(Long userId, Long taskId) {
        FuzzTaskProgressProjection task = taskRepository.findProgressByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(
                        "Counterexample search task", taskId));
        if (task.getProgress() != null) return task.getProgress();
        FuzzTaskPo.TaskStatus status = task.getStatus();
        return status == FuzzTaskPo.TaskStatus.COMPLETED
                || status == FuzzTaskPo.TaskStatus.FAILED
                || status == FuzzTaskPo.TaskStatus.CANCELLED ? 100 : 0;
    }

    @Override
    @Transactional
    public TaskCancellationResultDto cancelTask(Long userId, Long taskId) {
        return super.cancelTask(userId, taskId);
    }

    @Override
    @Transactional
    public void deleteTask(Long userId, Long taskId) {
        FuzzTaskPo task = requireOwnedTask(userId, taskId);
        if (task.getStatus() == FuzzTaskPo.TaskStatus.PENDING
                || task.getStatus() == FuzzTaskPo.TaskStatus.RUNNING) {
            throw new BadRequestException(
                    "An active counterexample search must be cancelled before it can be removed");
        }
        if (task.getStatus() == FuzzTaskPo.TaskStatus.COMPLETED) {
            throw new BadRequestException(
                    "Completed counterexample-search results must be removed from run history");
        }
        taskRepository.delete(task);
    }

    @Override
    @Transactional(readOnly = true)
    public List<FuzzRunSummaryDto> getRuns(Long userId, int page, int size) {
        Pageable pageable = pageRequest(page, size, 100);
        List<FuzzTaskSummaryProjection> runs =
                taskRepository.findSummaryByUserIdAndStatusOrderByCreatedAtDescIdDesc(
                userId, FuzzTaskPo.TaskStatus.COMPLETED, pageable);
        if (runs.isEmpty()) return List.of();
        List<Long> runIds = runs.stream().map(FuzzTaskSummaryProjection::getId).toList();
        Map<Long, List<FuzzFindingSummaryProjection>> findingsByRun = findingRepository
                .findSummariesByUserIdAndFuzzTaskIdIn(userId, runIds)
                .stream()
                .collect(Collectors.groupingBy(
                        FuzzFindingSummaryProjection::getFuzzTaskId,
                        LinkedHashMap::new,
                        Collectors.toList()));
        return runs.stream()
                .map(run -> toRunSummaryOrUnavailable(
                        run, findingsByRun.getOrDefault(run.getId(), List.of())))
                .toList();
    }

    private FuzzRunSummaryDto toRunSummaryOrUnavailable(
            FuzzTaskSummaryProjection run, List<FuzzFindingSummaryProjection> findings) {
        try {
            return fuzzMapper.toRunSummaryDtoFromTaskProjection(run, findings);
        } catch (RuntimeException e) {
            log.error("Fuzz history item {} is unavailable because persisted data is invalid",
                    run != null ? run.getId() : null, e);
            return FuzzRunSummaryDto.builder()
                    .id(run != null ? run.getId() : null)
                    .createdAt(run != null ? run.getCreatedAt() : null)
                    .completedAt(run != null ? run.getCompletedAt() : null)
                    .findingCount(run != null && run.getFindingCount() != null
                            && run.getFindingCount() >= 0 ? run.getFindingCount() : null)
                    .findings(List.of())
                    .dataAvailable(false)
                    .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                    .build();
        }
    }

    @Override
    @Transactional(readOnly = true)
    public FuzzRunDto getRun(Long userId, Long runId) {
        FuzzTaskPo run = requireOwnedRun(userId, runId);
        return fuzzMapper.toRunDto(run,
                findingRepository.findByUserIdAndFuzzTaskIdOrderByCreatedAtAscIdAsc(userId, runId));
    }

    @Override
    @Transactional
    public void deleteRun(Long userId, Long runId) {
        FuzzTaskPo run = requireOwnedRun(userId, runId);
        findingRepository.deleteByUserIdAndFuzzTaskId(userId, runId);
        taskRepository.delete(run);
    }

    @Override
    @Transactional(readOnly = true)
    public List<FuzzFindingDto> getFindings(Long userId, Long runId) {
        FuzzTaskPo run = requireOwnedRun(userId, runId);
        List<FuzzFindingPo> findings = findingRepository
                .findByUserIdAndFuzzTaskIdOrderByCreatedAtAscIdAsc(userId, runId);
        return fuzzMapper.toRunDto(run, findings).getFindings();
    }

    @Override
    @Transactional(readOnly = true)
    public FuzzFindingDto getFinding(Long userId, Long findingId) {
        FuzzFindingPo finding = findingRepository.findByIdAndUserId(findingId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(
                        "Counterexample search finding", findingId));
        FuzzTaskPo run = requireOwnedRun(userId, finding.getFuzzTaskId());
        return fuzzMapper.toFindingDto(run, finding);
    }

    private FuzzTaskPo requireOwnedTask(Long userId, Long taskId) {
        return taskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(
                        "Counterexample search task", taskId));
    }

    private FuzzTaskPo requireOwnedRun(Long userId, Long runId) {
        return taskRepository.findByIdAndUserIdAndStatus(
                        runId, userId, FuzzTaskPo.TaskStatus.COMPLETED)
                .orElseThrow(() -> new ResourceNotFoundException(
                        "Counterexample search run", runId));
    }

    private List<Long> normalizeExcludedTaskIds(List<Long> excludedTaskIds) {
        if (excludedTaskIds == null || excludedTaskIds.isEmpty()) return List.of();
        if (excludedTaskIds.size() > 100) {
            throw new ValidationException("excludeTaskIds", "At most 100 task IDs can be excluded");
        }
        if (excludedTaskIds.stream().anyMatch(id -> id == null || id <= 0)) {
            throw new ValidationException("excludeTaskIds", "Excluded task IDs must be positive");
        }
        return excludedTaskIds.stream().distinct().toList();
    }

    private Pageable pageRequest(int page, int size, int maximumSize) {
        if (page < 0 || page > 10_000) {
            throw new ValidationException("page", "Page must be between 0 and 10000");
        }
        if (size < 1 || size > maximumSize) {
            throw new ValidationException("size", "Page size must be between 1 and " + maximumSize);
        }
        return PageRequest.of(page, size);
    }

    private void failTaskById(Long taskId, String message) {
        transactionTemplate.executeWithoutResult(status -> {
            taskRepository.findByIdForUpdate(taskId);
            LocalDateTime completedAt = databaseNow();
            taskRepository.failTaskIfActive(
                    taskId,
                    FuzzTaskPo.TaskStatus.FAILED,
                    completedAt,
                    null,
                    truncateOutput(message),
                    serializeCheckLogs(List.of(message)),
                    ACTIVE_STATUSES,
                    workerId,
                    completedAt);
        });
    }

    private void failTask(FuzzTaskPo task, String message) {
        if (task == null) return;
        transactionTemplate.executeWithoutResult(status -> {
            taskRepository.findByIdForUpdate(task.getId());
            LocalDateTime completedAt = databaseNow();
            Long processingTimeMs = task.getStartedAt() == null ? null
                    : Duration.between(task.getStartedAt(), completedAt).toMillis();
            taskRepository.failTaskIfActive(
                    task.getId(),
                    FuzzTaskPo.TaskStatus.FAILED,
                    completedAt,
                    processingTimeMs,
                    truncateOutput(message),
                    serializeCheckLogs(List.of(message)),
                    ACTIVE_STATUSES,
                    workerId,
                    completedAt);
        });
    }

    private boolean isCancelledOrTerminal(Long taskId) {
        if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) return true;
        return taskRepository.findById(taskId)
                .map(FuzzTaskPo::isTerminalStatus)
                .orElse(true);
    }

    private long utf8Length(String value) {
        return value == null ? 0L : value.getBytes(StandardCharsets.UTF_8).length;
    }

    private String serializeFrozenSnapshot(ModelInputSnapshot snapshot, String errorField) {
        String json = JsonUtils.toJson(snapshot);
        if (utf8Length(json) > MAX_MODEL_INPUT_SNAPSHOT_BYTES) {
            throw new ValidationException(
                    errorField, "Frozen Board snapshot exceeds the 8 MiB persistence limit");
        }
        return json;
    }

    private NormalizedRequest executionRequest(FuzzTaskPo task) {
        return new NormalizedRequest(
                JsonUtils.fromJsonToStringList(task.getTargetSpecIdsJson()),
                Objects.requireNonNull(task.getMaxIterations(), "maxIterations is missing"),
                Objects.requireNonNull(task.getPathLength(), "pathLength is missing"),
                Objects.requireNonNull(task.getPopulationSize(), "populationSize is missing"),
                task.getSeed(),
                Objects.requireNonNull(task.getExplorationMode(), "explorationMode is missing"),
                null);
    }

    void requireBoundedRunMetadata(String eligibilityJson, String limitationsJson) {
        long bytes;
        try {
            bytes = Math.addExact(utf8Length(eligibilityJson), utf8Length(limitationsJson));
        } catch (ArithmeticException e) {
            throw new EvidenceLimitExceededException();
        }
        if (bytes > MAX_RUN_METADATA_BYTES) {
            throw new EvidenceLimitExceededException();
        }
    }

    String boundedSingleLine(String value, String fallback, int maxChars) {
        return FuzzMetadataPolicy.boundedSingleLine(value, fallback, maxChars);
    }

    private String publicTaskFailureMessage(Exception error) {
        if (error instanceof EvidenceLimitExceededException) {
            return "Candidate evidence exceeded the persistence safety limit";
        }
        return "Internal counterexample exploration error";
    }

    private void requireActiveUserForPersistence(Long userId) {
        if (userId == null) throw new ValidationException("userId", "User id cannot be null");
        if (userRepository.findByIdForUpdate(userId).isEmpty()) {
            throw ResourceNotFoundException.user(userId);
        }
    }

    @Override
    protected Optional<FuzzTaskPo> findTaskByIdAndUserId(Long id, Long userId) {
        return taskRepository.findByIdAndUserId(id, userId);
    }

    @Override
    protected int atomicCancelTask(Long taskId, LocalDateTime completedAt) {
        return taskRepository.cancelTaskIfStillActive(
                taskId, FuzzTaskPo.TaskStatus.CANCELLED, completedAt, ACTIVE_STATUSES);
    }

    @Override
    protected LocalDateTime currentTaskTime() {
        return databaseNow();
    }

    @Override
    protected int atomicUpdateProgress(Long taskId, int progress, TaskProgressStage stage) {
        return taskRepository.updateProgressIfActive(taskId, progress, stage, workerId, databaseNow());
    }

    @Override
    protected LocalExecutionStopResult stopAdditionalLocalExecution(Long taskId) {
        LocalFuzzExecution execution = localExecutions.get(taskId);
        return execution == null
                ? LocalExecutionStopResult.NONE
                : execution.requestStop();
    }

    private record NormalizedRequest(List<String> targetSpecIds,
                                     int maxIterations,
                                     int pathLength,
                                     int populationSize,
                                     Long seed,
                                     FuzzExplorationMode explorationMode,
                                     String paperDomainFingerprint) {
    }

    private enum LocalExecutionState {
        QUEUED,
        RUNNING,
        CANCELLED_BEFORE_START,
        FINISHED
    }

    private final class LocalFuzzExecution implements Runnable {
        private final Long taskId;
        private final Long userId;
        private final SubmissionCapacityPermit capacityPermit;
        private final AtomicReference<LocalExecutionState> state =
                new AtomicReference<>(LocalExecutionState.QUEUED);
        private final FutureTask<Void> futureTask;

        private LocalFuzzExecution(Long taskId,
                                   Long userId,
                                   SubmissionCapacityPermit capacityPermit) {
            this.taskId = taskId;
            this.userId = userId;
            this.capacityPermit = capacityPermit;
            this.futureTask = new FutureTask<>(this, null);
        }

        @Override
        public void run() {
            if (!state.compareAndSet(LocalExecutionState.QUEUED, LocalExecutionState.RUNNING)) {
                return;
            }
            try {
                runTask(userId, taskId);
            } finally {
                removeCancelledMark(taskId);
                state.set(LocalExecutionState.FINISHED);
                releaseAndForget();
            }
        }

        private boolean isQueued() {
            return state.get() == LocalExecutionState.QUEUED;
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
                    purgeCancelledFuzzTasks();
                    releaseAndForget();
                    return LocalExecutionStopResult.STOPPED_BEFORE_START;
                }
                if (current == LocalExecutionState.RUNNING) {
                    futureTask.cancel(true);
                    return LocalExecutionStopResult.STOP_REQUESTED;
                }
                return LocalExecutionStopResult.NONE;
            }
        }

        private void purgeIfCancelledAfterDispatch() {
            if (futureTask.isCancelled()) purgeCancelledFuzzTasks();
        }

        private void releaseAndForget() {
            capacityPermit.release();
            localExecutions.remove(taskId, this);
        }
    }

    private static final class SubmissionCapacityPermit {
        private final Semaphore capacity;
        private final AtomicBoolean released = new AtomicBoolean(false);

        private SubmissionCapacityPermit(Semaphore capacity) {
            this.capacity = capacity;
        }

        private void release() {
            if (released.compareAndSet(false, true)) capacity.release();
        }
    }

    private static final class EvidenceLimitExceededException extends IllegalStateException {
        private EvidenceLimitExceededException() {
            super("Candidate evidence exceeds the configured persistence safety limit");
        }
    }
}
