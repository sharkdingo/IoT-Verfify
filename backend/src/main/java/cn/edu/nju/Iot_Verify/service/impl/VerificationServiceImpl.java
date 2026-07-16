package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerationContext;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.AsyncTaskAdmissionConfig;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunSummaryDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.AsyncTaskQuotaExceededException;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.repository.VerificationTaskRepository;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.SmvConstants;
import cn.edu.nju.Iot_Verify.util.SpecificationFormulaPreview;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import cn.edu.nju.Iot_Verify.util.mapper.VerificationTaskMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.io.*;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.*;

/**
 * Verification service implementation.
 *
 * Manages sync/async verification flows, task lifecycle, and trace persistence.
 */
@Slf4j
@Service
public class VerificationServiceImpl extends AbstractAsyncTaskService<VerificationTaskPo> implements VerificationService {

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final NusmvConfig nusmvConfig;
    private final VerificationTaskRepository taskRepository;
    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final UserRepository userRepository;
    private final SpecificationMapper specificationMapper;
    private final VerificationTaskMapper verificationTaskMapper;
    private final ThreadPoolTaskExecutor verificationTaskExecutor;
    private final ThreadPoolTaskExecutor syncVerificationExecutor;
    private final TransactionTemplate transactionTemplate;
    private final AsyncTaskAdmissionConfig.Limits taskAdmissionLimits;

    @Autowired
    public VerificationServiceImpl(SmvGenerator smvGenerator,
                                   SmvTraceParser smvTraceParser,
                                   NusmvExecutor nusmvExecutor,
                                   NusmvConfig nusmvConfig,
                                   VerificationTaskRepository taskRepository,
                                   TraceRepository traceRepository,
                                   TraceMapper traceMapper,
                                   UserRepository userRepository,
                                   SpecificationMapper specificationMapper,
                                   VerificationTaskMapper verificationTaskMapper,
                                   ObjectMapper objectMapper,
                                   @Qualifier("verificationTaskExecutor") ThreadPoolTaskExecutor verificationTaskExecutor,
                                   @Qualifier("syncVerificationExecutor") ThreadPoolTaskExecutor syncVerificationExecutor,
                                   TransactionTemplate transactionTemplate,
                                   AsyncTaskAdmissionConfig taskAdmissionConfig) {
        super(objectMapper, "VerificationTask");
        this.smvGenerator = smvGenerator;
        this.smvTraceParser = smvTraceParser;
        this.nusmvExecutor = nusmvExecutor;
        this.nusmvConfig = nusmvConfig;
        this.taskRepository = taskRepository;
        this.traceRepository = traceRepository;
        this.traceMapper = traceMapper;
        this.userRepository = userRepository;
        this.specificationMapper = specificationMapper;
        this.verificationTaskMapper = verificationTaskMapper;
        this.verificationTaskExecutor = verificationTaskExecutor;
        this.syncVerificationExecutor = syncVerificationExecutor;
        this.transactionTemplate = transactionTemplate;
        this.taskAdmissionLimits = taskAdmissionConfig.getVerification();
    }

    VerificationServiceImpl(SmvGenerator smvGenerator,
                            SmvTraceParser smvTraceParser,
                            NusmvExecutor nusmvExecutor,
                            NusmvConfig nusmvConfig,
                            VerificationTaskRepository taskRepository,
                            TraceRepository traceRepository,
                            TraceMapper traceMapper,
                            UserRepository userRepository,
                            SpecificationMapper specificationMapper,
                            VerificationTaskMapper verificationTaskMapper,
                            ObjectMapper objectMapper,
                            ThreadPoolTaskExecutor verificationTaskExecutor,
                            ThreadPoolTaskExecutor syncVerificationExecutor,
                            TransactionTemplate transactionTemplate) {
        this(smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig, taskRepository,
                traceRepository, traceMapper, userRepository, specificationMapper,
                verificationTaskMapper, objectMapper, verificationTaskExecutor,
                syncVerificationExecutor, transactionTemplate, new AsyncTaskAdmissionConfig());
    }

    @PostConstruct
    void cleanupStaleTasks() {
        List<VerificationTaskPo> staleTasks = taskRepository.findByStatusIn(
                List.of(VerificationTaskPo.TaskStatus.RUNNING, VerificationTaskPo.TaskStatus.PENDING));
        if (!staleTasks.isEmpty()) {
            log.warn("Found {} stale tasks on startup, marking as FAILED", staleTasks.size());
            String msg = "Server restarted while task was in progress";
            for (VerificationTaskPo task : staleTasks) {
                task.setStatus(VerificationTaskPo.TaskStatus.FAILED);
                task.setProgress(100);
                task.setCompletedAt(LocalDateTime.now());
                task.setOutcome(VerificationOutcome.INCONCLUSIVE);
                task.setErrorMessage(msg);
                writeCheckLogs(task, List.of(msg));
                taskRepository.save(task);
            }
        }
    }

    // ==================== 同步验证 ====================

    @Override
    public VerificationResultDto verify(Long userId, VerificationRequestDto request) {
        return verifyInput(userId, validateAndNormalize(userId, request));
    }

    @Override
    public VerificationResultDto verifyWithTemplateSnapshot(
            Long userId,
            VerificationRequestDto request,
            Map<String, DeviceManifest> templateManifests) {
        return verifyInput(userId, validateAndNormalize(userId, request, templateManifests));
    }

    private VerificationResultDto verifyInput(Long userId, VerificationInput input) {

        log.info("Starting sync verification: userId={}, devices={}, specs={}, attack={}, attackBudget={}",
                userId, input.devices().size(), input.specs().size(), input.attack(), input.attackBudget());

        LocalDateTime startedAt = LocalDateTime.now();
        long timeoutMs = nusmvConfig.getTimeoutMs() * 2; // generate + execute total timeout
        Future<VerificationResultDto> future;
        try {
            future = syncVerificationExecutor.submit(() ->
                    doVerify(userId, input.devices(), input.rules(), input.specs(),
                            input.attack(), input.attackBudget(), input.enablePrivacy(), input.request(),
                            input.deviceSmvMap(), input.templateManifests(), input.modelSnapshot(),
                            SmvGenerator.TempModelContext.sync()));
        } catch (RejectedExecutionException e) {
            log.warn("Sync verification request rejected: executor is saturated ({})", syncVerificationExecutorSnapshot());
            throw new ServiceUnavailableException("Verification service is busy, please retry later", e);
        }

        VerificationResultDto result;
        try {
            result = future.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            future.cancel(true);
            purgeCancelledSyncTasks();
            log.warn("Sync verification timed out after {}ms", timeoutMs);
            result = applyRunContext(buildErrorResult("", List.of("Verification timed out")),
                    input.attack(), input.attackBudget(), input.enablePrivacy(),
                    input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                    input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(),
                    JsonUtils.toJson(input.templateManifests()));
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            if (cause instanceof ServiceUnavailableException sue) throw sue;
            if (cause instanceof SmvGenerationException sge) throw sge;
            log.error("Sync verification failed", cause);
            throw new InternalServerException("Verification failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            result = applyRunContext(buildErrorResult("", List.of("Verification interrupted")),
                    input.attack(), input.attackBudget(), input.enablePrivacy(),
                    input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                    input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(),
                    JsonUtils.toJson(input.templateManifests()));
        }
        try {
            Long runId = persistCompletedVerificationRun(userId, input, result, startedAt);
            result.setHistoryPersistence(RunPersistenceDto.saved(runId));
        } catch (RuntimeException e) {
            log.error("Verification completed but could not be added to run history for user {}", userId, e);
            result.setHistoryPersistence(RunPersistenceDto.outcomeUnknown("RUN_HISTORY_SAVE_OUTCOME_UNKNOWN"));
            List<String> logs = result.getCheckLogs() != null
                    ? new ArrayList<>(result.getCheckLogs()) : new ArrayList<>();
            logs.add("[history-save-unknown] Verification completed, but whether it entered run history could not be confirmed.");
            result.setCheckLogs(logs);
        }
        return result;
    }

    private VerificationResultDto doVerify(Long userId,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           List<SpecificationDto> specs,
                                            boolean isAttack, int attackBudget,
                                            boolean enablePrivacy,
                                            VerificationRequestDto request,
                                            Map<String, DeviceSmvData> resolvedDeviceSmvMap,
                                            Map<String, DeviceManifest> templateManifests,
                                            ModelRunSnapshotDto modelSnapshot,
                                            SmvGenerator.TempModelContext tempModelContext) {
        List<String> checkLogs = new ArrayList<>();
        File smvFile = null;
        Map<String, DeviceSmvData> deviceSmvMap = null;
        AttackSurface attackSurface = new AttackSurface(Set.of(), rules != null ? rules.size() : 0, 0);
        VerificationResultDto finalResult = null;
        String requestJson = buildRequestSnapshot(request);
        String templateSnapshotsJson = JsonUtils.toJson(templateManifests);

        try {
            checkLogs.add("Generating NuSMV model...");
            SmvGenerator.GenerateResult genResult = smvGenerator.generateWithResolvedDeviceModel(
                    userId, devices, request.getEnvironmentVariables(), rules, specs,
                    isAttack, attackBudget, enablePrivacy, SmvGenerator.GeneratePurpose.VERIFICATION,
                    tempModelContext, resolvedDeviceSmvMap);
            smvFile = genResult.smvFile();
            deviceSmvMap = genResult.deviceSmvMap();
            attackSurface = AttackSurface.analyze(rules, deviceSmvMap);
            appendGenerationWarnings(checkLogs, genResult);
            if (smvFile == null || !smvFile.exists()) {
                checkLogs.add("Failed to generate NuSMV model file");
                finalResult = buildErrorResult("", checkLogs);
                return finalResult;
            }
            checkLogs.add("Model generated: " + smvFile.getName());
            saveRequestJson(smvFile, requestJson);

            checkLogs.add("Executing NuSMV verification...");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (!result.isSuccess()) {
                if (result.isBusy()) {
                    checkLogs.add("NuSMV execution is busy, please retry later");
                    finalResult = buildErrorResult("", checkLogs);
                    throw new ServiceUnavailableException("NuSMV verification service is busy, please retry later");
                }
                checkLogs.add("NuSMV execution failed: " + result.getErrorMessage());
                finalResult = buildErrorResult("", checkLogs);
                return finalResult;
            }
            checkLogs.add("NuSMV execution completed.");

            // Build per-spec results and reuse deviceSmvMap from generation stage.
            finalResult = buildVerificationResult(result, devices, rules, specs, userId, null, checkLogs, deviceSmvMap,
                    templateManifests,
                    requestJson, genResult.emittedSpecs(), genResult.generationIssues(),
                    genResult.disabledRuleCount(), genResult.skippedSpecCount());
            applyRunContext(finalResult, isAttack, attackBudget, enablePrivacy,
                    attackSurface.deviceCount(), attackSurface.automationLinkCount(),
                    attackSurface.falsifiableReadingDeviceCount(), modelSnapshot, templateSnapshotsJson);
            return finalResult;

        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) Thread.currentThread().interrupt();
            log.error("Verification error", e);
            checkLogs.add("Error: " + e.getMessage());
            finalResult = buildErrorResult("", checkLogs);
            return finalResult;
        } catch (ServiceUnavailableException e) {
            throw e;
        } catch (SmvGenerationException e) {
            log.error("SMV generation failed", e);
            checkLogs.add("Error: " + e.getMessage());
            finalResult = buildErrorResult("", checkLogs);
            throw e;
        } catch (Exception e) {
            log.error("Verification failed", e);
            checkLogs.add("Error: " + e.getMessage());
            finalResult = buildErrorResult("", checkLogs);
            throw new InternalServerException("Verification failed: " + e.getMessage());
        } finally {
            // Persist result.json when tempDir exists (both success and failure) for debugging.
            if (finalResult != null) {
                applyRunContext(finalResult, isAttack, attackBudget, enablePrivacy,
                        attackSurface.deviceCount(), attackSurface.automationLinkCount(),
                        attackSurface.falsifiableReadingDeviceCount(), modelSnapshot, templateSnapshotsJson);
                saveResultJson(smvFile, finalResult);
            }
            cleanupTempFile(smvFile);
        }
    }

    private void saveResultJson(File smvFile, VerificationResultDto verificationResult) {
        if (smvFile == null || smvFile.getParentFile() == null) return;
        try {
            File jsonFile = new File(smvFile.getParentFile(), "result.json");
            Result<VerificationResultDto> wrapped = wrapResultForDebugFile(verificationResult);
            byte[] payload = objectMapper.writerWithDefaultPrettyPrinter().writeValueAsBytes(wrapped);
            java.nio.file.Files.write(jsonFile.toPath(), payload);
            log.debug("Verification result JSON saved to: {}", jsonFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save result JSON: {}", e.getMessage());
        }
    }

    private void saveRequestJson(File smvFile, String requestJson) {
        if (smvFile == null || smvFile.getParentFile() == null || requestJson == null || requestJson.isBlank()) return;
        try {
            File jsonFile = new File(smvFile.getParentFile(), "request.json");
            objectMapper.writerWithDefaultPrettyPrinter()
                    .writeValue(jsonFile, objectMapper.readTree(requestJson));
            log.debug("Verification request JSON saved to: {}", jsonFile.getAbsolutePath());
        } catch (IOException e) {
            log.warn("Failed to save verification request JSON: {}", e.getMessage());
        }
    }

    private void appendGenerationWarnings(List<String> checkLogs, SmvGenerator.GenerateResult genResult) {
        if (checkLogs == null || genResult == null || genResult.generationWarnings() == null
                || genResult.generationWarnings().isEmpty()) {
            return;
        }
        checkLogs.addAll(genResult.generationWarnings());
    }

    private String buildRequestSnapshot(VerificationRequestDto request) {
        return JsonUtils.toJson(request);
    }

    private VerificationInput validateAndNormalize(Long userId, VerificationRequestDto request) {
        return validateAndNormalize(userId, request, null);
    }

    private VerificationInput validateAndNormalize(
            Long userId,
            VerificationRequestDto request,
            Map<String, DeviceManifest> suppliedTemplateManifests) {
        if (request == null) {
            throw new ValidationException("request", "Verification request cannot be null");
        }
        VerificationRequestDto snapshot = snapshotRequest(request);
        List<DeviceVerificationDto> devices = copyRequiredList(
                snapshot.getDevices(), "devices", "Devices list cannot be empty");
        List<SpecificationDto> specs = copyRequiredList(
                snapshot.getSpecs(), "specs", "Specs list cannot be empty");
        List<RuleDto> rules = copyOptionalList(snapshot.getRules(), "rules");
        List<BoardEnvironmentVariableDto> environmentVariables = copyOptionalList(
                snapshot.getEnvironmentVariables(), "environmentVariables");
        int attackBudget = snapshot.getAttackBudget();
        if (attackBudget < 0 || attackBudget > 50) {
            throw new ValidationException("attackBudget", "Attack budget must be between 0 and 50");
        }
        if (snapshot.isAttack() && attackBudget < 1) {
            throw new ValidationException("attackBudget",
                    "Attack budget must be at least 1 when attack modeling is enabled");
        }
        if (!snapshot.isAttack() && attackBudget != 0) {
            throw new ValidationException("attackBudget",
                    "Attack budget must be 0 when attack modeling is disabled");
        }
        int effectiveAttackBudget = snapshot.isAttack() ? attackBudget : 0;
        snapshot.setDevices(devices);
        snapshot.setRules(rules);
        snapshot.setSpecs(specs);
        snapshot.setEnvironmentVariables(environmentVariables);
        snapshot.setAttackBudget(effectiveAttackBudget);
        snapshot.setEnablePrivacy(snapshot.isEnablePrivacy() || specificationsRequirePrivacy(specs));

        Map<String, String> errors = NusmvRequestValidator.newErrors();
        NusmvRequestValidator.validateDevices(devices, errors);
        NusmvRequestValidator.validateRules(rules, devices, errors);
        NusmvRequestValidator.validateSpecifications(specs, devices, errors);
        ModelBoundaryInput modelInput = validateModelSemantics(
                userId, devices, rules, specs, environmentVariables, snapshot.isAttack(),
                suppliedTemplateManifests, errors);
        snapshot.setEnvironmentVariables(modelInput.environmentVariables());
        NusmvRequestValidator.throwIfErrors(errors);

        AttackSurface attackSurface = modelInput.attackSurface();
        if (snapshot.isAttack() && attackBudget > attackSurface.totalCount()) {
            throw new ValidationException("attackBudget",
                    "Attack budget cannot exceed the behavior-changing device and automation-link points ("
                            + attackSurface.totalCount() + ")");
        }

        return new VerificationInput(modelInput.devices(), rules, specs, snapshot.isAttack(), effectiveAttackBudget,
                snapshot.isEnablePrivacy(), attackSurface.deviceCount(), attackSurface.automationLinkCount(),
                attackSurface.falsifiableReadingDeviceCount(), snapshot, modelInput.deviceSmvMap(),
                modelInput.templateManifests(), modelInput.modelSnapshot());
    }

    private boolean specificationsRequirePrivacy(List<SpecificationDto> specs) {
        if (specs == null) {
            return false;
        }
        return specs.stream()
                .filter(Objects::nonNull)
                .flatMap(spec -> java.util.stream.Stream.of(
                        spec.getAConditions(), spec.getIfConditions(), spec.getThenConditions()))
                .filter(Objects::nonNull)
                .flatMap(Collection::stream)
                .filter(Objects::nonNull)
                .map(SpecConditionDto::getTargetType)
                .anyMatch(type -> "privacy".equalsIgnoreCase(type));
    }

    private VerificationResultDto applyModelContext(VerificationResultDto result,
                                                     boolean isAttack,
                                                     int attackBudget,
                                                     boolean enablePrivacy,
                                                     int deviceCount,
                                                     int automationLinkCount,
                                                     int falsifiableReadingDeviceCount) {
        if (result == null) {
            return null;
        }
        result.setIsAttack(isAttack);
        result.setAttackBudget(isAttack ? attackBudget : 0);
        result.setEnablePrivacy(enablePrivacy);
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                isAttack, enablePrivacy, deviceCount, automationLinkCount,
                falsifiableReadingDeviceCount);
        result.setModelSemantics(semantics);
        if (result.getTraces() != null) {
            for (TraceDto trace : result.getTraces()) {
                trace.setAttack(isAttack);
                trace.setAttackBudget(isAttack ? attackBudget : 0);
                trace.setEnablePrivacy(enablePrivacy);
                trace.setModelSemantics(semantics);
            }
        }
        return result;
    }

    private VerificationResultDto applyRunContext(VerificationResultDto result,
                                                   boolean isAttack,
                                                   int attackBudget,
                                                   boolean enablePrivacy,
                                                   int deviceCount,
                                                   int automationLinkCount,
                                                   int falsifiableReadingDeviceCount,
                                                   ModelRunSnapshotDto modelSnapshot,
                                                   String templateSnapshotsJson) {
        applyModelContext(result, isAttack, attackBudget, enablePrivacy,
                deviceCount, automationLinkCount, falsifiableReadingDeviceCount);
        if (result == null) {
            return null;
        }
        result.setModelSnapshot(modelSnapshot);
        if (result.getTraces() != null) {
            for (TraceDto trace : result.getTraces()) {
                trace.setModelSnapshot(modelSnapshot);
                trace.setTemplateSnapshotsJson(templateSnapshotsJson);
            }
        }
        return result;
    }

    private ModelBoundaryInput validateModelSemantics(Long userId,
                                                      List<DeviceVerificationDto> devices,
                                                      List<RuleDto> rules,
                                                      List<SpecificationDto> specs,
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
            NusmvRequestValidator.validateSpecificationSemantics(specs, deviceSmvMap, errors);
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
                    specs != null ? specs.size() : 0,
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

    private VerificationRequestDto snapshotRequest(VerificationRequestDto request) {
        try {
            return objectMapper.convertValue(request, VerificationRequestDto.class);
        } catch (IllegalArgumentException e) {
            throw new ValidationException("request", "Verification request cannot be snapshotted");
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

    private Result<VerificationResultDto> wrapResultForDebugFile(VerificationResultDto verificationResult) {
        Result<VerificationResultDto> wrapped = new Result<>();
        wrapped.setData(verificationResult);
        if (isVerificationFailureResult(verificationResult)) {
            wrapped.setCode(inferVerificationErrorCode(verificationResult));
            wrapped.setMessage(inferVerificationErrorMessage(verificationResult));
        } else {
            wrapped.setCode(200);
            wrapped.setMessage("success");
        }
        return wrapped;
    }

    private boolean isVerificationFailureResult(VerificationResultDto result) {
        if (result == null) return true;
        if (result.getOutcome() == VerificationOutcome.INCONCLUSIVE) return true;
        boolean hasSpecResults = result.getSpecResults() != null && !result.getSpecResults().isEmpty();
        boolean hasTraces = result.getTraces() != null && !result.getTraces().isEmpty();
        if (hasSpecResults || hasTraces) return false;
        return result.getOutcome() != VerificationOutcome.SATISFIED;
    }

    private int inferVerificationErrorCode(VerificationResultDto result) {
        List<String> logs = result != null ? result.getCheckLogs() : null;
        if (logs != null) {
            for (String logLine : logs) {
                if (logLine != null && logLine.toLowerCase().contains("busy")) {
                    return 503;
                }
            }
        }
        return 500;
    }

    private String inferVerificationErrorMessage(VerificationResultDto result) {
        List<String> logs = result != null ? result.getCheckLogs() : null;
        if (logs != null && !logs.isEmpty()) {
            String last = logs.get(logs.size() - 1);
            if (last != null && !last.isBlank()) {
                return last;
            }
        }
        return "verification failed";
    }

    // ==================== 异步验证 ====================

    @Override
    public Long submitVerification(Long userId, VerificationRequestDto request) {
        return submitVerificationInput(userId, validateAndNormalize(userId, request));
    }

    @Override
    public Long submitVerificationWithTemplateSnapshot(
            Long userId,
            VerificationRequestDto request,
            Map<String, DeviceManifest> templateManifests) {
        return submitVerificationInput(
                userId, validateAndNormalize(userId, request, templateManifests));
    }

    private Long submitVerificationInput(Long userId, VerificationInput input) {
        Long taskId = createTask(userId, input.attack(), input.attackBudget(), input.enablePrivacy(),
                input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot());
        try {
            enqueueVerificationTask(userId, taskId, input);
        } catch (TaskRejectedException e) {
            log.warn("Verification task {} rejected: thread pool full", taskId);
            failTaskById(taskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later", e);
        }
        return taskId;
    }

    // Service-internal: task creation is only reachable through submitVerification and
    // the package-private async path below; it is no longer part of the public interface.
    @Transactional
    Long createTask(Long userId,
                    boolean isAttack,
                    int attackBudget,
                    boolean enablePrivacy,
                    int devicePointCount,
                    int linkPointCount,
                    int falsifiableReadingDeviceCount,
                    ModelRunSnapshotDto modelSnapshot) {
        return transactionTemplate.execute(status -> {
            requireActiveUserForTracePersistence(userId);
            long storedTaskCount = taskRepository.countByUserId(userId);
            if (storedTaskCount >= taskAdmissionLimits.getMaxStoredTasksPerUser()) {
                throw new AsyncTaskQuotaExceededException(
                        "verification", AsyncTaskQuotaExceededException.QuotaType.STORED,
                        storedTaskCount, taskAdmissionLimits.getMaxStoredTasksPerUser());
            }
            long activeTaskCount = taskRepository.countByUserIdAndStatusIn(
                    userId, List.of(VerificationTaskPo.TaskStatus.PENDING, VerificationTaskPo.TaskStatus.RUNNING));
            if (activeTaskCount >= taskAdmissionLimits.getMaxActiveTasksPerUser()) {
                throw new AsyncTaskQuotaExceededException(
                        "verification", AsyncTaskQuotaExceededException.QuotaType.ACTIVE,
                        activeTaskCount, taskAdmissionLimits.getMaxActiveTasksPerUser());
            }
            VerificationTaskPo task = VerificationTaskPo.builder()
                    .userId(userId)
                    .status(VerificationTaskPo.TaskStatus.PENDING)
                    .isAttack(isAttack)
                    .attackBudget(attackBudget)
                    .modeledDeviceAttackPointCount(devicePointCount)
                    .modeledFalsifiableReadingDeviceCount(falsifiableReadingDeviceCount)
                    .modeledAutomationLinkAttackPointCount(linkPointCount)
                    .enablePrivacy(enablePrivacy)
                    .modelSnapshotJson(JsonUtils.toJson(modelSnapshot))
                    .createdAt(LocalDateTime.now())
                    .build();
            VerificationTaskPo saved = taskRepository.save(Objects.requireNonNull(task));
            log.info("Created verification task: {} for user: {}", saved.getId(), userId);
            return Objects.requireNonNull(saved.getId());
        });
    }

    // Service-internal failure compensation, reachable only from the submit/async paths below.
    @Transactional
    void failTaskById(Long taskId, String errorMessage) {
        taskRepository.findById(Objects.requireNonNull(taskId, "taskId must not be null"))
                .ifPresent(task -> failTask(task, errorMessage));
    }

    // Package-private async entry: assumes the caller already created the task and passes a
    // non-null taskId. Production code goes through submitVerification; retained at this
    // visibility so same-package tests can drive the "execute with a fixed taskId" path.
    void verifyAsync(Long userId, Long taskId, VerificationRequestDto request) {
        Long requiredTaskId = requireTaskId(taskId);
        VerificationInput input;
        try {
            input = validateAndNormalize(userId, request);
        } catch (ValidationException e) {
            failTaskById(requiredTaskId, e.getMessage());
            throw e;
        }
        try {
            persistTaskModelContext(requiredTaskId, input.attack(), input.attackBudget(), input.enablePrivacy(),
                    input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                    input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot());
            enqueueVerificationTask(userId, requiredTaskId, input);
        } catch (TaskRejectedException e) {
            failTaskById(requiredTaskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later", e);
        }
    }

    private void enqueueVerificationTask(Long userId, Long taskId, VerificationInput input) {
        Long requiredTaskId = requireTaskId(taskId);
        VerificationInput requiredInput = Objects.requireNonNull(input, "verification input must not be null");
        verificationTaskExecutor.execute(() -> runVerificationTask(userId, requiredTaskId, requiredInput));
    }

    private Long requireTaskId(Long taskId) {
        if (taskId == null) {
            throw new ValidationException("taskId", "Task id cannot be null");
        }
        return taskId;
    }

    private void runVerificationTask(Long userId, Long taskId, VerificationInput input) {
        String requestJson = buildRequestSnapshot(input.request());
        String templateSnapshotsJson = JsonUtils.toJson(input.templateManifests());
        log.info("Starting async verification task: {} for user: {}", taskId, userId);

        registerRunningTask(taskId, Thread.currentThread());
        updateTaskProgress(taskId, 0, "Task started");

        File smvFile = null;
        VerificationTaskPo task = null;
        VerificationResultDto finalResult = null;
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
            int updated = taskRepository.startTaskIfStillPending(
                    taskId,
                    VerificationTaskPo.TaskStatus.RUNNING,
                    startedAt, 0, startCheckLogs,
                    VerificationTaskPo.TaskStatus.PENDING);
            if (updated == 0) {
                log.info("Task {} is no longer PENDING (cancelled or already started), aborting", taskId);
                return;
            }

            // Load entity for subsequent use (failTask/completeTask only need id and startedAt).
            task = taskRepository.findById(Objects.requireNonNull(taskId)).orElse(null);
            if (task == null) {
                log.error("Task not found after atomic start: {}", taskId);
                return;
            }

            updateTaskProgress(taskId, 20, "Generating NuSMV model");
            SmvGenerator.GenerateResult genResult = smvGenerator.generateWithResolvedDeviceModel(
                    userId, input.devices(), input.request().getEnvironmentVariables(), input.rules(), input.specs(),
                    input.attack(), input.attackBudget(), input.enablePrivacy(), SmvGenerator.GeneratePurpose.VERIFICATION,
                    SmvGenerator.TempModelContext.task(taskId), input.deviceSmvMap());
            smvFile = genResult.smvFile();
            Map<String, DeviceSmvData> deviceSmvMap = genResult.deviceSmvMap();
            List<String> checkLogs = new ArrayList<>();
            checkLogs.add("Generating NuSMV model...");
            appendGenerationWarnings(checkLogs, genResult);
            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }
            if (smvFile == null || !smvFile.exists()) {
                String msg = "Failed to generate NuSMV model file";
                failTask(task, msg);
                finalResult = buildErrorResult("", List.of(msg));
                return;
            }
            checkLogs.add("Model generated: " + smvFile.getName());
            saveRequestJson(smvFile, requestJson);


            updateTaskProgress(taskId, 50, "Executing NuSMV");
            checkLogs.add("Executing NuSMV verification...");
            NusmvResult result = nusmvExecutor.execute(smvFile);

            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }

            if (!result.isSuccess()) {
                String msg = "NuSMV execution failed: " + result.getErrorMessage();
                failTask(task, msg);
                finalResult = buildErrorResult("", List.of(msg));
                return;
            }
            checkLogs.add("NuSMV execution completed.");

            updateTaskProgress(taskId, 80, "Parsing results");
            finalResult = buildVerificationResult(
                    result, input.devices(), input.rules(), input.specs(), userId, taskId, checkLogs, deviceSmvMap,
                    input.templateManifests(), requestJson,
                    genResult.emittedSpecs(), genResult.generationIssues(),
                    genResult.disabledRuleCount(), genResult.skippedSpecCount());
            applyRunContext(finalResult, input.attack(), input.attackBudget(), input.enablePrivacy(),
                    input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                    input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(), templateSnapshotsJson);

            if (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted()) {
                return;
            }

            boolean completed = completeTaskAndSaveTraces(task, finalResult.getTraces(), userId, taskId, finalResult.getOutcome(),
                    countViolatedSpecs(finalResult.getSpecResults(), finalResult.getTraces()),
                    finalResult.getSpecResults(), finalResult.getCheckLogs(), truncateOutput(result.getOutput()),
                    finalResult.getGenerationIssues(),
                    finalResult.getDisabledRuleCount(), finalResult.getSkippedSpecCount());
            if (!completed && !isCompletionCancelled(taskId)) {
                failTask(task, "RESULT_PERSISTENCE_FAILED: Verification finished, but its result could not be saved.");
            }

        } catch (Exception e) {
            if (isTaskCancelled(taskId)) {
                // Exceptions caused by cancellation are handled in finally.
                log.info("Async verification cancelled for task: {}", taskId);
            } else {
                String msg = "Verification failed: " + e.getMessage();
                log.error("Async verification failed for task: {}", taskId, e);
                failTask(task, msg);
                finalResult = buildErrorResult("", List.of(msg));
            }
        } finally {
            if (finalResult != null) {
                applyRunContext(finalResult, input.attack(), input.attackBudget(), input.enablePrivacy(),
                        input.modeledDeviceAttackPointCount(), input.modeledAutomationLinkAttackPointCount(),
                        input.modeledFalsifiableReadingDeviceCount(), input.modelSnapshot(), templateSnapshotsJson);
                saveResultJson(smvFile, finalResult);
            }
            cleanupTempFile(smvFile);
            // Unified cancellation handling.
            if (removeCancelledMark(taskId)) {
                if (task != null) handleCancellation(task);
            }
            removeRunningTask(taskId);
            removeTaskProgress(taskId);
        }
    }

    private record VerificationInput(List<DeviceVerificationDto> devices,
                                     List<RuleDto> rules,
                                     List<SpecificationDto> specs,
                                     boolean attack,
                                     int attackBudget,
                                     boolean enablePrivacy,
                                     int modeledDeviceAttackPointCount,
                                     int modeledAutomationLinkAttackPointCount,
                                     int modeledFalsifiableReadingDeviceCount,
                                     VerificationRequestDto request,
                                     Map<String, DeviceSmvData> deviceSmvMap,
                                     Map<String, DeviceManifest> templateManifests,
                                     ModelRunSnapshotDto modelSnapshot) {}

    private record ModelBoundaryInput(List<DeviceVerificationDto> devices,
                                       List<BoardEnvironmentVariableDto> environmentVariables,
                                       AttackSurface attackSurface,
                                       Map<String, DeviceSmvData> deviceSmvMap,
                                       Map<String, DeviceManifest> templateManifests,
                                       ModelRunSnapshotDto modelSnapshot) {}

    // ==================== 查询方法 ====================

    @Override
    @Transactional(readOnly = true)
    public VerificationTaskDto getTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("VerificationTask", taskId));
        task.setCheckLogs(readCheckLogs(task));
        return verificationTaskMapper.toDto(task);
    }

    @Override
    @Transactional(readOnly = true)
    public List<VerificationTaskSummaryDto> getTasks(Long userId, List<Long> excludedTaskIds) {
        List<Long> normalizedExcludedIds = normalizeExcludedTaskIds(excludedTaskIds);
        List<VerificationTaskPo> tasks = normalizedExcludedIds.isEmpty()
                ? taskRepository.findByUserIdAndStatusNotOrderByCreatedAtDesc(
                        userId, VerificationTaskPo.TaskStatus.COMPLETED)
                : taskRepository.findByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDesc(
                        userId, VerificationTaskPo.TaskStatus.COMPLETED, normalizedExcludedIds);
        return verificationTaskMapper.toSummaryDtoList(
                tasks);
    }

    @Override
    @Transactional
    public void deleteTask(Long userId, Long taskId) {
        VerificationTaskPo task = taskRepository.findByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("VerificationTask", taskId));
        if (task.getStatus() == VerificationTaskPo.TaskStatus.PENDING
                || task.getStatus() == VerificationTaskPo.TaskStatus.RUNNING) {
            throw new BadRequestException("An active verification task must be cancelled before it can be removed");
        }
        if (task.getStatus() == VerificationTaskPo.TaskStatus.COMPLETED) {
            throw new BadRequestException("Completed verification results must be removed from run history");
        }
        taskRepository.delete(Objects.requireNonNull(task));
    }

    @Override
    @Transactional(readOnly = true)
    public List<VerificationRunSummaryDto> getRuns(Long userId) {
        Map<Long, List<TraceSummaryDto>> tracesByRun = new LinkedHashMap<>();
        for (TracePo trace : traceRepository.findByUserIdOrderByCreatedAtDesc(userId)) {
            if (trace == null || trace.getVerificationTaskId() == null) continue;
            tracesByRun.computeIfAbsent(trace.getVerificationTaskId(), ignored -> new ArrayList<>())
                    .add(toTraceSummaryOrUnavailable(trace));
        }
        return taskRepository.findByUserIdAndStatusOrderByCompletedAtDesc(
                        userId, VerificationTaskPo.TaskStatus.COMPLETED).stream()
                .map(run -> toRunSummaryOrUnavailable(
                        run, tracesByRun.getOrDefault(run.getId(), List.of())))
                .toList();
    }

    private VerificationRunSummaryDto toRunSummaryOrUnavailable(
            VerificationTaskPo run, List<TraceSummaryDto> counterexamples) {
        try {
            VerificationRunSummaryDto summary = verificationTaskMapper.toRunSummaryDto(
                    run, counterexamples.size());
            summary.setCounterexamples(List.copyOf(counterexamples));
            summary.setDataAvailable(true);
            return summary;
        } catch (RuntimeException e) {
            log.error("Verification history item {} is unavailable because persisted data is invalid",
                    run != null ? run.getId() : null, e);
            return VerificationRunSummaryDto.builder()
                    .id(run != null ? run.getId() : null)
                    .createdAt(run != null ? run.getCreatedAt() : null)
                    .startedAt(run != null ? run.getStartedAt() : null)
                    .completedAt(run != null ? run.getCompletedAt() : null)
                    .processingTimeMs(run != null ? run.getProcessingTimeMs() : null)
                    .counterexampleCount(counterexamples.size())
                    .counterexamples(List.copyOf(counterexamples))
                    .dataAvailable(false)
                    .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                    .build();
        }
    }

    private TraceSummaryDto toTraceSummaryOrUnavailable(TracePo trace) {
        try {
            return traceMapper.toSummaryDto(trace);
        } catch (RuntimeException e) {
            log.error("Verification trace summary {} is unavailable because persisted data is invalid",
                    trace != null ? trace.getId() : null, e);
            return TraceSummaryDto.builder()
                    .id(trace != null ? trace.getId() : null)
                    .verificationTaskId(trace != null ? trace.getVerificationTaskId() : null)
                    .violatedSpecId(trace != null ? trace.getViolatedSpecId() : null)
                    .createdAt(trace != null ? trace.getCreatedAt() : null)
                    .dataAvailable(false)
                    .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                    .build();
        }
    }

    @Override
    @Transactional(readOnly = true)
    public VerificationRunDto getRun(Long userId, Long runId) {
        VerificationTaskPo run = getCompletedRun(userId, runId);
        run.setCheckLogs(readCheckLogs(run));
        return verificationTaskMapper.toRunDto(run, counterexampleCount(userId, runId));
    }

    @Override
    @Transactional(readOnly = true)
    public List<TraceDto> getRunTraces(Long userId, Long runId) {
        getCompletedRun(userId, runId);
        return traceMapper.toDtoList(traceRepository.findByUserIdAndVerificationTaskId(userId, runId));
    }

    @Override
    @Transactional
    public void deleteRun(Long userId, Long runId) {
        VerificationTaskPo run = getCompletedRun(userId, runId);
        traceRepository.deleteByUserIdAndVerificationTaskId(userId, runId);
        taskRepository.delete(Objects.requireNonNull(run));
    }

    private VerificationTaskPo getCompletedRun(Long userId, Long runId) {
        VerificationTaskPo run = taskRepository.findByIdAndUserId(runId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("VerificationRun", runId));
        if (run.getStatus() != VerificationTaskPo.TaskStatus.COMPLETED) {
            throw new ResourceNotFoundException("VerificationRun", runId);
        }
        return run;
    }

    private int counterexampleCount(Long userId, Long runId) {
        long count = traceRepository.countByUserIdAndVerificationTaskId(userId, runId);
        return count > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) count;
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
    public List<TraceDto> getUserTraces(Long userId) {
        return traceMapper.toDtoList(traceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
    @Transactional(readOnly = true)
    public List<TraceDto> getTracesByTask(Long userId, Long taskId) {
        return traceMapper.toDtoList(traceRepository.findByUserIdAndVerificationTaskId(userId, taskId));
    }

    @Override
    @Transactional(readOnly = true)
    public TraceDto getTrace(Long userId, Long traceId) {
        return traceRepository.findByIdAndUserId(traceId, userId)
                .map(traceMapper::toDto)
                .orElseThrow(() -> new ResourceNotFoundException("Trace", traceId));
    }

    @Override
    @Transactional
    public void deleteTrace(Long userId, Long traceId) {
        TracePo trace = traceRepository.findByIdAndUserId(traceId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("Trace", traceId));
        traceRepository.delete(Objects.requireNonNull(trace));
    }

    @Override
    @Transactional
    public TaskCancellationResultDto cancelTask(Long userId, Long taskId) {
        return super.cancelTask(userId, taskId);
    }

    private void persistTaskModelContext(Long taskId,
                                         boolean isAttack,
                                         int attackBudget,
                                         boolean enablePrivacy,
                                         int devicePointCount,
                                         int linkPointCount,
                                         int falsifiableReadingDeviceCount,
                                         ModelRunSnapshotDto modelSnapshot) {
        taskRepository.updateModelContext(taskId, isAttack, isAttack ? attackBudget : 0, enablePrivacy,
                devicePointCount, falsifiableReadingDeviceCount, linkPointCount,
                JsonUtils.toJson(modelSnapshot));
    }

    @Override
    public void updateTaskProgress(Long taskId, int progress, String message) {
        super.updateTaskProgress(taskId, progress, message);
    }

    @Override
    @Transactional(readOnly = true)
    public int getTaskProgress(Long userId, Long taskId) {
        return super.getTaskProgress(userId, taskId);
    }

    // ==================== Core: build per-spec verification result ====================

    private VerificationResultDto buildVerificationResult(NusmvResult result,
                                                          List<DeviceVerificationDto> devices,
                                                          List<RuleDto> rules,
                                                          List<SpecificationDto> specs,
                                                          Long userId, Long taskId,
                                                          List<String> checkLogs,
                                                          Map<String, DeviceSmvData> deviceSmvMap,
                                                          Map<String, DeviceManifest> templateManifests,
                                                          String requestJson,
                                                          List<SmvGenerationContext.EmittedSpec> emittedSpecs,
                                                          List<ModelGenerationIssueDto> generationIssues,
                                                          int disabledRuleCount,
                                                          int skippedSpecCount) {
        List<SpecResultDto> specResults = new ArrayList<>();
        List<TraceDto> traces = new ArrayList<>();
        List<SpecCheckResult> rawSpecCheckResults = result.getSpecResults();
        List<SmvGenerationContext.EmittedSpec> effectiveSpecs = emittedSpecs != null ? emittedSpecs : List.of();
        SpecificationFormulaPreview.Context formulaPreviewContext =
                SpecificationFormulaPreview.modelContext(devices, templateManifests);

        // effectiveSpecs=0 means all specs were filtered out before SMV emission.
        if (effectiveSpecs.isEmpty()) {
            checkLogs.add("No valid specifications to verify (no specifications were emitted to NuSMV; all filtered out)");
            checkLogs.add(VerificationOutcome.INCONCLUSIVE_LOG_MARKER
                    + " No specifications were emitted, so verification has no conclusion.");
            return VerificationResultDto.builder()
                    .outcome(VerificationOutcome.INCONCLUSIVE)
                    .modelComplete(false)
                    .traces(List.of()).specResults(List.of())
                    .checkLogs(checkLogs)
                    .disabledRuleCount(disabledRuleCount)
                    .skippedSpecCount(skippedSpecCount)
                    .generationIssues(generationIssues)
                    .nusmvOutput(truncateOutput(result.getOutput())).build();
        }

        // Fail-closed: mark unsafe when per-spec results cannot be reliably parsed.
        boolean parseIncomplete = false;

        if (rawSpecCheckResults.isEmpty()) {
            checkLogs.add("Warning: could not parse per-spec results from NuSMV output");
            log.warn("No spec results parsed from NuSMV output; reporting all {} emitted specs as inconclusive", effectiveSpecs.size());
            for (SmvGenerationContext.EmittedSpec emittedSpec : effectiveSpecs) {
                specResults.add(toSpecResult(
                        emittedSpec, VerificationOutcome.INCONCLUSIVE, null, formulaPreviewContext));
            }
            parseIncomplete = true;
        } else {
            List<SpecCheckResult> specCheckResults = alignSpecResultsToEmittedSpecs(rawSpecCheckResults, effectiveSpecs, checkLogs);
            boolean hasMissingResult = specCheckResults.stream().anyMatch(Objects::isNull);

            if (rawSpecCheckResults.size() != effectiveSpecs.size() || hasMissingResult) {
            // 数量不一致：结果不可信，不把未知结果误报为通过或违反。
            log.warn("Spec count mismatch: NuSMV returned {} results but {} specs were generated. Reporting the run as inconclusive.",
                    rawSpecCheckResults.size(), effectiveSpecs.size());
            checkLogs.add("Warning: spec result count mismatch (got " + rawSpecCheckResults.size()
                    + ", expected " + effectiveSpecs.size() + ")");
            parseIncomplete = true;

            for (int specIdx = 0; specIdx < effectiveSpecs.size(); specIdx++) {
                SpecCheckResult scr = specCheckResults.get(specIdx);
                SmvGenerationContext.EmittedSpec emittedSpec = effectiveSpecs.get(specIdx);
                if (scr != null) {
                    appendParsedSpecResult(specResults, traces, specIdx, scr, emittedSpec,
                            userId, taskId, checkLogs, deviceSmvMap, rules, requestJson,
                            formulaPreviewContext);
                } else {
                    specResults.add(toSpecResult(
                            emittedSpec, VerificationOutcome.INCONCLUSIVE, null, formulaPreviewContext));
                    checkLogs.add("Spec " + describeSpec(emittedSpec, specIdx)
                            + " result missing, reported as inconclusive");
                }
            }

            if (rawSpecCheckResults.size() > effectiveSpecs.size()) {
                checkLogs.add("Warning: " + (rawSpecCheckResults.size() - effectiveSpecs.size())
                        + " extra NuSMV result(s) discarded");
            }
            } else {
                int specIdx = 0;
                for (SpecCheckResult scr : specCheckResults) {
                    appendParsedSpecResult(specResults, traces, specIdx, scr, effectiveSpecs.get(specIdx),
                            userId, taskId, checkLogs, deviceSmvMap, rules, requestJson,
                            formulaPreviewContext);
                    specIdx++;
                }
            }
        }

        boolean allPassed = !parseIncomplete && specResults.stream()
                .allMatch(specResult -> specResult.getOutcome() == VerificationOutcome.SATISFIED);
        if (parseIncomplete) {
            checkLogs.add(VerificationOutcome.INCONCLUSIVE_LOG_MARKER
                    + " Per-spec results are incomplete or unreliable; no satisfied/violated conclusion is reported.");
        } else if (!allPassed) {
            checkLogs.add("Some specifications violated.");
        } else {
            checkLogs.add("All specifications satisfied.");
        }

        VerificationOutcome outcome = parseIncomplete
                ? VerificationOutcome.INCONCLUSIVE
                : (allPassed ? VerificationOutcome.SATISFIED : VerificationOutcome.VIOLATED);
        boolean modelComplete = outcome.isModelComplete(disabledRuleCount, skippedSpecCount);
        for (TraceDto trace : traces) {
            trace.setDisabledRuleCount(disabledRuleCount);
            trace.setSkippedSpecCount(skippedSpecCount);
            trace.setModelComplete(modelComplete);
            trace.setGenerationIssues(generationIssues);
        }

        return VerificationResultDto.builder()
                .outcome(outcome)
                .modelComplete(modelComplete)
                .traces(traces)
                .specResults(specResults)
                .checkLogs(checkLogs)
                .disabledRuleCount(disabledRuleCount)
                .skippedSpecCount(skippedSpecCount)
                .generationIssues(generationIssues)
                .nusmvOutput(truncateOutput(result.getOutput()))
                .build();
    }

    private List<SpecCheckResult> alignSpecResultsToEmittedSpecs(List<SpecCheckResult> rawSpecResults,
                                                                  List<SmvGenerationContext.EmittedSpec> emittedSpecs,
                                                                  List<String> checkLogs) {
        Map<String, Deque<SpecCheckResult>> byExpression = new HashMap<>();
        Set<SpecCheckResult> used = Collections.newSetFromMap(new IdentityHashMap<>());
        for (SpecCheckResult result : rawSpecResults) {
            if (result == null) continue;
            String key = normalizeSpecExpression(result.getSpecExpression());
            if (key.isBlank()) continue;
            byExpression.computeIfAbsent(key, ignored -> new ArrayDeque<>()).add(result);
        }

        List<SpecCheckResult> aligned = new ArrayList<>(Collections.nCopies(emittedSpecs.size(), null));
        boolean reordered = false;
        for (int i = 0; i < emittedSpecs.size(); i++) {
            SmvGenerationContext.EmittedSpec emittedSpec = emittedSpecs.get(i);
            String key = normalizeSpecExpression(expression(emittedSpec));
            Deque<SpecCheckResult> matches = byExpression.get(key);
            if (matches == null || matches.isEmpty()) {
                continue;
            }
            SpecCheckResult matched = matches.removeFirst();
            aligned.set(i, matched);
            used.add(matched);
            if (i >= rawSpecResults.size() || rawSpecResults.get(i) != matched) {
                reordered = true;
            }
        }

        Deque<SpecCheckResult> unmatchedInOriginalOrder = new ArrayDeque<>();
        for (SpecCheckResult result : rawSpecResults) {
            if (result != null && !used.contains(result)) {
                unmatchedInOriginalOrder.add(result);
            }
        }
        for (int i = 0; i < aligned.size() && !unmatchedInOriginalOrder.isEmpty(); i++) {
            if (aligned.get(i) == null) {
                SpecCheckResult fallback = unmatchedInOriginalOrder.removeFirst();
                aligned.set(i, fallback);
                used.add(fallback);
            }
        }

        if (reordered && checkLogs != null) {
            checkLogs.add("NuSMV returned specification results in a different order; results were matched by expression.");
        }

        return aligned;
    }

    private String normalizeSpecExpression(String expression) {
        if (expression == null) {
            return "";
        }
        String normalized = expression.trim()
                .replaceFirst("(?i)^CTL\\s*SPEC\\s+", "")
                .replaceFirst("(?i)^LTL\\s*SPEC\\s+", "")
                .toLowerCase(Locale.ROOT);
        normalized = normalized.replaceAll("\\s+", "");
        normalized = normalized.replace("(", "").replace(")", "");
        return normalized;
    }

    private void appendParsedSpecResult(List<SpecResultDto> specResults,
                                        List<TraceDto> traces,
                                        int specIdx,
                                        SpecCheckResult scr,
                                        SmvGenerationContext.EmittedSpec emittedSpec,
                                        Long userId,
                                        Long taskId,
                                        List<String> checkLogs,
                                        Map<String, DeviceSmvData> deviceSmvMap,
                                        List<RuleDto> rules,
                                        String requestJson,
                                        SpecificationFormulaPreview.Context formulaPreviewContext) {
        specResults.add(toSpecResult(
                emittedSpec,
                scr.isPassed() ? VerificationOutcome.SATISFIED : VerificationOutcome.VIOLATED,
                scr.getSpecExpression(),
                formulaPreviewContext));
        if (!scr.isPassed() && scr.getCounterexample() != null) {
            checkLogs.add("Spec " + describeSpec(emittedSpec, specIdx) + " violated: "
                    + firstText(scr.getSpecExpression(), expression(emittedSpec)));
            List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                    scr.getCounterexample(), deviceSmvMap, rules);
            if (!states.isEmpty()) {
                SpecificationDto violatedSpec = emittedSpec.spec();
                TraceDto trace = TraceDto.builder()
                        .userId(userId)
                        .verificationTaskId(taskId)
                        .violatedSpecId(specId(emittedSpec))
                        .violatedSpecJson(violatedSpec != null ? specificationMapper.toJson(violatedSpec) : null)
                        .violatedSpec(violatedSpec)
                        .checkedExpression(scr.getSpecExpression())
                        .states(states)
                        .requestJson(requestJson)
                        .createdAt(LocalDateTime.now())
                        .build();
                traces.add(trace);
            }
        } else if (scr.isPassed()) {
            checkLogs.add("Spec " + describeSpec(emittedSpec, specIdx) + " satisfied");
        } else {
            checkLogs.add("Spec " + describeSpec(emittedSpec, specIdx)
                    + " violated (no counterexample): "
                    + firstText(scr.getSpecExpression(), expression(emittedSpec)));
        }
    }

    private SpecResultDto toSpecResult(SmvGenerationContext.EmittedSpec emittedSpec,
                                       VerificationOutcome outcome,
                                       String parsedExpression,
                                       SpecificationFormulaPreview.Context formulaPreviewContext) {
        SpecificationDto spec = emittedSpec != null ? emittedSpec.spec() : null;
        String templateId = spec != null ? firstText(spec.getTemplateId(), "unknown") : "unknown";
        String checkedExpression = firstText(parsedExpression, expression(emittedSpec));
        return SpecResultDto.builder()
                .specId(specId(emittedSpec))
                .templateId(templateId)
                .specificationLabel(SpecificationFormulaPreview.templateLabel(templateId))
                .formulaPreview(spec != null
                        ? SpecificationFormulaPreview.format(spec, formulaPreviewContext)
                        : "Structured specification")
                .formulaKind(checkedFormulaKind(checkedExpression, templateId))
                .outcome(outcome)
                .expression(checkedExpression)
                .build();
    }

    private String checkedFormulaKind(String expression, String templateId) {
        String normalized = expression == null ? "" : expression.trim().toUpperCase(Locale.ROOT);
        if (normalized.startsWith("LTLSPEC") || normalized.startsWith("LTL SPEC")) {
            return "LTL";
        }
        if (normalized.startsWith("CTLSPEC") || normalized.startsWith("CTL SPEC")) {
            return "CTL";
        }
        return "6".equals(templateId) ? "LTL" : "CTL";
    }

    private String specId(SmvGenerationContext.EmittedSpec emittedSpec) {
        if (emittedSpec != null && emittedSpec.specId() != null && !emittedSpec.specId().isBlank()) {
            return emittedSpec.specId();
        }
        SpecificationDto spec = emittedSpec != null ? emittedSpec.spec() : null;
        return specId(spec);
    }

    private String specId(SpecificationDto spec) {
        if (spec != null && spec.getId() != null && !spec.getId().isBlank()) {
            return spec.getId();
        }
        return SmvConstants.UNKNOWN_VIOLATED_SPEC_ID;
    }

    private String describeSpec(SmvGenerationContext.EmittedSpec emittedSpec, int index) {
        String id = specId(emittedSpec);
        return "#" + (index + 1) + " (" + id + ")";
    }

    private String expression(SmvGenerationContext.EmittedSpec emittedSpec) {
        if (emittedSpec != null && emittedSpec.expression() != null) {
            return emittedSpec.expression();
        }
        return "";
    }

    private String firstText(String preferred, String fallback) {
        if (preferred != null && !preferred.isBlank()) {
            return preferred;
        }
        if (fallback != null && !fallback.isBlank()) {
            return fallback;
        }
        return "";
    }

    // ==================== Task Status Management ====================

    private int countViolatedSpecs(List<SpecResultDto> specResults, List<TraceDto> traces) {
        if (specResults != null && !specResults.isEmpty()) {
            return (int) specResults.stream()
                    .filter(Objects::nonNull)
                    .filter(specResult -> specResult.getOutcome() == VerificationOutcome.VIOLATED)
                    .count();
        }
        return traces != null ? traces.size() : 0;
    }

    private boolean completeTask(VerificationTaskPo task, VerificationOutcome outcome, int violatedSpecCount,
                                 List<SpecResultDto> specResults, List<String> checkLogs, String nusmvOutput,
                                 List<ModelGenerationIssueDto> generationIssues,
                                 int disabledRuleCount, int skippedSpecCount) {
        try {
            LocalDateTime completedAt = LocalDateTime.now();
            Long processingTimeMs = task.getStartedAt() != null
                    ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
            String checkLogsJson = serializeCheckLogs(checkLogs);
            String specResultsJson = JsonUtils.toJsonOrEmpty(specResults);
            String generationIssuesJson = JsonUtils.toJsonOrEmpty(generationIssues);
            int updated = taskRepository.completeTaskIfRunning(
                    task.getId(),
                    VerificationTaskPo.TaskStatus.COMPLETED,
                    completedAt, outcome, violatedSpecCount,
                    disabledRuleCount, skippedSpecCount,
                    specResultsJson,
                    checkLogsJson, generationIssuesJson, truncateOutput(nusmvOutput),
                    null, processingTimeMs,
                    VerificationTaskPo.TaskStatus.RUNNING);
            if (updated == 0) {
                log.info("Verification task {} was not RUNNING or was already terminal, skipping completion", task.getId());
                return false;
            }
            return true;
        } catch (Exception e) {
            log.error("Failed to complete task: {}", task.getId(), e);
            return false;
        }
    }

    private void failTask(VerificationTaskPo task, String errorMessage) {
        if (task == null) {
            log.warn("failTask called with null task, errorMessage={}", errorMessage);
            return;
        }
        try {
            LocalDateTime completedAt = LocalDateTime.now();
            Long processingTimeMs = task.getStartedAt() != null
                    ? java.time.Duration.between(task.getStartedAt(), completedAt).toMillis() : null;
            String checkLogsJson = serializeCheckLogs(List.of(errorMessage));
            int updated = taskRepository.failTaskIfActive(
                    task.getId(),
                    VerificationTaskPo.TaskStatus.FAILED,
                    completedAt, VerificationOutcome.INCONCLUSIVE, errorMessage,
                    checkLogsJson, processingTimeMs,
                    List.of(VerificationTaskPo.TaskStatus.PENDING,
                            VerificationTaskPo.TaskStatus.RUNNING));
            if (updated == 0) {
                log.info("Verification task {} was no longer active, skipping fail", task.getId());
            }
        } catch (Exception e) {
            log.error("Failed to mark task as failed: {}", task.getId(), e);
        }
    }

    // ==================== Utilities ====================

    private Long persistCompletedVerificationRun(Long userId,
                                                 VerificationInput input,
                                                 VerificationResultDto result,
                                                 LocalDateTime startedAt) {
        if (transactionTemplate == null) {
            throw new IllegalStateException("transactionTemplate is required to persist verification runs");
        }
        List<TraceDto> traces = result.getTraces() != null ? result.getTraces() : List.of();
        List<String> persistedCheckLogs = result.getCheckLogs() != null
                ? new ArrayList<>(result.getCheckLogs()) : new ArrayList<>();
        appendTracePersistenceLog(persistedCheckLogs, traces);
        Long runId = transactionTemplate.execute(status -> {
            if (!lockActiveUserForTracePersistence(userId)) {
                throw new InternalServerException("Verification completed after the user account was removed");
            }

            LocalDateTime completedAt = LocalDateTime.now();
            VerificationOutcome outcome = result.getOutcome() != null
                    ? result.getOutcome()
                    : VerificationOutcome.INCONCLUSIVE;
            VerificationTaskPo run = VerificationTaskPo.builder()
                    .userId(userId)
                    .status(VerificationTaskPo.TaskStatus.COMPLETED)
                    .createdAt(startedAt)
                    .startedAt(startedAt)
                    .completedAt(completedAt)
                    .processingTimeMs(java.time.Duration.between(startedAt, completedAt).toMillis())
                    .isAttack(input.attack())
                    .attackBudget(input.attack() ? input.attackBudget() : 0)
                    .modeledDeviceAttackPointCount(input.modeledDeviceAttackPointCount())
                    .modeledFalsifiableReadingDeviceCount(input.modeledFalsifiableReadingDeviceCount())
                    .modeledAutomationLinkAttackPointCount(input.modeledAutomationLinkAttackPointCount())
                    .enablePrivacy(input.enablePrivacy())
                    .modelSnapshotJson(JsonUtils.toJson(input.modelSnapshot()))
                    .outcome(outcome)
                    .violatedSpecCount(countViolatedSpecs(result.getSpecResults(), traces))
                    .disabledRuleCount(result.getDisabledRuleCount())
                    .skippedSpecCount(result.getSkippedSpecCount())
                    .specResultsJson(JsonUtils.toJsonOrEmpty(result.getSpecResults()))
                    .checkLogsJson(serializeCheckLogs(persistedCheckLogs))
                    .generationIssuesJson(JsonUtils.toJsonOrEmpty(result.getGenerationIssues()))
                    .nusmvOutput(truncateOutput(result.getNusmvOutput()))
                    .progress(100)
                    .build();
            VerificationTaskPo savedRun = taskRepository.save(Objects.requireNonNull(run));
            if (savedRun == null || savedRun.getId() == null) {
                throw new InternalServerException("Verification result could not be added to run history");
            }
            if (!traces.isEmpty()) {
                saveTracesWithoutTransaction(traces, userId, savedRun.getId());
            }
            log.info("Saved synchronous verification run: id={}, userId={}, outcome={}, counterexamples={}",
                    savedRun.getId(), userId, outcome, traces.size());
            return savedRun.getId();
        });
        if (runId == null) {
            throw new InternalServerException("Verification result could not be added to run history");
        }
        result.setCheckLogs(persistedCheckLogs);
        return runId;
    }

    private boolean completeTaskAndSaveTraces(VerificationTaskPo task,
                                              List<TraceDto> traces,
                                              Long userId,
                                              Long taskId,
                                              VerificationOutcome outcome,
                                              int violatedSpecCount,
                                              List<SpecResultDto> specResults,
                                              List<String> checkLogs,
                                              String nusmvOutput,
                                              List<ModelGenerationIssueDto> generationIssues,
                                              int disabledRuleCount,
                                              int skippedSpecCount) {
        if (!userRepository.existsById(userId)) {
            log.info("User {} no longer exists, skipping verification task completion/persistence", userId);
            return false;
        }
        if (isCompletionCancelled(taskId)) {
            log.info("Verification task {} was cancelled before completion persistence", taskId);
            return false;
        }
        if (traces == null || traces.isEmpty()) {
            if (transactionTemplate == null) {
                return completeTask(task, outcome, violatedSpecCount, specResults, checkLogs, nusmvOutput,
                        generationIssues, disabledRuleCount, skippedSpecCount);
            }
            return Boolean.TRUE.equals(transactionTemplate.execute(status -> {
                if (!lockActiveUserForTracePersistence(userId)) {
                    log.info("User {} was deleted before verification task completion, skipping verification result", userId);
                    status.setRollbackOnly();
                    return false;
                }
                if (isCompletionCancelled(taskId)) {
                    log.info("Verification task {} was cancelled before completion", taskId);
                    status.setRollbackOnly();
                    return false;
                }
                return completeTask(task, outcome, violatedSpecCount, specResults, checkLogs, nusmvOutput,
                        generationIssues, disabledRuleCount, skippedSpecCount);
            }));
        }
        if (transactionTemplate == null) {
            throw new IllegalStateException("transactionTemplate is required to complete verification with traces");
        }
        return Boolean.TRUE.equals(transactionTemplate.execute(status -> {
            if (!lockActiveUserForTracePersistence(userId)) {
                log.info("User {} was deleted before trace persistence, skipping verification result", userId);
                status.setRollbackOnly();
                return false;
            }
            if (isCompletionCancelled(taskId)) {
                log.info("Verification task {} was cancelled before trace persistence", taskId);
                status.setRollbackOnly();
                return false;
            }
            appendTracePersistenceLog(checkLogs, traces);
            saveTracesWithoutTransaction(traces, userId, taskId);
            if (isCompletionCancelled(taskId)) {
                log.info("Verification task {} was cancelled after trace persistence but before completion; rolling back traces", taskId);
                status.setRollbackOnly();
                return false;
            }
            boolean completed = completeTask(task, outcome, violatedSpecCount, specResults, checkLogs, nusmvOutput,
                    generationIssues, disabledRuleCount, skippedSpecCount);
            if (!completed) {
                status.setRollbackOnly();
            }
            return completed;
        }));
    }

    private boolean isCompletionCancelled(Long taskId) {
        return taskId != null && (isTaskCancelled(taskId) || Thread.currentThread().isInterrupted());
    }

    private void appendTracePersistenceLog(List<String> checkLogs, List<TraceDto> traces) {
        if (checkLogs != null && traces != null && !traces.isEmpty()) {
            checkLogs.add("Auto-saved " + traces.size() + " violation trace(s).");
        }
    }

    private void saveTracesWithoutTransaction(List<TraceDto> traces, Long userId, Long taskId) {
        if (!lockActiveUserForTracePersistence(userId)) {
            log.info("User {} no longer exists, skipping trace persistence", userId);
            return;
        }
        for (TraceDto trace : traces) {
            trace.setUserId(userId);
            if (taskId != null) trace.setVerificationTaskId(taskId);
            TracePo po = traceMapper.toEntity(trace);
            if (po != null) {
                traceRepository.save(po);
                trace.setId(po.getId());
            }
        }
    }

    private boolean lockActiveUserForTracePersistence(Long userId) {
        return userId != null && userRepository.findByIdForUpdate(userId).isPresent();
    }

    private void requireActiveUserForTracePersistence(Long userId) {
        if (userId == null) {
            throw new ValidationException("userId", "User id cannot be null");
        }
        if (!lockActiveUserForTracePersistence(userId)) {
            throw ResourceNotFoundException.user(userId);
        }
    }

    private VerificationResultDto buildErrorResult(String nusmvOutput, List<String> checkLogs) {
        List<String> outcomeLogs = new ArrayList<>(checkLogs != null ? checkLogs : List.of());
        if (outcomeLogs.stream().noneMatch(log -> log != null
                && log.contains(VerificationOutcome.INCONCLUSIVE_LOG_MARKER))) {
            outcomeLogs.add(VerificationOutcome.INCONCLUSIVE_LOG_MARKER
                    + " Verification did not produce a reliable conclusion.");
        }
        return VerificationResultDto.builder()
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .modelComplete(false)
                .traces(List.of()).specResults(List.of())
                .checkLogs(outcomeLogs).nusmvOutput(truncateOutput(nusmvOutput)).build();
    }

    private void cleanupTempFile(File file) {
        // Keeping NuSMV model file for review: model.smv, request.json, output.txt, result.json
        // Temp directories (nusmv_*) are retained for post-mortem debugging.
    }

    private String syncVerificationExecutorSnapshot() {
        try {
            ThreadPoolExecutor nativeExecutor = syncVerificationExecutor.getThreadPoolExecutor();
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
            syncVerificationExecutor.getThreadPoolExecutor().purge();
        } catch (IllegalStateException ignored) {
            // executor may not be initialized yet
        }
    }

    // ==================== AbstractAsyncTaskService hooks ====================

    @Override
    protected Optional<VerificationTaskPo> findTaskByIdAndUserId(Long id, Long userId) {
        return taskRepository.findByIdAndUserId(id, userId);
    }

    @Override
    protected int atomicCancelTask(Long taskId, LocalDateTime completedAt) {
        return taskRepository.cancelTaskIfStillActive(
                taskId,
                VerificationTaskPo.TaskStatus.CANCELLED,
                completedAt,
                VerificationOutcome.INCONCLUSIVE,
                List.of(VerificationTaskPo.TaskStatus.PENDING,
                        VerificationTaskPo.TaskStatus.RUNNING));
    }

    @Override
    protected int atomicUpdateProgress(Long taskId, int progress) {
        return taskRepository.updateProgressIfActive(taskId, progress);
    }
}
