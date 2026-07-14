package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.FixStrategyApplier;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultLocalizationResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixStrategyAttemptDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.dto.fix.TemplateSnapshotComparison;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.BoardSemanticFingerprint;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

@Slf4j
@Service
@RequiredArgsConstructor
public class FixServiceImpl implements FixService {

    private static final List<String> DEFAULT_FIX_STRATEGIES = List.of("parameter", "condition", "remove");
    private static final Set<String> SUPPORTED_FIX_STRATEGIES = Set.copyOf(DEFAULT_FIX_STRATEGIES);

    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final SmvGenerator smvGenerator;
    private final RuleFixer ruleFixer;
    private final FixConfig fixConfig;
    private final BoardStorageService boardStorageService;
    private final BoardDataConverter boardDataConverter;

    @Override
    @Transactional(readOnly = true)
    public FaultLocalizationResultDto localizeFault(Long userId, Long traceId) {
        VerificationContext ctx = loadContext(userId, traceId);
        ModelBoundaryInput modelInput = modelBoundaryInput(ctx.request, ctx.templateManifests);
        List<FaultRuleDto> faultRules = ruleFixer.localizeFaults(
                ctx.trace.getStates(), ctx.request.getRules(), modelInput.deviceSmvMap());
        boolean modelComplete = sourceModelComplete(ctx.trace);
        String summary = faultRules.isEmpty()
                ? "No user-defined automation rule was localized in the counterexample transitions. "
                    + "The violation may instead depend on device or environment evolution."
                : faultRules.size() + " automation rule(s) were involved in counterexample transitions. "
                    + "This narrows review but does not prove that every listed rule independently caused the violation.";
        List<String> warnings = modelComplete
                ? List.of()
                : List.of(incompleteSourceModelWarning(ctx.trace));
        return FaultLocalizationResultDto.builder()
                .traceId(traceId)
                .violatedSpecId(ctx.trace.getViolatedSpecId())
                .sourceModelComplete(modelComplete)
                .sourceDisabledRuleCount(sourceDisabledRuleCount(ctx.trace))
                .sourceSkippedSpecCount(sourceSkippedSpecCount(ctx.trace))
                .sourceGenerationIssues(sourceGenerationIssues(ctx.trace))
                .faultRules(faultRules)
                .summary(summary)
                .warnings(warnings)
                .build();
    }

    @Override
    public FixResultDto fix(Long userId, Long traceId, List<String> strategies,
                            Map<String, PreferredRange> preferredRanges) {
        strategies = validateRequestedStrategies(strategies);
        validatePreferredRanges(preferredRanges);
        VerificationContext ctx = loadContext(userId, traceId);
        VerificationRequestDto req = ctx.request;
        ModelBoundaryInput modelInput = modelBoundaryInput(req, ctx.templateManifests);
        Map<String, DeviceSmvData> deviceSmvMap = modelInput.deviceSmvMap();

        if (!sourceModelComplete(ctx.trace)) {
            return incompleteSourceModelResult(traceId, ctx, strategies, deviceSmvMap);
        }

        FixResultDto result = ruleFixer.fix(
                traceId,
                ctx.trace.getViolatedSpecId(),
                ctx.trace.getStates(),
                req.getRules(),
                modelInput.devices(),
                modelInput.environmentVariables(),
                req.getSpecs(),
                deviceSmvMap,
                userId,
                req.isAttack(),
                req.getAttackBudget(),
                req.isEnablePrivacy(),
                strategies,
                fixConfig.getMaxAttempts(),
                preferredRanges
        );

        appendDriftWarningIfNeeded(result, userId, ctx);
        applySourceModelMetadata(result, ctx.trace);

        return result;
    }

    @Override
    @Transactional
    public FixApplyResultDto applyFix(Long userId, Long traceId, String strategy,
                                      Map<String, PreferredRange> preferredRanges) {
        return applyFixInternal(userId, traceId, strategy, null, preferredRanges);
    }

    /**
     * Kept for service-level tamper-detection tests. REST callers do not send a concrete suggestion:
     * the public API applies the server-recomputed proposal for the selected strategy.
     */
    @Override
    @Deprecated
    @Transactional
    public FixApplyResultDto applyFix(Long userId, Long traceId, String strategy, FixSuggestionDto suggestion,
                                      Map<String, PreferredRange> preferredRanges) {
        if (suggestion == null) {
            throw new BadRequestException("suggestion must not be null");
        }
        if (strategy == null || strategy.isBlank()) {
            throw new BadRequestException("strategy must not be blank");
        }
        if (suggestion.getStrategy() != null && !strategy.equals(suggestion.getStrategy())) {
            throw new BadRequestException("strategy '" + strategy
                    + "' does not match suggestion.strategy '" + suggestion.getStrategy() + "'");
        }
        return applyFixInternal(userId, traceId, strategy, suggestion, preferredRanges);
    }

    private FixApplyResultDto applyFixInternal(Long userId, Long traceId, String strategy,
                                               FixSuggestionDto clientSuggestion,
                                               Map<String, PreferredRange> preferredRanges) {
        String validatedStrategy = validateApplyStrategy(strategy);
        validatePreferredRanges(preferredRanges);
        // Load the trace's verification-time snapshot (normalized rules) for index/fingerprint alignment.
        VerificationContext ctx = loadContext(userId, traceId);
        assertCompleteSourceForApply(ctx.trace);
        List<RuleDto> snapshotRules = ctx.request.getRules();
        if (snapshotRules == null || snapshotRules.isEmpty()) {
            throw new BadRequestException("Verification context has no rules; cannot apply fix.");
        }

        ModelBoundaryInput modelInput = modelBoundaryInput(ctx.request, ctx.templateManifests);
        Map<String, DeviceSmvData> deviceSmvMap = modelInput.deviceSmvMap();

        // Re-derive the fix server-side for the requested strategy against the trace's own context.
        // The REST API never accepts an operation list; the optional clientSuggestion is used only by
        // the internal service overload that tests tamper detection for programmatic callers.
        FixSuggestionDto trusted = recomputeVerifiedSuggestion(
                userId, ctx, validatedStrategy, modelInput, preferredRanges);
        if (trusted == null) {
            throw new BadRequestException("Could not reproduce a verified '" + validatedStrategy
                    + "' fix for this trace (the board or templates may have changed). "
                    + "Please re-run the fix and try again.");
        }
        if (clientSuggestion != null
                && !suggestionsEquivalent(validatedStrategy, clientSuggestion, trusted, deviceSmvMap)) {
            throw new BadRequestException("The submitted fix no longer matches the current verified '"
                    + validatedStrategy + "' suggestion. Please re-run the fix and apply the updated suggestion.");
        }

        // Read current rules → drift check → apply → save, all inside ONE per-user lock + transaction.
        // This closes the race where a concurrent save could interleave between an unlocked read and the
        // locked write, letting apply overwrite freshly-saved rules with a stale list. The drift check
        // runs on the exact snapshot that gets written.
        int[] before = {0};
        List<RuleDto> saved = boardStorageService.updateRulesAgainstSnapshot(userId, boardSnapshot -> {
            List<RuleDto> boardRules = boardSnapshot.rules();
            before[0] = boardRules.size();
            ModelInputSnapshot currentSnapshot = boardDataConverter.toModelInputSnapshot(boardSnapshot);
            assertTemplatesUnchanged(ctx, currentSnapshot.templateManifests());
            // Spec/device drift guard: run inside the same per-user write lock as the final save, so a
            // concurrent spec/device edit cannot slip in after the check but before persistence.
            CurrentBoardSemanticContext currentBoard = assertSpecsAndDevicesUnchanged(
                    currentSnapshot, ctx, deviceSmvMap);
            // Guard against board drift: the snapshot the fix was computed against must still line up
            // with the current board rules by ordered fingerprint. Internal fix coordinates must never
            // be allowed to target a different rule or condition after the board changes.
            assertBoardAlignedWithSnapshot(boardRules, snapshotRules, deviceSmvMap);
            // Apply the server-recomputed suggestion, so the persisted change is exactly what NuSMV
            // just verified.
            Map<String, String> persistenceDeviceRefs = buildPersistenceDeviceRefAliases(
                    currentSnapshot.nodes(), deviceSmvMap, currentBoard.currentDeviceSmvMap());
            Map<String, String> displayDeviceNames = "remove".equals(validatedStrategy)
                    ? Map.of()
                    : buildDisplayDeviceNames(currentSnapshot.nodes());
            return FixStrategyApplier.apply(
                    validatedStrategy, trusted, boardRules, deviceSmvMap,
                    persistenceDeviceRefs, displayDeviceNames);
        });
        log.info("Applied '{}' fix for trace {} (user {}): {} rule(s) -> {} rule(s)",
                validatedStrategy, traceId, userId, before[0], saved.size());

        return FixApplyResultDto.builder()
                .applied(true)
                .strategy(validatedStrategy)
                .verificationRechecked(true)
                .appliedSuggestion(trusted)
                .previousRuleCount(before[0])
                .currentRuleCount(saved.size())
                .message(buildApplyMessage(validatedStrategy, trusted, before[0], saved.size()))
                .rules(saved)
                .build();
    }

    /**
     * Recompute the fix for a single strategy against the trace's own verification context and return
     * the verified suggestion for that strategy, or {@code null} if none was produced/verified.
     */
    private FixSuggestionDto recomputeVerifiedSuggestion(Long userId, VerificationContext ctx,
                                                         String strategy,
                                                         ModelBoundaryInput modelInput,
                                                         Map<String, PreferredRange> preferredRanges) {
        VerificationRequestDto req = ctx.request;
        Map<String, DeviceSmvData> deviceSmvMap = modelInput.deviceSmvMap();
        FixResultDto recomputed = ruleFixer.fix(
                ctx.trace.getId(),
                ctx.trace.getViolatedSpecId(),
                ctx.trace.getStates(),
                req.getRules(),
                modelInput.devices(),
                modelInput.environmentVariables(),
                req.getSpecs(),
                deviceSmvMap,
                userId,
                req.isAttack(),
                req.getAttackBudget(),
                req.isEnablePrivacy(),
                List.of(strategy),
                fixConfig.getMaxAttempts(),
                preferredRanges
        );
        if (recomputed == null || recomputed.getSuggestions() == null) {
            return null;
        }
        return recomputed.getSuggestions().stream()
                .filter(s -> s != null && strategy.equals(s.getStrategy()) && s.isVerified())
                .findFirst()
                .orElse(null);
    }

    /**
     * WYSIWYG check: the client suggestion the user acted on must be equivalent to the freshly
     * recomputed, verified server suggestion. Compared by the operations they encode (not object
     * identity), per strategy.
     */
    private boolean suggestionsEquivalent(String strategy, FixSuggestionDto client, FixSuggestionDto server,
                                          Map<String, DeviceSmvData> deviceSmvMap) {
        if (client == null || server == null) return false;
        switch (strategy) {
            case "parameter":
                return Objects.equals(
                        parameterFingerprint(client.getParameterAdjustments()),
                        parameterFingerprint(server.getParameterAdjustments()));
            case "condition":
                return Objects.equals(
                        conditionAdjFingerprint(client.getConditionAdjustments()),
                        conditionAdjFingerprint(server.getConditionAdjustments()));
            case "remove":
                return Objects.equals(
                        sortedInts(client.getRemovedRuleIndices()),
                        sortedInts(server.getRemovedRuleIndices()));
            default:
                return false;
        }
    }

    private String parameterFingerprint(List<cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment> adjs) {
        if (adjs == null) return "";
        return adjs.stream()
                .map(a -> a.getRuleIndex() + ":" + a.getConditionIndex() + ":"
                        + a.getAttribute() + ":" + a.getRelation() + ":" + a.getNewValue())
                .sorted()
                .reduce("", (x, y) -> x + "|" + y);
    }

    private String conditionAdjFingerprint(List<cn.edu.nju.Iot_Verify.dto.fix.ConditionAdjustment> adjs) {
        if (adjs == null) return "";
        return adjs.stream()
                .filter(a -> !"keep".equals(a.getAction()))
                .map(a -> a.getRuleIndex() + ":" + a.getConditionIndex() + ":" + a.getAction() + ":"
                        + a.getTargetType() + ":" + a.getAttribute() + ":" + a.getDeviceName()
                        + ":" + a.getRelation() + ":" + a.getValue())
                .sorted()
                .reduce("", (x, y) -> x + "|" + y);
    }

    private List<Integer> sortedInts(List<Integer> in) {
        if (in == null) return List.of();
        List<Integer> copy = new ArrayList<>(in);
        copy.sort(java.util.Comparator.naturalOrder());
        return copy;
    }

    /**
     * Ensure the current board rules still align with the trace snapshot the fix was computed against.
     * Alignment = same rule count AND each rule's semantic fingerprint matches position-by-position.
     * If the user edited/added/removed rules after verifying, internal suggestion coordinates would be
     * stale, so we reject rather than risk editing the wrong rule.
     */
    private void assertBoardAlignedWithSnapshot(List<RuleDto> boardRules, List<RuleDto> snapshotRules,
                                                Map<String, DeviceSmvData> deviceSmvMap) {
        if (boardRules.size() != snapshotRules.size()) {
            throw new BadRequestException("Board rules changed since verification ("
                    + snapshotRules.size() + " rules verified, " + boardRules.size()
                    + " now). Please re-run verification before applying a fix.");
        }
        for (int i = 0; i < boardRules.size(); i++) {
            String boardFp = ruleFingerprint(boardRules.get(i), deviceSmvMap);
            String snapFp = ruleFingerprint(snapshotRules.get(i), deviceSmvMap);
            if (!Objects.equals(boardFp, snapFp)) {
                throw new BadRequestException(ruleDriftLabel(boardRules.get(i), i)
                        + " changed since verification. "
                        + "Please re-run verification before applying a fix.");
            }
        }
    }

    /** Reject apply unless the current manifests can be proven equal to the frozen run snapshot. */
    private void assertTemplatesUnchanged(
            VerificationContext ctx,
            Map<String, DeviceManifest> currentTemplateManifests) {
        TemplateSnapshotComparison comparison = compareTemplateSnapshots(
                ctx.templateManifests, currentTemplateManifests);
        if (comparison == TemplateSnapshotComparison.CHANGED) {
            throw new BadRequestException("Device template(s) were modified after this trace was recorded. "
                    + "The fix may no longer match the verification model. "
                    + "Please re-run verification before applying a fix.");
        }
        if (comparison == TemplateSnapshotComparison.UNAVAILABLE) {
            throw new ServiceUnavailableException("Could not confirm whether the current device templates "
                    + "still match this verification run. Please retry applying the fix later.");
        }
    }

    /**
     * Reject the apply if the user edited specs or device instance state (variables, privacies, initial
     * state, trust) after the trace was recorded. The server recompute replays the trace's stored
     * context, so it cannot detect these edits on its own; without this guard a fix verified against a
     * stale spec/device model would be silently persisted.
     *
     * <p>Compares a canonical SEMANTIC fingerprint of the trace's snapshot against the current board.
     * Both sides are canonicalized identically ({@link BoardSemanticFingerprint}) — device names
     * normalized, effective variable/trust/privacy values derived from the same manifests NuSMV uses,
     * values de-quoted — so an untouched board matches its model-boundary normalized snapshot instead of
     * misfiring (the failure mode of the earlier byte-equality attempt). {@code snapshotDeviceSmvMap}
     * was built from the snapshot devices; the current board gets its own map so omitted instance
     * overrides resolve against the same manifests.</p>
     */
    private CurrentBoardSemanticContext assertSpecsAndDevicesUnchanged(
            ModelInputSnapshot currentBoard,
            VerificationContext ctx,
            Map<String, DeviceSmvData> snapshotDeviceSmvMap) {
        List<DeviceVerificationDto> currentDevices = currentBoard.devices();
        List<SpecificationDto> currentSpecs = currentBoard.specifications();
        assertCompleteSourceForApply(ctx.trace);

        Map<String, DeviceSmvData> currentDeviceSmvMap;
        List<BoardEnvironmentVariableDto> currentEnvironmentVariables = currentBoard.environmentVariables();
        try {
            currentDeviceSmvMap = smvGenerator.buildDeviceSmvMapFromTemplateSnapshots(
                    currentDevices, currentBoard.templateManifests());
        } catch (SmvGenerationException e) {
            if (isTransientCurrentDeviceModelFailure(e)) {
                log.warn("Spec/device drift check: current board device model could not be confirmed; "
                        + "failing closed [{}]: {}", e.getErrorCategory(), e.getMessage());
                throw new ServiceUnavailableException("Could not confirm the current board device model. "
                        + "Please retry applying the fix later.", e);
            }
            throw currentBoardDeviceModelChanged(e);
        } catch (BadRequestException e) {
            throw currentBoardDeviceModelChanged(e);
        } catch (Exception e) {
            // We cannot tell whether the current board still matches the verified snapshot. Fail closed,
            // but report a retryable service issue instead of telling the user their board changed.
            log.warn("Spec/device drift check: current board device model check failed unexpectedly; "
                            + "failing closed: {}",
                    e.getMessage());
            throw new ServiceUnavailableException("Could not confirm the current board device model. "
                    + "Please retry applying the fix later.", e);
        }

        String snapshotFp = BoardSemanticFingerprint.of(
                ctx.request.getDevices(), ctx.request.getSpecs(), ctx.request.getEnvironmentVariables(),
                snapshotDeviceSmvMap);
        String currentFp = BoardSemanticFingerprint.of(
                currentDevices, currentSpecs, currentEnvironmentVariables, currentDeviceSmvMap);

        if (!snapshotFp.equals(currentFp)) {
            log.info("Spec/device drift detected for trace {}", ctx.trace.getId());
            throw new BadRequestException("Specifications or device state changed since verification. "
                    + "The fix was verified against the earlier model. "
                    + "Please re-run verification before applying a fix.");
        }
        return new CurrentBoardSemanticContext(currentDevices, currentDeviceSmvMap);
    }

    private String ruleDriftLabel(RuleDto rule, int index) {
        String description = rule == null ? null : rule.getRuleString();
        if (description != null && !description.isBlank()) {
            return "Automation rule \"" + description.trim() + "\" (position " + (index + 1) + ")";
        }
        return "The automation rule at position " + (index + 1);
    }

    private boolean isTransientCurrentDeviceModelFailure(SmvGenerationException e) {
        return e != null
                && SmvGenerationException.ErrorCategories.TEMPLATE_LOAD_ERROR.equals(e.getErrorCategory());
    }

    private BadRequestException currentBoardDeviceModelChanged(Exception e) {
        log.warn("Spec/device drift check: current board failed to build a valid device model; "
                + "failing closed: {}", e.getMessage());
        return new BadRequestException("The board's devices changed since verification and no longer "
                + "form a valid model. Please re-run verification before applying a fix.", e);
    }

    /**
     * Build aliases from model-boundary device references back to persisted board node ids.
     *
     * <p>{@link BoardDataConverter} intentionally normalizes raw node ids to NuSMV-safe
     * {@code varName}s. Those names are valid for model generation, but they are not necessarily
     * valid values for the board rules table (for example, a UUID with '-' becomes a value with
     * '_'). The raw node snapshot is therefore the persistence authority for fix application.</p>
     */
    private Map<String, String> buildPersistenceDeviceRefAliases(
            List<DeviceNodeDto> currentNodes,
            Map<String, DeviceSmvData> snapshotDeviceSmvMap,
            Map<String, DeviceSmvData> currentDeviceSmvMap) {
        Map<String, String> aliases = new LinkedHashMap<>();
        if (currentNodes == null || currentNodes.isEmpty()) {
            return aliases;
        }
        for (DeviceNodeDto node : currentNodes) {
            if (node == null) continue;
            String persistedRef = trimToNull(node.getId());
            if (persistedRef == null) continue;
            putAlias(aliases, persistedRef, persistedRef);
            putAlias(aliases, DeviceNameNormalizer.normalize(persistedRef), persistedRef);
            putResolvedAlias(aliases, persistedRef, snapshotDeviceSmvMap);
            putResolvedAlias(aliases, persistedRef, currentDeviceSmvMap);
        }
        return aliases;
    }

    private Map<String, String> buildDisplayDeviceNames(List<DeviceNodeDto> nodes) {
        Map<String, String> displayNames = new LinkedHashMap<>();
        for (DeviceNodeDto node : nodes == null ? List.<DeviceNodeDto>of() : nodes) {
            if (node == null) continue;
            String id = trimToNull(node.getId());
            String label = trimToNull(node.getLabel());
            if (id == null || label == null) continue;
            displayNames.putIfAbsent(id, label);
            displayNames.putIfAbsent(DeviceNameNormalizer.normalize(id), label);
        }
        return displayNames;
    }

    private void putResolvedAlias(Map<String, String> aliases, String persistedRef,
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        try {
            DeviceSmvData smv = DeviceReferenceResolver.resolve(
                    persistedRef, deviceSmvMap);
            if (smv != null) {
                putAlias(aliases, smv.getVarName(), persistedRef);
            }
        } catch (Exception e) {
            log.debug("Could not build persistence alias for device '{}': {}", persistedRef, e.getMessage());
        }
    }

    private void putAlias(Map<String, String> aliases, String alias, String persistedRef) {
        String key = trimToNull(alias);
        String value = trimToNull(persistedRef);
        if (key != null && value != null) {
            aliases.putIfAbsent(key, value);
        }
    }

    private String trimToNull(String value) {
        if (value == null) return null;
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    /**
     * Fingerprint of a rule = command(deviceName|action) + ORDER-PRESERVING condition fingerprints.
     * Uses the same SMV varName resolution the fixer uses, so normalized snapshot names and raw board
     * names compare equal when they denote the same device.
     *
     * <p>Condition order is preserved (not sorted): the fix's {@code conditionIndex} is positional,
     * so a board rule whose conditions were merely reordered must NOT pass the drift check — otherwise
     * apply would edit/remove the wrong condition.</p>
     */
    private String ruleFingerprint(RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder sb = new StringBuilder();
        RuleDto.Command cmd = rule.getCommand();
        if (cmd != null) {
            sb.append(resolveVar(cmd.getDeviceName(), deviceSmvMap))
              .append('#').append(cmd.getAction() == null ? "" : cmd.getAction())
              // contentDevice/content drive privacy content migration in SMV generation, so a change to
              // them is a real rule change that must fail the drift check (resolve the device ref so a
              // renamed contentDevice compares equal only when it denotes the same device).
              .append('#').append(cmd.getContentDevice() == null ? ""
                      : resolveVar(cmd.getContentDevice(), deviceSmvMap))
              .append('#').append(cmd.getContent() == null ? "" : cmd.getContent());
        }
        sb.append("=>");
        List<String> condFps = new ArrayList<>();
        if (rule.getConditions() != null) {
            for (RuleDto.Condition c : rule.getConditions()) {
                condFps.add(FixStrategyApplier.conditionFingerprint(normalizeConditionDeviceName(c), deviceSmvMap));
            }
        }
        // Positional join — do NOT sort; conditionIndex alignment depends on order.
        sb.append(String.join(",", condFps));
        return sb.toString();
    }

    /**
     * Resolve a raw board node id to the SMV-safe varName used by the trace snapshot.
     */
    private String resolveVar(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        return FixStrategyApplier.resolveVarName(DeviceNameNormalizer.normalize(deviceName), deviceSmvMap);
    }

    /**
     * Return a copy of the condition with its deviceName normalized to the SMV-safe varName, so
     * fingerprints from raw board rules line up with the normalized snapshot. The original condition
     * is not mutated.
     */
    private RuleDto.Condition normalizeConditionDeviceName(RuleDto.Condition c) {
        if (c == null) return null;
        String normalized = DeviceNameNormalizer.normalize(c.getDeviceName());
        if (Objects.equals(normalized, c.getDeviceName())) {
            return c;
        }
        return RuleDto.Condition.builder()
                .deviceName(normalized)
                .attribute(c.getAttribute())
                .targetType(c.getTargetType())
                .relation(c.getRelation())
                .value(c.getValue())
                .build();
    }

    private String buildApplyMessage(String strategy, FixSuggestionDto suggestion,
                                     int before, int after) {
        switch (strategy) {
            case "parameter":
                int pCount = suggestion.getParameterAdjustments() == null ? 0
                        : suggestion.getParameterAdjustments().size();
                return "Applied " + pCount + " parameter adjustment(s) after the server recomputed "
                        + "and verified the suggestion.";
            case "condition":
                int cCount = suggestion.getConditionAdjustments() == null ? 0
                        : (int) suggestion.getConditionAdjustments().stream()
                                .filter(a -> !"keep".equals(a.getAction())).count();
                return "Applied " + cCount + " condition change(s) after the server recomputed "
                        + "and verified the suggestion.";
            case "remove":
                return "Permanently removed " + (before - after) + " automation rule(s) after the server recomputed "
                        + "and verified the suggestion.";
            default:
                return "Fix applied after the server recomputed and verified the suggestion.";
        }
    }

    private void appendDriftWarningIfNeeded(FixResultDto result, Long userId,
                                            VerificationContext ctx) {
        TemplateSnapshotComparison comparison;
        try {
            comparison = compareTemplateSnapshots(
                    ctx.templateManifests,
                    boardDataConverter.getModelInputSnapshot(userId).templateManifests());
        } catch (Exception e) {
            log.warn("Template snapshot comparison is unavailable: {}", e.getMessage());
            comparison = TemplateSnapshotComparison.UNAVAILABLE;
        }
        result.setTemplateSnapshotComparison(comparison);
        if (comparison == TemplateSnapshotComparison.UNCHANGED) return;

        String warning = comparison == TemplateSnapshotComparison.CHANGED
                ? "WARNING: Current device template(s) differ from the run snapshot. Suggestions were "
                    + "generated from the earlier frozen model and cannot be applied until verification "
                    + "is run again on the current board."
                : "WARNING: Current device templates could not be compared with the run snapshot. "
                    + "Suggestions were generated from the earlier frozen model, but apply will remain "
                    + "blocked until the comparison can be completed.";
        String base = result.getSummary() != null ? result.getSummary() : "";
        result.setSummary(base.isEmpty() ? warning : base + " " + warning);
        addResultWarning(result, warning);
    }

    private FixResultDto incompleteSourceModelResult(Long traceId,
                                                     VerificationContext ctx,
                                                     List<String> strategies,
                                                     Map<String, DeviceSmvData> deviceSmvMap) {
        int disabledRules = sourceDisabledRuleCount(ctx.trace);
        int skippedSpecs = sourceSkippedSpecCount(ctx.trace);
        String warning = incompleteSourceModelWarning(ctx.trace);
        List<String> effectiveStrategies = strategies != null && !strategies.isEmpty()
                ? strategies : DEFAULT_FIX_STRATEGIES;
        List<FixStrategyAttemptDto> attempts = effectiveStrategies.stream()
                .map(strategy -> FixStrategyAttemptDto.builder()
                        .strategy(strategy)
                        .status("SKIPPED_INCOMPLETE_SOURCE_MODEL")
                        .reason(warning)
                        .build())
                .toList();
        List<FaultRuleDto> faultRules = ruleFixer.localizeFaults(
                ctx.trace.getStates(), ctx.request.getRules(), deviceSmvMap);
        return FixResultDto.builder()
                .traceId(traceId)
                .violatedSpecId(ctx.trace.getViolatedSpecId())
                .faultRules(faultRules)
                .suggestions(List.of())
                .strategyAttempts(attempts)
                .fixable(false)
                .sourceModelComplete(false)
                .sourceDisabledRuleCount(disabledRules)
                .sourceSkippedSpecCount(skippedSpecs)
                .sourceGenerationIssues(sourceGenerationIssues(ctx.trace))
                .summary(warning)
                .warnings(List.of(warning))
                .build();
    }

    private void applySourceModelMetadata(FixResultDto result, TraceDto trace) {
        if (result == null) return;
        result.setSourceModelComplete(sourceModelComplete(trace));
        result.setSourceDisabledRuleCount(sourceDisabledRuleCount(trace));
        result.setSourceSkippedSpecCount(sourceSkippedSpecCount(trace));
        result.setSourceGenerationIssues(sourceGenerationIssues(trace));
    }

    private boolean sourceModelComplete(TraceDto trace) {
        return trace != null && Boolean.TRUE.equals(trace.getModelComplete());
    }

    private int sourceDisabledRuleCount(TraceDto trace) {
        return trace != null && trace.getDisabledRuleCount() != null ? trace.getDisabledRuleCount() : 0;
    }

    private int sourceSkippedSpecCount(TraceDto trace) {
        return trace != null && trace.getSkippedSpecCount() != null ? trace.getSkippedSpecCount() : 0;
    }

    private List<ModelGenerationIssueDto> sourceGenerationIssues(TraceDto trace) {
        return trace != null && trace.getGenerationIssues() != null
                ? List.copyOf(trace.getGenerationIssues())
                : List.of();
    }

    private String incompleteSourceModelWarning(TraceDto trace) {
        if (trace == null || trace.getModelComplete() == null) {
            return "Automatic fix was not attempted because the source verification does not contain explicit "
                    + "model-completeness metadata. Verify the current board again before requesting a fix.";
        }
        return "Automatic fix was not attempted because the source verification used an incomplete generated "
                + "model (" + sourceDisabledRuleCount(trace) + " rule(s) disabled, "
                + sourceSkippedSpecCount(trace) + " specification(s) skipped). Resolve the itemized generation "
                + "issues and verify again first.";
    }

    private void assertCompleteSourceForApply(TraceDto trace) {
        if (sourceModelComplete(trace)) {
            return;
        }
        if (trace == null || trace.getModelComplete() == null) {
            throw new BadRequestException("Cannot apply an automatic fix because the source verification does not "
                    + "contain explicit model-completeness metadata. Verify the current board again first.");
        }
        throw new BadRequestException("Cannot apply an automatic fix from this trace because its source verification "
                + "used an incomplete generated model ("
                + sourceDisabledRuleCount(trace) + " rule(s) disabled, "
                + sourceSkippedSpecCount(trace) + " specification(s) skipped). Resolve the itemized generation "
                + "issues and verify the current board again first.");
    }

    private void addResultWarning(FixResultDto result, String warning) {
        List<String> warnings = new ArrayList<>(result.getWarnings() != null ? result.getWarnings() : List.of());
        if (!warnings.contains(warning)) warnings.add(warning);
        result.setWarnings(warnings);
    }

    /**
     * Compare the persisted manifest projection rather than Java object identity. Trace snapshots are
     * serialized and deserialized before this check, so write-only compatibility fields (for example
     * an empty legacy API Assignments list) may be absent even when the current parsed manifest still
     * carries an empty collection. Those representations are semantically identical to the model.
     */
    private TemplateSnapshotComparison compareTemplateSnapshots(
            Map<String, DeviceManifest> verificationTemplateSnapshots,
            Map<String, DeviceManifest> currentTemplateSnapshots) {
        if (verificationTemplateSnapshots == null || verificationTemplateSnapshots.isEmpty()
                || currentTemplateSnapshots == null || currentTemplateSnapshots.isEmpty()) {
            return TemplateSnapshotComparison.UNAVAILABLE;
        }
        boolean drifted = !verificationTemplateSnapshots.keySet().equals(currentTemplateSnapshots.keySet())
                || verificationTemplateSnapshots.entrySet().stream()
                        .anyMatch(entry -> !sameTemplateManifest(
                                entry.getValue(), currentTemplateSnapshots.get(entry.getKey())));
        if (drifted) {
            log.warn("Template drift detected by manifest comparison");
        }
        return drifted ? TemplateSnapshotComparison.CHANGED : TemplateSnapshotComparison.UNCHANGED;
    }

    private boolean sameTemplateManifest(DeviceManifest first, DeviceManifest second) {
        if (first == null || second == null) {
            return first == second;
        }
        return Objects.equals(JsonUtils.toJson(first), JsonUtils.toJson(second));
    }

    private List<String> validateRequestedStrategies(List<String> strategies) {
        if (strategies == null) {
            return null;
        }
        if (strategies.isEmpty()) {
            throw new BadRequestException(
                    "strategies must be non-empty when provided; omit it to use the default order");
        }
        Set<String> seen = new LinkedHashSet<>();
        for (int i = 0; i < strategies.size(); i++) {
            String strategy = strategies.get(i);
            if (strategy == null || strategy.isBlank()) {
                throw new BadRequestException("strategies[" + i + "] must not be blank");
            }
            if (!SUPPORTED_FIX_STRATEGIES.contains(strategy)) {
                throw new BadRequestException("Unsupported strategy '" + strategy
                        + "'. Allowed: parameter, condition, remove.");
            }
            if (!seen.add(strategy)) {
                throw new BadRequestException("Duplicate strategy '" + strategy + "'.");
            }
        }
        return List.copyOf(strategies);
    }

    private String validateApplyStrategy(String strategy) {
        if (strategy == null || strategy.isBlank()) {
            throw new BadRequestException("strategy must not be blank");
        }
        if (!SUPPORTED_FIX_STRATEGIES.contains(strategy)) {
            throw new BadRequestException("Unsupported strategy '" + strategy
                    + "'. Allowed: parameter, condition, remove.");
        }
        return strategy;
    }

    private void validatePreferredRanges(Map<String, PreferredRange> ranges) {
        if (ranges == null) return;
        for (Map.Entry<String, PreferredRange> entry : ranges.entrySet()) {
            String key = entry.getKey();
            if (key == null) {
                throw new BadRequestException("preferred range targetId must not be null");
            }
            PreferredRange pr = entry.getValue();
            if (!PreferredRangeSelection.isValidTargetId(key)) {
                throw new BadRequestException("Invalid preferred range targetId '" + key + "'");
            }
            if (pr == null) {
                throw new BadRequestException("preferred range value for targetId '" + key + "' must not be null");
            }
            if (pr.getLower() == null || pr.getUpper() == null) {
                throw new BadRequestException("preferred range entry for targetId '" + key
                        + "': lower and upper must not be null");
            }
            if (pr.getLower() > pr.getUpper()) {
                throw new BadRequestException("Invalid preferred range for targetId '" + key
                        + "': lower(" + pr.getLower() + ") > upper(" + pr.getUpper() + ")");
            }
        }
    }

    private VerificationContext loadContext(Long userId, Long traceId) {
        TracePo po = traceRepository.findByIdAndUserId(traceId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("Trace", traceId));
        TraceDto trace = traceMapper.toDto(po);

        String requestJson = po.getRequestJson();
        if (requestJson == null || requestJson.isBlank()) {
            throw new BadRequestException(
                    "This trace was created before the fix feature was available. "
                    + "No verification context saved. Please re-run verification to enable fix.");
        }

        VerificationRequestDto request = JsonUtils.fromJson(requestJson, VerificationRequestDto.class);
        if (request == null || request.getDevices() == null || request.getDevices().isEmpty()) {
            throw new BadRequestException("Invalid verification context in trace requestJson.");
        }

        Map<String, DeviceManifest> templateManifests = JsonUtils.fromJson(
                po.getTemplateSnapshotsJson(), new TypeReference<Map<String, DeviceManifest>>() {});
        if (templateManifests == null || templateManifests.isEmpty()) {
            throw new BadRequestException(
                    "This trace does not contain the exact device-template snapshot used for verification. "
                    + "Please re-run verification before requesting or applying an automatic fix.");
        }

        log.debug("Loaded verification context for trace {}", traceId);

        return new VerificationContext(trace, request, Map.copyOf(templateManifests));
    }

    private ModelBoundaryInput modelBoundaryInput(VerificationRequestDto request,
                                                  Map<String, DeviceManifest> templateManifests) {
        List<DeviceVerificationDto> devices = request.getDevices() == null ? List.of() : request.getDevices();
        Map<String, DeviceSmvData> rawDeviceSmvMap =
                smvGenerator.buildDeviceSmvMapFromTemplateSnapshots(devices, templateManifests);
        List<BoardEnvironmentVariableDto> environmentVariables = NusmvEnvironmentPool.mergeWithDefaults(
                request.getEnvironmentVariables(), rawDeviceSmvMap);
        request.setEnvironmentVariables(environmentVariables);
        List<DeviceVerificationDto> expandedDevices = NusmvEnvironmentPool.expandDevices(
                devices, environmentVariables, rawDeviceSmvMap);
        Map<String, DeviceSmvData> expandedDeviceSmvMap =
                smvGenerator.buildDeviceSmvMapFromTemplateSnapshots(expandedDevices, templateManifests);
        return new ModelBoundaryInput(expandedDevices, environmentVariables, expandedDeviceSmvMap);
    }

    private record VerificationContext(TraceDto trace,
                                       VerificationRequestDto request,
                                       Map<String, DeviceManifest> templateManifests) {}

    private record ModelBoundaryInput(List<DeviceVerificationDto> devices,
                                      List<BoardEnvironmentVariableDto> environmentVariables,
                                      Map<String, DeviceSmvData> deviceSmvMap) {}

    private record CurrentBoardSemanticContext(List<DeviceVerificationDto> currentDevices,
                                               Map<String, DeviceSmvData> currentDeviceSmvMap) {}
}
