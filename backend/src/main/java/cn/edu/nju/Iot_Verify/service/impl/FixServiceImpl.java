package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.FixStrategyApplier;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.BoardSemanticFingerprint;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.regex.Pattern;

@Slf4j
@Service
@RequiredArgsConstructor
public class FixServiceImpl implements FixService {

    private static final Pattern PARAM_KEY_PATTERN = Pattern.compile("r\\d+_c\\d+");

    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final SmvGenerator smvGenerator;
    private final RuleFixer ruleFixer;
    private final FixConfig fixConfig;
    private final DeviceTemplateRepository deviceTemplateRepository;
    private final BoardStorageService boardStorageService;
    private final BoardDataConverter boardDataConverter;

    @Override
    @Transactional(readOnly = true)
    public List<FaultRuleDto> localizeFault(Long userId, Long traceId) {
        VerificationContext ctx = loadContext(userId, traceId);
        Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, ctx.request.getDevices());
        return ruleFixer.localizeFaults(ctx.trace.getStates(), ctx.request.getRules(), deviceSmvMap);
    }

    @Override
    @Transactional(readOnly = true)
    public FixResultDto fix(Long userId, Long traceId, List<String> strategies,
                            Map<String, PreferredRange> preferredRanges) {
        validatePreferredRanges(preferredRanges);
        VerificationContext ctx = loadContext(userId, traceId);
        VerificationRequestDto req = ctx.request;
        Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, req.getDevices());

        FixResultDto result = ruleFixer.fix(
                traceId,
                ctx.trace.getViolatedSpecId(),
                ctx.trace.getStates(),
                req.getRules(),
                req.getDevices(),
                req.getSpecs(),
                deviceSmvMap,
                userId,
                req.isAttack(),
                req.getIntensity(),
                req.isEnablePrivacy(),
                strategies,
                fixConfig.getMaxAttempts(),
                preferredRanges
        );

        // Template drift detection: warn if templates were modified after the trace was recorded
        appendDriftWarningIfNeeded(result, userId, req, ctx.trace);

        return result;
    }

    @Override
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
        validatePreferredRanges(preferredRanges);
        // Load the trace's verification-time snapshot (normalized rules) for index/fingerprint alignment.
        VerificationContext ctx = loadContext(userId, traceId);
        List<RuleDto> snapshotRules = ctx.request.getRules();
        if (snapshotRules == null || snapshotRules.isEmpty()) {
            throw new BadRequestException("Verification context has no rules; cannot apply fix.");
        }

        // Template-drift guard (checked BEFORE the expensive NuSMV recompute): applyFix rebuilds the
        // device model from the CURRENT templates, so if a template used by the trace changed after the
        // trace was recorded, the recompute would prove (and persist) a fix against a different model than
        // the one that produced the counterexample. Reject rather than silently apply a stale fix. Unlike
        // /fix — which only warns — apply blocks. (This is one cheap DB query vs. a full NuSMV run.)
        assertTemplatesUnchanged(userId, ctx);

        Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, ctx.request.getDevices());

        // SECURITY: do NOT trust the client's suggestion.verified flag. Re-derive the fix server-side
        // for the requested strategy against the trace's own context, and require that the client's
        // suggestion matches a freshly-recomputed, NuSMV-verified server suggestion. This makes the
        // "only apply verified suggestions" guarantee independent of any client-supplied boolean.
        FixSuggestionDto trusted = recomputeVerifiedSuggestion(userId, ctx, strategy, deviceSmvMap, preferredRanges);
        if (trusted == null) {
            throw new BadRequestException("Could not reproduce a verified '" + strategy
                    + "' fix for this trace (the board or templates may have changed). "
                    + "Please re-run the fix and try again.");
        }
        if (!suggestionsEquivalent(strategy, suggestion, trusted, deviceSmvMap)) {
            throw new BadRequestException("The submitted fix no longer matches the current verified '"
                    + strategy + "' suggestion. Please re-run the fix and apply the updated suggestion.");
        }

        // Read current rules → drift check → apply → save, all inside ONE per-user lock + transaction.
        // This closes the race where a concurrent save could interleave between an unlocked read and the
        // locked write, letting apply overwrite freshly-saved rules with a stale list. The drift check
        // runs on the exact snapshot that gets written.
        int[] before = {0};
        List<RuleDto> saved = boardStorageService.updateRules(userId, boardRules -> {
            before[0] = boardRules.size();
            // Spec/device drift guard: run inside the same per-user write lock as the final save, so a
            // concurrent spec/device edit cannot slip in after the check but before persistence.
            CurrentBoardSemanticContext currentBoard = assertSpecsAndDevicesUnchanged(userId, ctx, deviceSmvMap);
            // Guard against board drift: the snapshot the fix was computed against must still line up
            // with the current board rules by index + ordered fingerprint. Otherwise ruleIndex/
            // conditionIndex could point at a different rule/condition now and we'd corrupt it.
            assertBoardAlignedWithSnapshot(boardRules, snapshotRules, deviceSmvMap);
            // Apply the SERVER-recomputed suggestion (not the client's), so the persisted change is
            // exactly what NuSMV just verified.
            Map<String, String> persistenceDeviceNames = buildPersistenceDeviceNameAliases(
                    currentBoard.currentDevices(), deviceSmvMap, currentBoard.currentDeviceSmvMap());
            return FixStrategyApplier.apply(strategy, trusted, boardRules, deviceSmvMap, persistenceDeviceNames);
        });
        log.info("Applied '{}' fix for trace {} (user {}): {} rule(s) -> {} rule(s)",
                strategy, traceId, userId, before[0], saved.size());

        return FixApplyResultDto.builder()
                .applied(true)
                .strategy(strategy)
                .message(buildApplyMessage(strategy, trusted, before[0], saved.size()))
                .rules(saved)
                .build();
    }

    /**
     * Recompute the fix for a single strategy against the trace's own verification context and return
     * the verified suggestion for that strategy, or {@code null} if none was produced/verified.
     */
    private FixSuggestionDto recomputeVerifiedSuggestion(Long userId, VerificationContext ctx,
                                                         String strategy,
                                                         Map<String, DeviceSmvData> deviceSmvMap,
                                                         Map<String, PreferredRange> preferredRanges) {
        VerificationRequestDto req = ctx.request;
        FixResultDto recomputed = ruleFixer.fix(
                null,
                ctx.trace.getViolatedSpecId(),
                ctx.trace.getStates(),
                req.getRules(),
                req.getDevices(),
                req.getSpecs(),
                deviceSmvMap,
                userId,
                req.isAttack(),
                req.getIntensity(),
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
            case "disable":
                return Objects.equals(
                        sortedInts(client.getDisabledRuleIndices()),
                        sortedInts(server.getDisabledRuleIndices()));
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
                        + a.getAttribute() + ":" + a.getDeviceName() + ":" + a.getRelation() + ":" + a.getValue())
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
     * Alignment = same rule count AND each rule's condition fingerprints (device varName|attr|rel|value)
     * match position-by-position. If the user edited/added/removed rules after verifying, indices in the
     * suggestion would be stale, so we reject rather than risk editing the wrong rule.
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
                throw new BadRequestException("Rule #" + i + " changed since verification. "
                        + "Please re-run verification before applying a fix.");
            }
        }
    }

    /**
     * Reject the apply if any device template used by the trace was modified after the trace was
     * recorded. applyFix rebuilds {@code deviceSmvMap} from the CURRENT templates, so template drift
     * means the server would prove (and persist) a fix against a different NuSMV model than the one that
     * produced the counterexample. Unlike {@code /fix} — which only warns — apply must not silently
     * commit a stale fix, so this blocks with a 400.
     */
    private void assertTemplatesUnchanged(Long userId, VerificationContext ctx) {
        if (hasTemplateDrift(userId, ctx.request, ctx.trace, /* failClosed */ true)) {
            throw new BadRequestException("Device template(s) were modified after this trace was recorded. "
                    + "The fix may no longer match the verification model. "
                    + "Please re-run verification before applying a fix.");
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
     * normalized, empty variable/privacy lists manifest-defaulted, values de-quoted — so an untouched
     * board matches its frontend-transformed snapshot instead of misfiring (the failure mode of the
     * earlier byte-equality attempt). {@code snapshotDeviceSmvMap} was built from the snapshot devices;
     * the current board gets its own map so empty lists default against the same manifests.</p>
     */
    private CurrentBoardSemanticContext assertSpecsAndDevicesUnchanged(Long userId, VerificationContext ctx,
                                                                       Map<String, DeviceSmvData> snapshotDeviceSmvMap) {
        List<DeviceVerificationDto> currentDevices = boardDataConverter.getDevicesForVerification(userId);
        List<SpecificationDto> currentSpecs = boardStorageService.getSpecs(userId);
        if (currentSpecs == null) {
            currentSpecs = List.of();
        }

        Map<String, DeviceSmvData> currentDeviceSmvMap;
        try {
            currentDeviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, currentDevices);
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
                ctx.request.getDevices(), ctx.request.getSpecs(), snapshotDeviceSmvMap);
        String currentFp = BoardSemanticFingerprint.of(
                currentDevices, currentSpecs, currentDeviceSmvMap);

        if (!snapshotFp.equals(currentFp)) {
            log.info("Spec/device drift detected for trace {} (user {})", ctx.trace.getId(), userId);
            throw new BadRequestException("Specifications or device state changed since verification. "
                    + "The fix was verified against the earlier model. "
                    + "Please re-run verification before applying a fix.");
        }
        return new CurrentBoardSemanticContext(currentDevices, currentDeviceSmvMap);
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

    private Map<String, String> buildPersistenceDeviceNameAliases(
            List<DeviceVerificationDto> currentDevices,
            Map<String, DeviceSmvData> snapshotDeviceSmvMap,
            Map<String, DeviceSmvData> currentDeviceSmvMap) {
        Map<String, String> aliases = new LinkedHashMap<>();
        if (currentDevices == null || currentDevices.isEmpty()) {
            return aliases;
        }
        for (DeviceVerificationDto device : currentDevices) {
            if (device == null) continue;
            String persistedName = trimToNull(device.getVarName());
            if (persistedName == null) continue;
            putAlias(aliases, persistedName, persistedName);
            putAlias(aliases, DeviceNameNormalizer.normalize(persistedName), persistedName);
            putResolvedAlias(aliases, persistedName, snapshotDeviceSmvMap);
            putResolvedAlias(aliases, persistedName, currentDeviceSmvMap);
        }
        return aliases;
    }

    private void putResolvedAlias(Map<String, String> aliases, String persistedName,
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        try {
            DeviceSmvData smv = DeviceReferenceResolver.resolve(
                    persistedName, DeviceNameNormalizer.normalize(persistedName), deviceSmvMap);
            if (smv != null) {
                putAlias(aliases, smv.getVarName(), persistedName);
            }
        } catch (Exception e) {
            log.debug("Could not build persistence alias for device '{}': {}", persistedName, e.getMessage());
        }
    }

    private void putAlias(Map<String, String> aliases, String alias, String persistedName) {
        String key = trimToNull(alias);
        String value = trimToNull(persistedName);
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
     * Resolve a device reference to its SMV varName, canonicalizing digit-leading names first.
     * The trace snapshot names devices with the frontend transform ({@code 1Lamp} → {@code d_1Lamp});
     * the persisted board rules carry the raw label ({@code 1Lamp}). Normalizing both before resolution
     * lets the two denote the same device instead of producing a spurious drift rejection.
     */
    private String resolveVar(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        return FixStrategyApplier.resolveVarName(DeviceNameNormalizer.normalize(deviceName), deviceSmvMap);
    }

    /**
     * Return a copy of the condition with its deviceName canonicalized (digit-leading → {@code d_}),
     * so condition fingerprints computed from raw board rules line up with the normalized snapshot.
     * The original condition is not mutated.
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
                return "Applied " + pCount + " parameter adjustment(s) to your rules.";
            case "condition":
                int cCount = suggestion.getConditionAdjustments() == null ? 0
                        : (int) suggestion.getConditionAdjustments().stream()
                                .filter(a -> !"keep".equals(a.getAction())).count();
                return "Applied " + cCount + " condition change(s) to your rules.";
            case "disable":
                return "Disabled " + (before - after) + " rule(s).";
            default:
                return "Fix applied.";
        }
    }

    private void appendDriftWarningIfNeeded(FixResultDto result, Long userId,
                                            VerificationRequestDto req, TraceDto trace) {
        if (hasTemplateDrift(userId, req, trace, /* failClosed */ false)) {
            String warning = "WARNING: Device template(s) were modified after this trace was recorded. "
                    + "Fix suggestions may not match the original verification context.";
            String base = result.getSummary() != null ? result.getSummary() : "";
            result.setSummary(base.isEmpty() ? warning : base + " " + warning);
        }
    }

    /**
     * True if any device template referenced by the trace's request was modified after the trace was
     * recorded. Shared by {@code /fix} (warns) and {@code /apply} (blocks).
     *
     * <p>Behaviour on a template-repo error is governed by {@code failClosed}:</p>
     * <ul>
     *   <li>{@code /fix} passes {@code false} (fail-open): a transient repo issue must not wedge the
     *       advisory warning path — the worst case is a missing warning.</li>
     *   <li>{@code /apply} passes {@code true} (fail-closed): if we cannot confirm templates are
     *       unchanged, we must not persist a fix that might have been proved against a drifted model,
     *       so we treat an unverifiable check as drift and let the caller reject.</li>
     * </ul>
     */
    private boolean hasTemplateDrift(Long userId, VerificationRequestDto req, TraceDto trace, boolean failClosed) {
        if (trace.getCreatedAt() == null) return false;

        List<String> templateNames = req.getDevices().stream()
                .map(DeviceVerificationDto::getTemplateName)
                .filter(Objects::nonNull)
                .filter(n -> !n.isBlank())
                // toLowerCase(Locale.ROOT) is safe: template names are restricted to
                // printable ASCII (validated by SAFE_TEMPLATE_NAME in both
                // addDeviceTemplate and initDefaultTemplates)
                .map(n -> n.toLowerCase(Locale.ROOT))
                .distinct()
                .toList();
        if (templateNames.isEmpty()) return false;

        try {
            boolean drifted = deviceTemplateRepository.existsModifiedAfter(
                    userId, templateNames, trace.getCreatedAt());
            if (drifted) {
                log.warn("Template drift detected for trace (createdAt={})", trace.getCreatedAt());
            }
            return drifted;
        } catch (Exception e) {
            if (failClosed) {
                // apply path: we could not confirm templates are unchanged, so we must not persist a
                // potentially-stale fix. Treat the unverifiable check as drift.
                log.warn("Template drift check failed on apply path; failing closed: {}", e.getMessage());
                return true;
            }
            log.debug("Template drift check failed (non-critical): {}", e.getMessage());
            return false;
        }
    }

    private void validatePreferredRanges(Map<String, PreferredRange> ranges) {
        if (ranges == null) return;
        for (Map.Entry<String, PreferredRange> entry : ranges.entrySet()) {
            String key = entry.getKey();
            if (key == null) {
                throw new BadRequestException("preferredRanges key must not be null");
            }
            PreferredRange pr = entry.getValue();
            if (!PARAM_KEY_PATTERN.matcher(key).matches()) {
                throw new BadRequestException("Invalid preferredRanges key '" + key
                        + "': must match 'r{ruleIdx}_c{condIdx}' (e.g. 'r0_c1')");
            }
            if (pr == null) {
                throw new BadRequestException("preferredRanges value for '" + key + "' must not be null");
            }
            if (pr.getLower() == null || pr.getUpper() == null) {
                throw new BadRequestException("preferredRanges entry '" + key
                        + "': lower and upper must not be null");
            }
            if (pr.getLower() > pr.getUpper()) {
                throw new BadRequestException("Invalid preferred range for '" + key
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

        // Note: deviceSmvMap is rebuilt from current templates, not a snapshot.
        // Template drift is detected post-fix via appendDriftWarningIfNeeded().
        log.debug("Loaded verification context for trace {}", traceId);

        return new VerificationContext(trace, request);
    }

    private record VerificationContext(TraceDto trace, VerificationRequestDto request) {}

    private record CurrentBoardSemanticContext(List<DeviceVerificationDto> currentDevices,
                                               Map<String, DeviceSmvData> currentDeviceSmvMap) {}
}
