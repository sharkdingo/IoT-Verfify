package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import lombok.extern.slf4j.Slf4j;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Shared utilities for fix strategy implementations.
 */
@Slf4j
public final class FixStrategyUtils {

    private FixStrategyUtils() {}

    /**
     * Forward-verify: regenerate the SMV model with modified rules and check all specs pass.
     */
    public static boolean forwardVerify(SmvGenerator smvGenerator, NusmvExecutor nusmvExecutor,
                                         FixContext ctx, List<RuleDto> modifiedRules) {
        if (ctx.isExpired()) return false;
        File smvFile = null;
        try {
            SmvGenerator.GenerateResult genResult = generateResolved(
                    smvGenerator, ctx, modifiedRules, SmvGenerator.GeneratePurpose.VERIFICATION);
            if (genResult == null) return false;
            smvFile = genResult.smvFile();

            if (genResult.disabledRuleCount() > 0 || genResult.skippedSpecCount() > 0) {
                String diagnostic = "A candidate was rejected because forward verification generated an incomplete model ("
                        + genResult.disabledRuleCount() + " rule(s) disabled, "
                        + genResult.skippedSpecCount() + " specification(s) skipped).";
                ctx.addDiagnostic(diagnostic);
                log.warn("Forward verification rejected incomplete generated model: disabledRules={}, skippedSpecs={}",
                        genResult.disabledRuleCount(), genResult.skippedSpecCount());
                return false;
            }

            NusmvResult result = executeWithinDeadline(nusmvExecutor, smvFile, ctx);
            if (!result.isSuccess()) {
                log.warn("Forward verification: NuSMV execution failed: {}", result.getErrorMessage());
                ctx.addDiagnostic("A candidate could not be confirmed because NuSMV forward verification failed.");
                return false;
            }

            List<SpecCheckResult> specResults = result.getSpecResults();
            int expectedSpecCount = ctx.getSpecs() != null ? ctx.getSpecs().size() : 0;
            boolean resultCountComplete = specResults != null
                    && !specResults.isEmpty()
                    && (expectedSpecCount == 0 || specResults.size() == expectedSpecCount);
            boolean emittedCountComplete = genResult.emittedSpecs() == null
                    || genResult.emittedSpecs().isEmpty()
                    || expectedSpecCount == 0
                    || genResult.emittedSpecs().size() == expectedSpecCount;
            if (!resultCountComplete || !emittedCountComplete) {
                ctx.addDiagnostic("A candidate was rejected because forward verification did not return one reliable result for every specification.");
                log.warn("Forward verification rejected incomplete result set: expected={}, emitted={}, parsed={}",
                        expectedSpecCount,
                        genResult.emittedSpecs() != null ? genResult.emittedSpecs().size() : 0,
                        specResults != null ? specResults.size() : 0);
                return false;
            }

            boolean allPass = specResults.stream().allMatch(SpecCheckResult::isPassed);
            log.info("Forward verification result: allPass={}", allPass);
            return allPass;
        } catch (Exception e) {
            log.warn("Forward verification failed: {}", e.getMessage(), e);
            ctx.addDiagnostic("A candidate could not be confirmed because forward verification encountered an error.");
            return false;
        } finally {
            cleanupTempDir(smvFile);
        }
    }

    public static SmvGenerator.GenerateResult generateResolved(
            SmvGenerator smvGenerator,
            FixContext ctx,
            List<RuleDto> rules,
            SmvGenerator.GeneratePurpose purpose) throws java.io.IOException {
        AttackScenarioDto scenario = ctx.resolvedAttackScenario();
        if (!preservesExactAutomationLinkSelection(scenario, rules)) {
            ctx.addDiagnostic("A candidate was rejected because it would remove or duplicate an explicitly selected automation-link attack point and change the original attack scenario.");
            return null;
        }
        if (scenario.getMode() == AttackScenarioDto.Mode.EXACT_POINTS) {
            return smvGenerator.generateWithResolvedDeviceModel(
                    ctx.getUserId(), ctx.getDevices(), ctx.getEnvironmentVariables(), rules, ctx.getSpecs(),
                    scenario, ctx.isEnablePrivacy(), purpose, tempContext(ctx), ctx.getDeviceSmvMap());
        }
        return smvGenerator.generateWithResolvedDeviceModel(
                ctx.getUserId(), ctx.getDevices(), ctx.getEnvironmentVariables(), rules, ctx.getSpecs(),
                scenario.isEnabled(), scenario.effectiveBudget(), ctx.isEnablePrivacy(), purpose,
                tempContext(ctx), ctx.getDeviceSmvMap());
    }

    public static SmvGenerator.GenerateResult generateParameterizedResolved(
            SmvGenerator smvGenerator,
            FixContext ctx,
            List<RuleDto> rules,
            ParameterizationConfig config) throws java.io.IOException {
        AttackScenarioDto scenario = ctx.resolvedAttackScenario();
        if (!preservesExactAutomationLinkSelection(scenario, rules)) {
            ctx.addDiagnostic("A candidate was rejected because it would remove or duplicate an explicitly selected automation-link attack point and change the original attack scenario.");
            return null;
        }
        if (scenario.getMode() == AttackScenarioDto.Mode.EXACT_POINTS) {
            return smvGenerator.generateParameterizedWithResolvedDeviceModel(
                    ctx.getUserId(), ctx.getDevices(), ctx.getEnvironmentVariables(), rules, ctx.getSpecs(),
                    scenario, ctx.isEnablePrivacy(), config, tempContext(ctx), ctx.getDeviceSmvMap());
        }
        return smvGenerator.generateParameterizedWithResolvedDeviceModel(
                ctx.getUserId(), ctx.getDevices(), ctx.getEnvironmentVariables(), rules, ctx.getSpecs(),
                scenario.isEnabled(), scenario.effectiveBudget(), ctx.isEnablePrivacy(), config,
                tempContext(ctx), ctx.getDeviceSmvMap());
    }

    static boolean preservesExactAutomationLinkSelection(AttackScenarioDto scenario,
                                                           List<RuleDto> rules) {
        if (scenario == null || scenario.getMode() != AttackScenarioDto.Mode.EXACT_POINTS) {
            return true;
        }
        Set<Long> selectedRuleIds = scenario.selectedAutomationLinkRuleIds();
        if (selectedRuleIds.isEmpty()) {
            return true;
        }
        Map<Long, Integer> ruleIdCounts = new HashMap<>();
        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule != null && rule.getId() != null) {
                    ruleIdCounts.merge(rule.getId(), 1, Integer::sum);
                }
            }
        }
        return selectedRuleIds.stream().allMatch(ruleId -> ruleIdCounts.getOrDefault(ruleId, 0) == 1);
    }

    /**
     * Deep-copy rules including conditions and command, so modifications don't affect the originals.
     */
    public static List<RuleDto> deepCopyRules(List<RuleDto> rules) {
        List<RuleDto> copy = new ArrayList<>();
        for (RuleDto rule : rules) {
            List<RuleDto.Condition> condCopy = new ArrayList<>();
            if (rule.getConditions() != null) {
                for (RuleDto.Condition c : rule.getConditions()) {
                    condCopy.add(RuleDto.Condition.builder()
                            .deviceName(c.getDeviceName())
                            .attribute(c.getAttribute())
                            .targetType(c.getTargetType())
                            .relation(c.getRelation())
                            .value(c.getValue())
                            .build());
                }
            }
            RuleDto.Command cmdCopy = null;
            if (rule.getCommand() != null) {
                RuleDto.Command cmd = rule.getCommand();
                cmdCopy = RuleDto.Command.builder()
                        .deviceName(cmd.getDeviceName())
                        .action(cmd.getAction())
                        .contentDevice(cmd.getContentDevice())
                        .content(cmd.getContent())
                        .build();
            }
            copy.add(RuleDto.builder()
                    .id(rule.getId())
                    .userId(rule.getUserId())
                    .conditions(condCopy)
                    .command(cmdCopy)
                    .ruleString(rule.getRuleString())
                    .build());
        }
        return copy;
    }

    /**
     * Clean up the temp directory containing the SMV file.
     */
    public static void cleanupTempDir(File smvFile) {
        if (smvFile == null) return;
        try {
            File parentDir = smvFile.getParentFile();
            if (parentDir != null && parentDir.exists()) {
                File[] files = parentDir.listFiles();
                if (files != null) {
                    for (File f : files) {
                        if (!f.delete()) {
                            log.debug("Failed to delete temp file: {}", f);
                        }
                    }
                }
                if (!parentDir.delete()) {
                    log.debug("Failed to delete temp dir: {}", parentDir);
                }
            }
        } catch (Exception e) {
            log.debug("Failed to clean up temp dir: {}", e.getMessage());
        }
    }

    // ======================== E2: Expand parameterization scope ========================

    /**
     * §5: faultRules ∪ rules sharing devices with violated spec.
     * Uses the same device-reference resolver as the generator so scope expansion aligns raw board
     * node ids with SMV-safe verification-time varNames consistently.
     * Known limitation: "domains" not supported — device-level only alignment.
     */
    public static Set<Integer> expandRuleIndices(
            List<FaultRuleDto> faultRules,
            List<RuleDto> allRules,
            SpecificationDto violatedSpec,
            Map<String, DeviceSmvData> deviceSmvMap) {

        Set<Integer> result = new LinkedHashSet<>();
        if (allRules == null || allRules.isEmpty()) {
            return result;
        }

        // 1. Collect fault rule indices
        if (faultRules != null) {
            for (FaultRuleDto fr : faultRules) {
                int idx = fr.getRuleIndex();
                if (idx >= 0 && idx < allRules.size()) {
                    result.add(idx);
                }
            }
        }

        // 2. Extract spec device varNames
        Set<String> specVarNames = new HashSet<>();
        if (violatedSpec != null) {
            List<SpecConditionDto> allSpecConds = new ArrayList<>();
            if (violatedSpec.getAConditions() != null) allSpecConds.addAll(violatedSpec.getAConditions());
            if (violatedSpec.getIfConditions() != null) allSpecConds.addAll(violatedSpec.getIfConditions());
            if (violatedSpec.getThenConditions() != null) allSpecConds.addAll(violatedSpec.getThenConditions());

            for (SpecConditionDto sc : allSpecConds) {
                if (sc.getDeviceId() == null || sc.getDeviceId().isBlank()) continue;
                String varName = resolveVarNameInclusive(sc.getDeviceId(), deviceSmvMap);
                if (varName != null) specVarNames.add(varName);
            }
        }

        if (specVarNames.isEmpty()) return result;

        // 3. Scan allRules for shared-device rules
        for (int i = 0; i < allRules.size(); i++) {
            if (result.contains(i)) continue;
            RuleDto rule = allRules.get(i);
            if (ruleReferencesAnyDevice(rule, specVarNames, deviceSmvMap)) {
                result.add(i);
            }
        }
        return result;
    }

    /**
     * Check if rule references any device in targetVarNames (via conditions or command).
     */
    private static boolean ruleReferencesAnyDevice(
            RuleDto rule, Set<String> targetVarNames,
            Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() != null) {
            for (RuleDto.Condition cond : rule.getConditions()) {
                if (cond == null || cond.getDeviceName() == null) continue;
                String varName = resolveVarNameInclusive(cond.getDeviceName(), deviceSmvMap);
                if (varName != null && targetVarNames.contains(varName)) return true;
            }
        }
        if (rule.getCommand() != null && rule.getCommand().getDeviceName() != null) {
            String varName = resolveVarNameInclusive(rule.getCommand().getDeviceName(), deviceSmvMap);
            if (varName != null && targetVarNames.contains(varName)) return true;
        }
        return false;
    }

    static NusmvResult executeWithinDeadline(NusmvExecutor nusmvExecutor, File smvFile,
                                              FixContext ctx) throws InterruptedException {
        if (ctx.getDeadline() == null) {
            return nusmvExecutor.execute(smvFile);
        }
        long remainingMs = ctx.remainingMillis();
        if (remainingMs <= 0) {
            ctx.addDiagnostic("The automatic-fix deadline expired before the next NuSMV check started.");
            return NusmvResult.error("Automatic-fix deadline expired before NuSMV execution");
        }
        return nusmvExecutor.execute(smvFile, remainingMs);
    }

    static boolean hasEnvironmentPool(FixContext ctx) {
        return ctx != null && ctx.getEnvironmentVariables() != null && !ctx.getEnvironmentVariables().isEmpty();
    }

    static SmvGenerator.TempModelContext tempContext(FixContext ctx) {
        return SmvGenerator.TempModelContext.fixTrace(ctx != null ? ctx.getTraceId() : null);
    }

    /**
     * Resolve device reference → varName for scope expansion. Ambiguity is fail-closed
     * to match the generator's "do not silently bind to the wrong device" rule.
     */
    private static String resolveVarNameInclusive(
            String primaryRef, Map<String, DeviceSmvData> deviceSmvMap) {
        try {
            DeviceSmvData smv = DeviceReferenceResolver.resolve(primaryRef, deviceSmvMap);
            return smv != null ? smv.getVarName() : null;
        } catch (SmvGenerationException e) {
            log.warn("resolveVarNameInclusive: device reference '{}' failed, skipping: {}",
                    primaryRef, e.getMessage());
            return null;
        }
    }

    /**
     * Strict: resolve device name → varName, null on failure or ambiguity.
     * Used by validateCandidateCondition / conditionFingerprint where
     * precision matters (false-positive = broken SMV model).
     */
    static String resolveVarNameSafe(
            String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        try {
            DeviceSmvData smv = DeviceReferenceResolver.resolve(deviceName, deviceSmvMap);
            return smv != null ? smv.getVarName() : null;
        } catch (SmvGenerationException e) {
            log.warn("resolveVarNameSafe: ambiguous device '{}', skipping: {}", deviceName, e.getMessage());
            return null;
        }
    }

    // ======================== E1: Candidate condition extraction ========================

    /**
     * Extract candidate conditions from violated spec not already in the rule.
     * Dispatches by targetType; validates compilability; dedup by 4-tuple; truncates at max.
     */
    public static List<RuleDto.Condition> extractCandidateConditions(
            SpecificationDto violatedSpec,
            RuleDto rule,
            Map<String, DeviceSmvData> deviceSmvMap,
            int maxCandidatesPerRule) {

        if (violatedSpec == null) return Collections.emptyList();
        if (maxCandidatesPerRule <= 0) return Collections.emptyList();

        // 1. Build existing-condition fingerprint set for dedup
        Set<String> existingFingerprints = new HashSet<>();
        if (rule.getConditions() != null) {
            for (RuleDto.Condition c : rule.getConditions()) {
                String fp = conditionFingerprint(c, deviceSmvMap);
                if (fp != null) existingFingerprints.add(fp);
            }
        }

        // 2. Collect spec conditions (a + if + then)
        List<SpecConditionDto> allSpecConds = new ArrayList<>();
        if (violatedSpec.getAConditions() != null) allSpecConds.addAll(violatedSpec.getAConditions());
        if (violatedSpec.getIfConditions() != null) allSpecConds.addAll(violatedSpec.getIfConditions());
        if (violatedSpec.getThenConditions() != null) allSpecConds.addAll(violatedSpec.getThenConditions());

        // 3. Map, validate, dedup, truncate
        List<RuleDto.Condition> candidates = new ArrayList<>();
        Set<String> candidateFingerprints = new HashSet<>();

        for (SpecConditionDto sc : allSpecConds) {
            String targetType = sc.getTargetType();
            if (targetType == null) continue;
            targetType = targetType.toLowerCase();

            if (!"state".equals(targetType) && !"mode".equals(targetType) && !"variable".equals(targetType)) continue;

            String deviceRef = DeviceReferenceResolver.resolvableReference(
                    sc.getDeviceId(), deviceSmvMap);

            RuleDto.Condition candidate;
            if ("state".equals(targetType)) {
                candidate = RuleDto.Condition.builder()
                        .deviceName(deviceRef)
                        .attribute("state")
                        .targetType(targetType)
                        .relation(sc.getRelation())
                        .value(sc.getValue())
                        .build();
            } else if ("mode".equals(targetType)) {
                candidate = RuleDto.Condition.builder()
                        .deviceName(deviceRef)
                        .attribute(sc.getKey())
                        .targetType(targetType)
                        .relation(sc.getRelation())
                        .value(sc.getValue())
                        .build();
            } else {
                candidate = RuleDto.Condition.builder()
                        .deviceName(deviceRef)
                        .attribute(sc.getKey())
                        .targetType(targetType)
                        .relation(sc.getRelation())
                        .value(sc.getValue())
                        .build();
            }

            if (!validateCandidateCondition(candidate, deviceSmvMap)) {
                log.debug("extractCandidates: candidate from spec ({}/{}) failed validation, skipping",
                        deviceRef, sc.getKey());
                continue;
            }

            // A condition equal to the command's own resulting state is a postcondition, not a
            // meaningful trigger. Keeping it would turn e.g. "motion -> take photo" into
            // "camera already taking photo -> take photo", which can pass a safety property only
            // because the useful automation has become unreachable.
            if (isCommandOutcomeCondition(rule, candidate, deviceSmvMap)) {
                log.debug("extractCandidates: skipped command-outcome condition for rule command {}",
                        rule.getCommand() != null ? rule.getCommand().getAction() : "<none>");
                continue;
            }
            if (isCommandPrestateIncompatible(rule, candidate, deviceSmvMap)) {
                log.debug("extractCandidates: skipped condition incompatible with the command API pre-state for {}",
                        rule.getCommand() != null ? rule.getCommand().getAction() : "<none>");
                continue;
            }

            String fp = conditionFingerprint(candidate, deviceSmvMap);
            if (fp == null) continue;
            if (existingFingerprints.contains(fp) || candidateFingerprints.contains(fp)) continue;
            candidateFingerprints.add(fp);

            candidates.add(candidate);
            if (candidates.size() >= maxCandidatesPerRule) break;
        }
        return candidates;
    }

    /**
     * Whether a candidate condition is satisfied by the state that the same rule command produces.
     * Such a condition cannot initiate that command from its normal pre-state and is therefore a
     * misleading automatic-fix candidate. Negative conditions (for example {@code != taking_photo})
     * remain eligible when they can hold in the command's declared start state; a negative condition
     * that is false in every concrete start state is rejected as unreachable as well.
     */
    static boolean isCommandOutcomeCondition(
            RuleDto rule,
            RuleDto.Condition candidate,
            Map<String, DeviceSmvData> deviceSmvMap) {
        CommandApiContext command = commandApiContext(rule, candidate, deviceSmvMap);
        if (command == null) return false;
        DeviceSmvData commandDevice = command.device();
        DeviceManifest.API api = command.api();
        if (api == null || api.getEndState() == null || api.getEndState().isBlank()) {
            return false;
        }

        String relation = SmvRelationUtils.normalizeRelation(candidate.getRelation());
        // Only positive membership can be guaranteed by an action's result. != and not-in are
        // legitimate guards that prevent repeated commands and must remain eligible.
        if (!"=".equals(relation) && !"in".equals(relation)) {
            return false;
        }

        String targetType = candidate.getTargetType() == null
                ? ""
                : candidate.getTargetType().trim().toLowerCase();
        if ("mode".equals(targetType)) {
            int modeIndex = commandDevice.getModes() == null
                    ? -1
                    : commandDevice.getModes().indexOf(candidate.getAttribute());
            if (modeIndex < 0) return false;
            String endState = endStateForMode(commandDevice, api.getEndState(), modeIndex);
            return endState != null && positiveValueContains(relation, candidate.getValue(), endState);
        }
        if (!"state".equals(targetType) || !"state".equals(candidate.getAttribute())) {
            return false;
        }

        Map<String, String> endTuple = concreteEndState(commandDevice, api.getEndState());
        if (endTuple.isEmpty()) return false;
        List<String> candidateValues = "in".equals(relation)
                ? SmvRelationUtils.splitStateRuleValues(candidate.getValue(), commandDevice.getModes().size())
                : candidate.getValue() == null ? List.of() : List.of(candidate.getValue());
        return candidateValues.stream().anyMatch(value -> stateConditionMatchesTuple(
                commandDevice, value, endTuple));
    }

    /**
     * Whether a candidate condition is provably false whenever the command API is executable.
     * Wildcard API start-state segments remain eligible: they leave at least one model state in
     * which the condition and command can both hold, so this guard never rejects on uncertainty.
     */
    static boolean isCommandPrestateIncompatible(
            RuleDto rule,
            RuleDto.Condition candidate,
            Map<String, DeviceSmvData> deviceSmvMap) {
        CommandApiContext command = commandApiContext(rule, candidate, deviceSmvMap);
        if (command == null || command.api().getStartState() == null
                || command.api().getStartState().isBlank()) {
            return false;
        }
        DeviceSmvData commandDevice = command.device();
        String relation = SmvRelationUtils.normalizeRelation(candidate.getRelation());
        String targetType = candidate.getTargetType() == null
                ? ""
                : candidate.getTargetType().trim().toLowerCase();

        if ("mode".equals(targetType)) {
            int modeIndex = commandDevice.getModes() == null
                    ? -1
                    : commandDevice.getModes().indexOf(candidate.getAttribute());
            if (modeIndex < 0) return false;
            String startState = startStateForMode(commandDevice, command.api().getStartState(), modeIndex);
            if (startState == null) return false;
            List<String> values = "in".equals(relation) || "not in".equals(relation)
                    ? SmvRelationUtils.splitRuleValues(candidate.getValue())
                    : candidate.getValue() == null ? List.of() : List.of(candidate.getValue());
            boolean containsStart = values.stream()
                    .map(DeviceSmvDataFactory::cleanStateName)
                    .anyMatch(startState::equals);
            return switch (relation) {
                case "=" -> !containsStart;
                case "!=" -> containsStart;
                case "in" -> !containsStart;
                case "not in" -> containsStart;
                default -> false;
            };
        }
        if (!"state".equals(targetType) || !"state".equals(candidate.getAttribute())) {
            return false;
        }

        Map<String, String> startTuple = concreteStartState(commandDevice, command.api().getStartState());
        if (startTuple.isEmpty()) return false;
        List<String> values = "in".equals(relation) || "not in".equals(relation)
                ? SmvRelationUtils.splitStateRuleValues(candidate.getValue(), commandDevice.getModes().size())
                : candidate.getValue() == null ? List.of() : List.of(candidate.getValue());
        List<TupleMatch> matches = values.stream()
                .map(value -> compareCandidateToKnownState(commandDevice, value, startTuple))
                .toList();
        if (matches.isEmpty()) return false;
        return switch (relation) {
            case "=" -> matches.get(0) == TupleMatch.IMPOSSIBLE;
            case "!=" -> matches.get(0) == TupleMatch.DEFINITE;
            case "in" -> matches.stream().allMatch(match -> match == TupleMatch.IMPOSSIBLE);
            case "not in" -> matches.stream().anyMatch(match -> match == TupleMatch.DEFINITE);
            default -> false;
        };
    }

    private static CommandApiContext commandApiContext(
            RuleDto rule,
            RuleDto.Condition candidate,
            Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule == null || candidate == null || rule.getCommand() == null
                || deviceSmvMap == null || deviceSmvMap.isEmpty()) {
            return null;
        }
        String commandVar = resolveVarNameSafe(rule.getCommand().getDeviceName(), deviceSmvMap);
        String candidateVar = resolveVarNameSafe(candidate.getDeviceName(), deviceSmvMap);
        if (commandVar == null || !Objects.equals(commandVar, candidateVar)) {
            return null;
        }
        DeviceSmvData commandDevice = deviceSmvMap.get(commandVar);
        DeviceManifest.API api = commandDevice == null
                ? null
                : DeviceSmvDataFactory.findApi(commandDevice.getManifest(), rule.getCommand().getAction());
        return api == null ? null : new CommandApiContext(commandDevice, api);
    }

    private record CommandApiContext(DeviceSmvData device, DeviceManifest.API api) {}

    private enum TupleMatch {
        DEFINITE,
        POSSIBLE,
        IMPOSSIBLE
    }

    private static boolean positiveValueContains(String relation, String rawValue, String endState) {
        if (rawValue == null || endState == null) return false;
        if ("=".equals(relation)) {
            return Objects.equals(DeviceSmvDataFactory.cleanStateName(rawValue), endState);
        }
        return SmvRelationUtils.splitStateRuleValues(rawValue, 1).stream()
                .map(DeviceSmvDataFactory::cleanStateName)
                .anyMatch(endState::equals);
    }

    private static Map<String, String> concreteEndState(DeviceSmvData smv, String rawEndState) {
        return concreteApiState(smv, rawEndState, false);
    }

    private static Map<String, String> concreteStartState(DeviceSmvData smv, String rawStartState) {
        return concreteApiState(smv, rawStartState, true);
    }

    private static Map<String, String> concreteApiState(
            DeviceSmvData smv,
            String rawState,
            boolean allowWildcard) {
        List<String> modes = smv.getModes();
        if (modes == null || modes.isEmpty() || rawState == null) return Map.of();
        String[] parts = rawState.split(";", -1);
        if (modes.size() == 1) {
            String state = allowWildcard
                    ? DeviceSmvDataFactory.cleanStartState(rawState)
                    : DeviceSmvDataFactory.cleanStateName(rawState);
            return state == null || state.isBlank() || "_".equals(state)
                    ? Map.of()
                    : Map.of(modes.get(0), state);
        }
        if (parts.length != modes.size()) return Map.of();
        Map<String, String> result = new LinkedHashMap<>();
        for (int i = 0; i < modes.size(); i++) {
            String state = allowWildcard
                    ? DeviceSmvDataFactory.cleanStartState(parts[i])
                    : DeviceSmvDataFactory.cleanStateName(parts[i]);
            if (state == null || state.isBlank() || "_".equals(state)) continue;
            result.put(modes.get(i), state);
        }
        return result;
    }

    private static String endStateForMode(DeviceSmvData smv, String rawEndState, int modeIndex) {
        Map<String, String> endTuple = concreteEndState(smv, rawEndState);
        if (endTuple.isEmpty() || smv.getModes() == null || modeIndex >= smv.getModes().size()) return null;
        return endTuple.get(smv.getModes().get(modeIndex));
    }

    private static String startStateForMode(DeviceSmvData smv, String rawStartState, int modeIndex) {
        Map<String, String> startTuple = concreteStartState(smv, rawStartState);
        if (startTuple.isEmpty() || smv.getModes() == null || modeIndex >= smv.getModes().size()) return null;
        return startTuple.get(smv.getModes().get(modeIndex));
    }

    private static boolean stateConditionMatchesTuple(
            DeviceSmvData smv,
            String rawCandidate,
            Map<String, String> endTuple) {
        return compareCandidateToKnownState(smv, rawCandidate, endTuple) == TupleMatch.DEFINITE;
    }

    private static TupleMatch compareCandidateToKnownState(
            DeviceSmvData smv,
            String rawCandidate,
            Map<String, String> knownState) {
        Map<String, String> candidateTuple = resolveCandidateStateTuple(smv, rawCandidate);
        if (candidateTuple.isEmpty()) return TupleMatch.POSSIBLE;
        boolean hasUnknownState = false;
        for (Map.Entry<String, String> entry : candidateTuple.entrySet()) {
            String actual = knownState.get(entry.getKey());
            if (actual == null) {
                hasUnknownState = true;
            } else if (!Objects.equals(actual, entry.getValue())) {
                return TupleMatch.IMPOSSIBLE;
            }
        }
        return hasUnknownState ? TupleMatch.POSSIBLE : TupleMatch.DEFINITE;
    }

    private static Map<String, String> resolveCandidateStateTuple(
            DeviceSmvData smv,
            String rawCandidate) {
        if (smv == null || smv.getModes() == null || smv.getModes().isEmpty()
                || rawCandidate == null || rawCandidate.isBlank()) {
            return Map.of();
        }
        List<String> modes = smv.getModes();
        String candidate = rawCandidate.trim();
        if (candidate.contains(";") && modes.size() > 1) {
            String[] parts = candidate.split(";", -1);
            if (parts.length != modes.size()) return Map.of();
            Map<String, String> tuple = new LinkedHashMap<>();
            for (int i = 0; i < modes.size(); i++) {
                String state = DeviceSmvDataFactory.cleanStateName(parts[i]);
                if (state == null || state.isBlank() || "_".equals(state)) continue;
                List<String> legalStates = smv.getModeStates().get(modes.get(i));
                if (legalStates == null || !legalStates.contains(state)) return Map.of();
                tuple.put(modes.get(i), state);
            }
            return tuple;
        }

        String state = DeviceSmvDataFactory.cleanStateName(candidate);
        if (state == null || state.isBlank()) return Map.of();
        if (modes.size() == 1) {
            return Map.of(modes.get(0), state);
        }
        List<String> matchedModes = modes.stream()
                .filter(mode -> smv.getModeStates().getOrDefault(mode, List.of()).contains(state))
                .toList();
        return matchedModes.size() == 1 ? Map.of(matchedModes.get(0), state) : Map.of();
    }

    /**
     * Validate that a candidate condition can be compiled by SmvMainModuleBuilder
     * without triggering fail-closed (FALSE for entire rule).
     */
    static boolean validateCandidateCondition(
            RuleDto.Condition candidate,
            Map<String, DeviceSmvData> deviceSmvMap) {
        // 1. Device resolvable and unambiguous
        DeviceSmvData smv;
        try {
            smv = DeviceReferenceResolver.resolve(candidate.getDeviceName(), deviceSmvMap);
        } catch (SmvGenerationException e) {
            return false;
        }
        if (smv == null) return false;

        // 2. Value non-blank
        if (candidate.getValue() == null || candidate.getValue().isBlank()) return false;

        // 3. Attribute resolvable
        String attr = candidate.getAttribute();
        if (attr == null || attr.isBlank()) return false;
        String targetType = candidate.getTargetType();
        if (targetType == null || targetType.isBlank()) return false;
        targetType = targetType.toLowerCase();
        if (!"state".equals(targetType) && !"mode".equals(targetType) && !"variable".equals(targetType)) {
            return false;
        }

        // 4. Relation valid (type-specific)
        if (candidate.getRelation() == null) return false;
        String normalizedRel = SmvRelationUtils.normalizeRelation(candidate.getRelation());

        if ("state".equals(targetType)) {
            if (!"state".equals(attr)) return false;
            // State only allows = != in not_in (SmvMainModuleBuilder.buildRuleStateCondition:595-600)
            if (!"=".equals(normalizedRel) && !"!=".equals(normalizedRel)
                    && !"in".equals(normalizedRel) && !"not in".equals(normalizedRel)) {
                return false;
            }
            // Validate each state value exists in the device
            if (smv.getStates() == null || smv.getStates().isEmpty()) return false;
            if ("in".equals(normalizedRel) || "not in".equals(normalizedRel)) {
                // Mode-aware split: multi-mode devices use ; inside tuples (e.g. "cool;off")
                int modeCount = (smv.getModes() != null) ? smv.getModes().size() : 1;
                List<String> parts = SmvRelationUtils.splitStateRuleValues(candidate.getValue(), modeCount);
                if (parts.isEmpty()) return false;
                for (String part : parts) {
                    if (!isValidStateValue(smv, part)) return false;
                }
                return true;
            } else {
                return isValidStateValue(smv, candidate.getValue());
            }
        } else if ("mode".equals(targetType)) {
            if (!isModeAttribute(smv, attr)) return false;
            if (!"=".equals(normalizedRel) && !"!=".equals(normalizedRel)
                    && !"in".equals(normalizedRel) && !"not in".equals(normalizedRel)) {
                return false;
            }
            List<String> values = splitModeValues(candidate.getValue(), normalizedRel);
            if (values.isEmpty()) return false;
            if (("=".equals(normalizedRel) || "!=".equals(normalizedRel)) && values.size() != 1) {
                return false;
            }
            List<String> legalValues = smv.getModeStates() != null ? smv.getModeStates().get(attr) : null;
            if (legalValues == null || legalValues.isEmpty()) return false;
            for (String value : values) {
                String cleanValue = DeviceSmvDataFactory.cleanStateName(value);
                if (cleanValue == null || cleanValue.isBlank() || !legalValues.contains(cleanValue)) {
                    return false;
                }
            }
            return true;
        } else {
            // Non-state: general relation validation
            if (!SmvRelationUtils.isSupportedRelation(normalizedRel)) return false;

            boolean foundInVars = smv.getVariables() != null && smv.getVariables().stream()
                    .anyMatch(v -> attr.equals(v.getName()));
            if (foundInVars) return true;
            if (smv.getEnvVariables() != null) {
                return smv.getEnvVariables().containsKey(attr);
            }
            return false;
        }
    }

    /**
     * Check if a raw state value is valid for the given device.
     * Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate() semantics:
     * <ul>
     *   <li>No modes: reject (buildRuleStateCondition:591 requires modes)</li>
     *   <li>Multi-mode tuple (contains ;): split by ; → check each segment per-mode;
     *       all-wildcard tuple rejected (resolveStateTupleCandidate:697)</li>
     *   <li>Single-mode: cleanStateName → check against mode's state list</li>
     *   <li>Multi-mode single value (no ;): cleanStateName → valid if exactly one mode contains it</li>
     * </ul>
     */
    private static boolean isValidStateValue(DeviceSmvData smv, String rawValue) {
        if (rawValue == null || rawValue.isBlank()) return false;
        String trimmed = rawValue.trim();
        List<String> modes = smv.getModes();
        Map<String, List<String>> modeStates = smv.getModeStates();

        // No modes → state conditions cannot be resolved (SmvMainModuleBuilder:591-593)
        if (modes == null || modes.isEmpty()) return false;

        // Multi-mode tuple resolution: "cool;high" → split by ; → check per-mode
        if (trimmed.contains(";") && modes.size() > 1) {
            String[] segments = trimmed.split(";", -1);
            if (segments.length != modes.size()) return false;
            if (modeStates == null) return false;
            boolean anyNonWildcard = false;
            for (int i = 0; i < modes.size(); i++) {
                if (DeviceSmvDataFactory.isWildcardStateSegment(segments[i])) continue;
                String cleanSeg = DeviceSmvDataFactory.cleanStateName(segments[i]);
                if (cleanSeg == null || cleanSeg.isBlank()) continue; // wildcard
                anyNonWildcard = true;
                List<String> modeStateList = modeStates.get(modes.get(i));
                if (modeStateList == null || !modeStateList.contains(cleanSeg)) return false;
            }
            // All-wildcard tuple → empty map → null in generator (line 697)
            return anyNonWildcard;
        }

        // Single value
        String cleanValue = DeviceSmvDataFactory.cleanStateName(trimmed);
        if (cleanValue == null || cleanValue.isEmpty()) return false;

        // Single-mode: check against that mode's state list
        if (modes.size() == 1) {
            List<String> modeStateList = modeStates != null ? modeStates.get(modes.get(0)) : null;
            return modeStateList != null && modeStateList.contains(cleanValue);
        }

        // Multi-mode single value (no ;): valid if exactly one mode contains it
        // (SmvMainModuleBuilder:716-728 — ambiguous match → null)
        if (modeStates != null) {
            int matchCount = 0;
            for (String mode : modes) {
                List<String> modeStateList = modeStates.get(mode);
                if (modeStateList != null && modeStateList.contains(cleanValue)) {
                    matchCount++;
                }
            }
            return matchCount == 1;
        }

        return false;
    }

    private static boolean isModeAttribute(DeviceSmvData smv, String attr) {
        return smv != null && smv.getModes() != null && smv.getModes().contains(attr);
    }

    private static List<String> splitModeValues(String rawValue, String normalizedRel) {
        if (rawValue == null) {
            return List.of();
        }
        if ("in".equals(normalizedRel) || "not in".equals(normalizedRel)) {
            return Arrays.stream(rawValue.split("[,;|]"))
                    .map(String::trim)
                    .filter(v -> !v.isEmpty())
                    .toList();
        }
        String trimmed = rawValue.trim();
        return trimmed.isEmpty() ? List.of() : List.of(trimmed);
    }

    /**
     * Fingerprint = "varName|targetType|attribute|normalizedRelation|normalizedValue".
     * [C2] normalizedValue uses SmvRelationUtils.cleanRuleValueByRelation()
     * to match SmvMainModuleBuilder's normalization semantics exactly.
     * Mode-aware: for state IN/NOT_IN on multi-mode devices, preserves ; within tuples.
     * Returns null if device resolution fails.
     */
    static String conditionFingerprint(
            RuleDto.Condition c, Map<String, DeviceSmvData> deviceSmvMap) {
        if (c == null || c.getDeviceName() == null) return null;
        String varName = resolveVarNameSafe(c.getDeviceName(), deviceSmvMap);
        if (varName == null) return null;
        String normRel = SmvRelationUtils.normalizeRelation(c.getRelation());
        // Resolve mode count for mode-aware value normalization
        int modeCount = 1;
        if ("state".equals(c.getAttribute())) {
            DeviceSmvData smv = deviceSmvMap.get(varName);
            if (smv == null) {
                // Fallback: try resolving from device name
                try {
                    smv = DeviceReferenceResolver.resolve(c.getDeviceName(), deviceSmvMap);
                } catch (SmvGenerationException ignored) { }
            }
            if (smv != null && smv.getModes() != null) {
                modeCount = smv.getModes().size();
            }
        }
        String normVal = SmvRelationUtils.cleanRuleValueByRelation(normRel, c.getValue(), modeCount);
        if (normVal == null) normVal = "";
        String attr = c.getAttribute() != null ? c.getAttribute() : "";
        String targetType = c.getTargetType() != null ? c.getTargetType().toLowerCase() : "";
        return varName + "|" + targetType + "|" + attr + "|" + normRel + "|" + normVal;
    }
}
