package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import lombok.extern.slf4j.Slf4j;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
            SmvGenerator.GenerateResult genResult = smvGenerator.generate(
                    ctx.getUserId(), ctx.getDevices(), modifiedRules, ctx.getSpecs(),
                    ctx.isAttack(), ctx.getIntensity(), ctx.isEnablePrivacy());
            if (genResult == null) return false;
            smvFile = genResult.smvFile();

            NusmvResult result = nusmvExecutor.execute(smvFile);
            if (!result.isSuccess()) {
                log.warn("Forward verification: NuSMV execution failed: {}", result.getErrorMessage());
                return false;
            }

            boolean allPass = result.getSpecResults() != null
                    && !result.getSpecResults().isEmpty()
                    && result.getSpecResults().stream().allMatch(SpecCheckResult::isPassed);
            log.info("Forward verification result: allPass={}", allPass);
            return allPass;
        } catch (Exception e) {
            log.warn("Forward verification failed: {}", e.getMessage(), e);
            return false;
        } finally {
            cleanupTempDir(smvFile);
        }
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
     * [C5] Uses non-strict findDeviceSmvData() for inclusive matching
     * (false-positive less harmful than false-negative in scope expansion).
     * Known limitation: "domains" not supported — device-level only alignment.
     */
    public static Set<Integer> expandRuleIndices(
            List<FaultRuleDto> faultRules,
            List<RuleDto> allRules,
            SpecificationDto violatedSpec,
            Map<String, DeviceSmvData> deviceSmvMap) {

        Set<Integer> result = new LinkedHashSet<>();

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
                // [C5] non-strict: inclusive matching for scope expansion
                DeviceSmvData smv = DeviceSmvDataFactory.findDeviceSmvData(
                        sc.getDeviceId(), deviceSmvMap);
                if (smv != null) specVarNames.add(smv.getVarName());
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

    /**
     * [C5] Non-strict: resolve device name → varName for inclusive scope expansion.
     * Ambiguity returns arbitrary first match (false-positive acceptable).
     */
    private static String resolveVarNameInclusive(
            String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        DeviceSmvData smv = DeviceSmvDataFactory.findDeviceSmvData(deviceName, deviceSmvMap);
        return smv != null ? smv.getVarName() : null;
    }

    /**
     * Strict: resolve device name → varName, null on failure or ambiguity.
     * Used by validateCandidateCondition / conditionFingerprint where
     * precision matters (false-positive = broken SMV model).
     */
    static String resolveVarNameSafe(
            String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        try {
            DeviceSmvData smv = DeviceSmvDataFactory.findDeviceSmvDataStrict(deviceName, deviceSmvMap);
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

            if (!"state".equals(targetType) && !"variable".equals(targetType)) continue;

            RuleDto.Condition candidate;
            if ("state".equals(targetType)) {
                candidate = RuleDto.Condition.builder()
                        .deviceName(sc.getDeviceId())
                        .attribute("state")
                        .relation(sc.getRelation())
                        .value(sc.getValue())
                        .build();
            } else {
                candidate = RuleDto.Condition.builder()
                        .deviceName(sc.getDeviceId())
                        .attribute(sc.getKey())
                        .relation(sc.getRelation())
                        .value(sc.getValue())
                        .build();
            }

            if (!validateCandidateCondition(candidate, deviceSmvMap)) {
                log.debug("extractCandidates: candidate from spec ({}/{}) failed validation, skipping",
                        sc.getDeviceId(), sc.getKey());
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
     * Validate that a candidate condition can be compiled by SmvMainModuleBuilder
     * without triggering fail-closed (FALSE for entire rule).
     */
    static boolean validateCandidateCondition(
            RuleDto.Condition candidate,
            Map<String, DeviceSmvData> deviceSmvMap) {
        // 1. Device resolvable and unambiguous
        DeviceSmvData smv;
        try {
            smv = DeviceSmvDataFactory.findDeviceSmvDataStrict(
                    candidate.getDeviceName(), deviceSmvMap);
        } catch (SmvGenerationException e) {
            return false;
        }
        if (smv == null) return false;

        // 2. Value non-blank
        if (candidate.getValue() == null || candidate.getValue().isBlank()) return false;

        // 3. Attribute resolvable
        String attr = candidate.getAttribute();
        if (attr == null || attr.isBlank()) return false;

        // 4. Relation valid (type-specific)
        if (candidate.getRelation() == null) return false;
        String normalizedRel = SmvRelationUtils.normalizeRelation(candidate.getRelation());

        if ("state".equals(attr)) {
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
        } else {
            // Non-state: general relation validation
            if (!SmvRelationUtils.isSupportedRelation(normalizedRel)) return false;

            boolean foundInVars = smv.getVariables() != null && smv.getVariables().stream()
                    .anyMatch(v -> attr.equals(v.getName()));
            if (foundInVars) return true;
            if (smv.getEnvVariables() != null) {
                String envKey = attr.startsWith("a_") ? attr.substring(2) : attr;
                return smv.getEnvVariables().containsKey(envKey);
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

    /**
     * Fingerprint = "varName|attribute|normalizedRelation|normalizedValue".
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
                    smv = DeviceSmvDataFactory.findDeviceSmvDataStrict(c.getDeviceName(), deviceSmvMap);
                } catch (SmvGenerationException ignored) { }
            }
            if (smv != null && smv.getModes() != null) {
                modeCount = smv.getModes().size();
            }
        }
        String normVal = SmvRelationUtils.cleanRuleValueByRelation(normRel, c.getValue(), modeCount);
        if (normVal == null) normVal = "";
        String attr = c.getAttribute() != null ? c.getAttribute() : "";
        return varName + "|" + attr + "|" + normRel + "|" + normVal;
    }
}
