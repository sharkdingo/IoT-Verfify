package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.util.EnvironmentDomainUtils;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * SMV 模型前置校验器（集中式）
 *
 * 在 SmvGenerator 生成 SMV 文本之前调用，提前发现模板/实例数据中的不合法项。
 * 所有硬性校验（会抛异常的）统一收口在此类，软性校验（仅 warn）也集中于此。
 */
@Slf4j
@Component
public class SmvModelValidator {

    /**
     * 执行全部校验。任何一项失败即抛出 SmvGenerationException。
     * 使用 IdentityHashMap 去重，确保同一 DeviceSmvData 对象只校验一次
     * （deviceSmvMap 中可能存在多个 key 指向同一对象的别名条目）。
     */
    public void validate(Map<String, DeviceSmvData> deviceSmvMap) {
        Set<DeviceSmvData> validated = Collections.newSetFromMap(new IdentityHashMap<>());
        for (DeviceSmvData smv : deviceSmvMap.values()) {
            if (smv.getManifest() == null) continue;
            if (!validated.add(smv)) continue;

            validateTriggerAttributes(smv);
            validateStartEndStates(smv);
            validateApiEventSemantics(smv);
            validateTrustPrivacyConsistency(smv);
            validatePropertyValues(smv);
            validateImpactedEnvironmentDefinitions(smv);
            validateVariableDomainsAndDynamics(smv);
        }
        validateEnvVarConflicts(deviceSmvMap);
    }

    /**
     * 软性校验：用户输入变量名是否存在于模板中（仅 warn，不抛异常）。
     * 从 DeviceSmvDataFactory 提取至此，由 Factory 调用。
     */
    public void warnUnknownUserVariables(DeviceSmvData smv, DeviceVerificationDto device) {
        if (device.getVariables() == null) return;
        Set<String> knownNames = new HashSet<>();
        for (DeviceManifest.InternalVariable v : smv.getVariables()) knownNames.add(v.getName());
        knownNames.addAll(smv.getEnvVariables().keySet());
        knownNames.addAll(smv.getImpactedEnvironmentVariables().keySet());

        for (VariableStateDto var : device.getVariables()) {
            if (var.getName() != null && !knownNames.contains(var.getName())) {
                log.warn("Device '{}' (template '{}'): user-provided variable '{}' not found in template, ignored",
                        device.getVarName(), device.getTemplateName(), var.getName());
            }
        }
    }

    /**
     * 软性校验：无模式传感器设备传入 state 时警告。
     * 从 DeviceSmvDataFactory 提取至此，由 Factory 调用。
     */
    public void warnStatelessDeviceWithState(DeviceSmvData smv, DeviceVerificationDto device) {
        if (smv.getModes().isEmpty() && device.getState() != null && !device.getState().isBlank()) {
            log.warn("Device '{}' (template '{}') has no modes; user-provided state '{}' is ignored",
                    device.getVarName(), device.getTemplateName(), device.getState());
        }
    }

    // ==================== P1: Trigger.Attribute 合法性 ====================

    private void validateTriggerAttributes(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        Set<String> legalAttrs = buildLegalAttributeSet(smv);

        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                String ctx = "Transition '" + trans.getName() + "'";
                validateAssignments(smv, ctx, trans.getAssignments());
                boolean hasAssignments = trans.getAssignments() != null && !trans.getAssignments().isEmpty();
                int assignmentCount = hasAssignments ? trans.getAssignments().size() : 0;
                boolean hasStartState = trans.getStartState() != null && !trans.getStartState().isBlank();
                boolean hasEndState = trans.getEndState() != null && !trans.getEndState().isBlank();
                int stateEffectCount = hasEndState ? countConcreteStateEffects(trans.getEndState()) : 0;
                if (smv.getModes().isEmpty() && (hasStartState || hasEndState)) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " declares a state endpoint, but the template has no Modes; "
                            + "stateless transitions may only use a Trigger and one variable Assignment");
                }
                if (hasEndState && stateEffectCount == 0) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " EndState changes no mode");
                }
                if (stateEffectCount + assignmentCount > 1) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " declares multiple state/variable effects that cannot be preserved as one atomic action; "
                            + "use separate single-effect transitions with explicit triggers");
                }
                if (trans.getTrigger() == null) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " has no Trigger, so its autonomous effect has no modeled cause");
                }
                if (!hasEndState && !hasAssignments) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " has a Trigger but changes neither state nor a variable");
                }
                validateTriggerCompleteness(smv.getVarName(), ctx, trans.getTrigger());
                String attr = trans.getTrigger().getAttribute();
                if (!legalAttrs.contains(attr)) {
                    throw SmvGenerationException.illegalTriggerAttribute(
                            smv.getVarName(), ctx, attr, legalAttrs);
                }
                validateTriggerRelation(smv.getVarName(), ctx, trans.getTrigger().getRelation());
                validateTriggerValue(smv, ctx, trans.getTrigger());
                if (hasEndState && hasNoPossibleApiStateChange(trans.getStartState(), trans.getEndState())) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " has identical concrete StartState and EndState effects and cannot change the model");
                }
            }
        }
        if (manifest.getApis() != null) {
            if (!manifest.getApis().isEmpty() && (smv.getModes() == null || smv.getModes().isEmpty())) {
                throw SmvGenerationException.templateInvalid(smv.getVarName(),
                        "APIs require at least one Mode because API commands are modeled as state changes");
            }
            for (DeviceManifest.API api : manifest.getApis()) {
                String ctx = "API '" + api.getName() + "'";
                if (api.getEndState() == null || api.getEndState().isBlank()) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " requires a non-empty EndState");
                }
                if (api.getEndState() != null
                        && !api.getEndState().isEmpty()
                        && api.getEndState().replace(";", "").isBlank()) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " EndState changes no mode; at least one concrete state effect is required");
                }
                if (api.getTrigger() != null) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), ctx
                            + " contains an unsupported Trigger; API commands use StartState/EndState, while "
                            + "conditional autonomous behavior belongs in Transitions");
                }
            }
        }
    }

    private void validateTriggerCompleteness(String deviceName, String context, DeviceManifest.Trigger trigger) {
        if (trigger.getAttribute() == null || trigger.getAttribute().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "attribute is null/blank");
        }
        if (trigger.getRelation() == null || trigger.getRelation().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "relation is null/blank");
        }
        if (trigger.getValue() == null || trigger.getValue().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "value is null/blank");
        }
    }

    private void validateTriggerRelation(String deviceName, String context, String rawRelation) {
        String normalized = normalizeTriggerRelation(rawRelation);
        if (!isSupportedTriggerRelation(normalized)) {
            throw SmvGenerationException.illegalTriggerRelation(
                    deviceName, context, rawRelation,
                    List.of("=", "!=", ">", ">=", "<", "<="));
        }
    }

    private String normalizeTriggerRelation(String relation) {
        return SmvRelationUtils.normalizeTriggerRelation(relation);
    }

    private boolean isSupportedTriggerRelation(String relation) {
        return SmvRelationUtils.isSupportedTriggerRelation(relation);
    }

    private void validateTriggerValue(DeviceSmvData smv,
                                      String context,
                                      DeviceManifest.Trigger trigger) {
        String attribute = trigger.getAttribute();
        String relation = normalizeTriggerRelation(trigger.getRelation());
        String normalizedValue = trigger.getValue().trim().replace(" ", "");
        List<String> modeValues = smv.getModeStates().get(attribute);
        if (modeValues != null) {
            validateEnumeratedTriggerValue(smv.getVarName(), context, attribute, relation,
                    normalizedValue, modeValues, "mode");
            return;
        }
        DeviceManifest.InternalVariable variable = findReadableTriggerDomain(smv, attribute);
        if (variable == null) {
            return;
        }
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            validateEnumeratedTriggerValue(smv.getVarName(), context, attribute, relation,
                    normalizedValue, variable.getValues(), "enum variable");
            return;
        }
        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            final int numericValue;
            try {
                numericValue = Integer.parseInt(trigger.getValue().trim());
            } catch (NumberFormatException exception) {
                throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                        + " compares numeric trigger '" + attribute + "' with non-integer value '"
                        + trigger.getValue() + "'");
            }
            if (numericValue < variable.getLowerBound() || numericValue > variable.getUpperBound()) {
                throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                        + " compares '" + attribute + "' with " + numericValue + ", outside range "
                        + variable.getLowerBound() + ".." + variable.getUpperBound());
            }
            return;
        }
        validateEnumeratedTriggerValue(smv.getVarName(), context, attribute, relation,
                normalizedValue.toUpperCase(Locale.ROOT), List.of("TRUE", "FALSE"), "boolean variable");
    }

    private void validateEnumeratedTriggerValue(String deviceName,
                                                String context,
                                                String attribute,
                                                String relation,
                                                String normalizedValue,
                                                List<String> values,
                                                String domainKind) {
        if (!"=".equals(relation) && !"!=".equals(relation)) {
            throw SmvGenerationException.templateInvalid(deviceName, context + " uses ordering relation '"
                    + relation + "' on " + domainKind + " '" + attribute + "'; use = or !=");
        }
        boolean allowed = values.stream()
                .filter(Objects::nonNull)
                .map(value -> value.replace(" ", ""))
                .anyMatch(normalizedValue::equals);
        if (!allowed) {
            throw SmvGenerationException.templateInvalid(deviceName, context + " compares '"
                    + attribute + "' with unknown value '" + normalizedValue + "'; allowed values are " + values);
        }
    }

    private DeviceManifest.InternalVariable findReadableTriggerDomain(DeviceSmvData smv, String attribute) {
        if (smv.getManifest().getInternalVariables() == null) {
            return null;
        }
        return smv.getManifest().getInternalVariables().stream()
                .filter(Objects::nonNull)
                .filter(variable -> attribute.equals(variable.getName()))
                .findFirst()
                .orElse(null);
    }

    private int countConcreteStateEffects(String endState) {
        int count = 0;
        for (String component : endState.split(";", -1)) {
            String normalized = DeviceSmvDataFactory.cleanStateName(component);
            if (normalized != null && !normalized.isEmpty() && !"_".equals(normalized)) {
                count++;
            }
        }
        return count;
    }

    private void validateAssignments(DeviceSmvData smv,
                                     String context,
                                     List<DeviceManifest.Assignment> assignments) {
        if (assignments == null) return;
        for (int i = 0; i < assignments.size(); i++) {
            DeviceManifest.Assignment a = assignments.get(i);
            if (a == null) {
                throw SmvGenerationException.incompleteTrigger(smv.getVarName(), context, "assignment[" + i + "] is null");
            }
            if (a.getAttribute() == null || a.getAttribute().isBlank()) {
                throw SmvGenerationException.incompleteTrigger(smv.getVarName(), context, "assignment[" + i + "].attribute is null/blank");
            }
            if (a.getValue() == null || a.getValue().isBlank()) {
                throw SmvGenerationException.incompleteTrigger(smv.getVarName(), context, "assignment[" + i + "].value is null/blank");
            }
            DeviceManifest.InternalVariable domain = findAssignmentDomain(smv, a.getAttribute());
            if (domain == null) {
                throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                        + " assigns unknown variable '" + a.getAttribute()
                        + "'; targets must be declared in InternalVariables or EnvironmentDomains");
            }
            validateAssignmentValue(smv.getVarName(), context, a, domain);
        }
    }

    private void validateApiEventSemantics(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        if (manifest == null || manifest.getApis() == null || manifest.getApis().isEmpty()) {
            return;
        }
        Map<String, String> signalRoutes = new LinkedHashMap<>();
        for (DeviceManifest.API api : manifest.getApis()) {
            String context = "API '" + api.getName() + "'";
            if (hasNoPossibleApiStateChange(api.getStartState(), api.getEndState())) {
                throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                        + " has identical concrete StartState and EndState effects and cannot change the model");
            }
            if (Boolean.TRUE.equals(api.getSignal())) {
                String route = canonicalApiState(api.getStartState(), true, smv.getModes().size())
                        + "->" + canonicalApiState(api.getEndState(), false, smv.getModes().size());
                String previous = signalRoutes.putIfAbsent(route, api.getName());
                if (previous != null) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(),
                            "signal APIs '" + previous + "' and '" + api.getName()
                                    + "' have indistinguishable state-transition pulses");
                }
            }
        }
    }

    private String canonicalApiState(String state, boolean startState, int modeCount) {
        String[] raw = state == null ? new String[0] : state.split(";", -1);
        List<String> parts = new ArrayList<>(modeCount);
        for (int i = 0; i < modeCount; i++) {
            String value = i < raw.length ? raw[i].trim().replace(" ", "").toLowerCase(Locale.ROOT) : "";
            parts.add(startState && "_".equals(value) ? "" : value);
        }
        return String.join(";", parts);
    }

    private boolean hasNoPossibleApiStateChange(String startState, String endState) {
        String[] starts = startState == null ? new String[0] : startState.split(";", -1);
        String[] ends = endState == null ? new String[0] : endState.split(";", -1);
        boolean hasEffect = false;
        for (int i = 0; i < ends.length; i++) {
            String end = DeviceSmvDataFactory.cleanStateName(ends[i]);
            if (end == null || end.isEmpty()) {
                continue;
            }
            hasEffect = true;
            String start = i < starts.length ? DeviceSmvDataFactory.cleanStartState(starts[i]) : "";
            if (start == null || start.isEmpty() || !start.equals(end)) {
                return false;
            }
        }
        return hasEffect;
    }

    private DeviceManifest.InternalVariable findAssignmentDomain(DeviceSmvData smv, String attribute) {
        if (smv.getManifest() != null && smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable variable : smv.getManifest().getInternalVariables()) {
                if (variable != null && attribute.equals(variable.getName())) {
                    return variable;
                }
            }
        }
        return smv.getImpactedEnvironmentVariables() != null
                ? smv.getImpactedEnvironmentVariables().get(attribute)
                : null;
    }

    private void validateAssignmentValue(String deviceName,
                                         String context,
                                         DeviceManifest.Assignment assignment,
                                         DeviceManifest.InternalVariable domain) {
        String value = assignment.getValue().trim();
        if (domain.getValues() != null && !domain.getValues().isEmpty()) {
            String normalized = value.replace(" ", "");
            boolean allowed = domain.getValues().stream()
                    .filter(Objects::nonNull)
                    .map(candidate -> candidate.replace(" ", ""))
                    .anyMatch(normalized::equals);
            if (!allowed) {
                throw SmvGenerationException.templateInvalid(deviceName, context + " assigns '"
                        + value + "' to '" + assignment.getAttribute() + "', outside enum domain "
                        + domain.getValues());
            }
            return;
        }
        if (domain.getLowerBound() != null && domain.getUpperBound() != null) {
            final int numeric;
            try {
                numeric = Integer.parseInt(value);
            } catch (NumberFormatException e) {
                throw SmvGenerationException.templateInvalid(deviceName, context + " assigns non-integer '"
                        + value + "' to numeric variable '" + assignment.getAttribute() + "'");
            }
            if (numeric < domain.getLowerBound() || numeric > domain.getUpperBound()) {
                throw SmvGenerationException.templateInvalid(deviceName, context + " assigns " + numeric
                        + " to '" + assignment.getAttribute() + "', outside range "
                        + domain.getLowerBound() + ".." + domain.getUpperBound());
            }
            return;
        }
        if (!"TRUE".equalsIgnoreCase(value) && !"FALSE".equalsIgnoreCase(value)) {
            throw SmvGenerationException.templateInvalid(deviceName, context + " assigns '" + value
                    + "' to boolean variable '" + assignment.getAttribute() + "'; use TRUE or FALSE");
        }
    }

    private Set<String> buildLegalAttributeSet(DeviceSmvData smv) {
        Set<String> attrs = new LinkedHashSet<>();
        attrs.addAll(smv.getModes());
        if (smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : smv.getManifest().getInternalVariables()) {
                if (iv.getName() != null) attrs.add(iv.getName());
            }
        }
        return attrs;
    }

    // ==================== P2: StartState/EndState 格式与语义 ====================

    private void validateStartEndStates(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        boolean multiMode = smv.getModes().size() > 1;
        int modeCount = smv.getModes().size();

        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                validateStateString(smv, api.getName(), "API", api.getStartState(), multiMode, modeCount, true);
                validateStateString(smv, api.getName(), "API", api.getEndState(), multiMode, modeCount, false);
            }
        }
        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                validateStateString(smv, trans.getName(), "Transition", trans.getStartState(), multiMode, modeCount, true);
                validateStateString(smv, trans.getName(), "Transition", trans.getEndState(), multiMode, modeCount, false);
            }
        }
    }

    private void validateStateString(DeviceSmvData smv, String itemName, String itemType,
                                     String stateStr, boolean multiMode, int modeCount, boolean isStartState) {
        if (stateStr == null || stateStr.isBlank()) return;

        // Special case: StartState="_" is a global wildcard for all modes
        if (isStartState && stateStr.trim().equals("_")) return;

        if (!multiMode) {
            if (stateStr.contains(";")) {
                throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                        "contains ';' but device is single-mode");
            }
            if (!smv.getModes().isEmpty()) {
                String mode = smv.getModes().get(0);
                String clean = isStartState ? DeviceSmvDataFactory.cleanStartState(stateStr)
                                            : DeviceSmvDataFactory.cleanStateName(stateStr);
                List<String> legal = smv.getModeStates().get(mode);
                if (legal != null && !legal.isEmpty() && !clean.isEmpty() && !legal.contains(clean)) {
                    throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, clean,
                            "not in legal values " + legal + " for mode '" + mode + "'");
                }
            }
        } else {
            String[] parts = stateStr.split(";", -1);
            if (parts.length != modeCount) {
                throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                        parts.length + " segments, expected " + modeCount + " (modes=" + smv.getModes() + ")");
            }
            for (int i = 0; i < parts.length; i++) {
                String rawSeg = parts[i].trim();
                if (rawSeg.isEmpty()) continue;
                // For StartState, "_" is treated as wildcard and skipped
                if (isStartState && rawSeg.equals("_")) continue;
                String seg = DeviceSmvDataFactory.cleanStateName(rawSeg);
                String mode = smv.getModes().get(i);
                List<String> legal = smv.getModeStates().get(mode);
                if (legal != null && !legal.isEmpty() && !legal.contains(seg)) {
                    throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                            "segment[" + i + "]='" + seg + "' not in legal values " + legal + " for mode '" + mode + "'");
                }
            }
        }
    }

    // ==================== P5: 同名 env var 冲突检测 ====================

    private void validateEnvVarConflicts(Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, List<EnvVarSource>> envSources = new LinkedHashMap<>();

        for (Map.Entry<String, DeviceSmvData> entry : deviceSmvMap.entrySet()) {
            DeviceSmvData smv = entry.getValue();
            if (smv.getManifest() == null) continue;
            if (!entry.getKey().equals(smv.getVarName())) continue;

            for (Map.Entry<String, DeviceManifest.InternalVariable> ev : smv.getEnvVariables().entrySet()) {
                envSources.computeIfAbsent(ev.getKey().toLowerCase(Locale.ROOT), k -> new ArrayList<>())
                        .add(new EnvVarSource(ev.getKey(), smv.getVarName(), "read", ev.getValue()));
            }
            for (Map.Entry<String, DeviceManifest.InternalVariable> ev : smv.getImpactedEnvironmentVariables().entrySet()) {
                envSources.computeIfAbsent(ev.getKey().toLowerCase(Locale.ROOT), k -> new ArrayList<>())
                        .add(new EnvVarSource(ev.getKey(), smv.getVarName(), "impact", ev.getValue()));
            }
        }

        for (Map.Entry<String, List<EnvVarSource>> entry : envSources.entrySet()) {
            List<EnvVarSource> sources = entry.getValue();
            if (sources.size() <= 1) continue;
            EnvVarSource first = sources.get(0);
            for (int i = 1; i < sources.size(); i++) {
                checkEnvVarCompatibility(entry.getKey(), first, sources.get(i));
            }
        }
    }

    private void checkEnvVarCompatibility(String varName, EnvVarSource a, EnvVarSource b) {
        if (!a.name.equals(b.name)) {
            throw SmvGenerationException.envVarConflict(varName,
                    "name/case mismatch: device '" + a.device + "' declares '" + a.name
                            + "', device '" + b.device + "' declares '" + b.name + "'");
        }
        String mismatch = EnvironmentDomainUtils.incompatibility(a.var, b.var);
        if (mismatch != null) {
            throw SmvGenerationException.envVarConflict(varName,
                    mismatch + ": device '" + a.device + "' (" + a.role + ") versus device '"
                            + b.device + "' (" + b.role + ")");
        }
    }

    private void validateImpactedEnvironmentDefinitions(DeviceSmvData smv) {
        if (smv.getImpactedVariables() == null || smv.getImpactedVariables().isEmpty()) {
            return;
        }
        Set<String> localVariables = new HashSet<>();
        if (smv.getManifest() != null && smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable variable : smv.getManifest().getInternalVariables()) {
                if (variable != null && variable.getName() != null && Boolean.TRUE.equals(variable.getIsInside())) {
                    localVariables.add(variable.getName());
                }
            }
        }
        for (String impacted : smv.getImpactedVariables()) {
            if (impacted == null || impacted.isBlank()) {
                continue;
            }
            if (localVariables.contains(impacted)) {
                throw SmvGenerationException.smvGenerationError(
                        "Template '" + smv.getTemplateName() + "' uses ImpactedVariable '" + impacted
                                + "' with the same name as a local InternalVariable. Use WorkingStates.Dynamics "
                                + "for local device state, and reserve ImpactedVariables for shared environment variables.");
            }
            if (smv.getImpactedEnvironmentVariables() == null
                    || !smv.getImpactedEnvironmentVariables().containsKey(impacted)) {
                throw SmvGenerationException.smvGenerationError(
                        "Template '" + smv.getTemplateName() + "' impacts environment variable '" + impacted
                                + "', but its own manifest does not define that domain. Add EnvironmentDomains[].Name='"
                                + impacted + "', or declare a readable InternalVariable with the same name and IsInside=false.");
            }
        }
    }

    private void validateVariableDomainsAndDynamics(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        Map<String, DeviceManifest.InternalVariable> writableDomains = new LinkedHashMap<>();
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                if (variable == null || variable.getName() == null) {
                    continue;
                }
                validateVariableDomain(smv.getVarName(), "InternalVariable '" + variable.getName() + "'", variable);
                if (Boolean.TRUE.equals(variable.getIsInside())) {
                    writableDomains.putIfAbsent(variable.getName(), variable);
                }
            }
        }
        if (manifest.getEnvironmentDomains() != null) {
            for (DeviceManifest.EnvironmentDomain domain : manifest.getEnvironmentDomains()) {
                if (domain == null || domain.getName() == null) {
                    continue;
                }
                validateVariableDomain(smv.getVarName(), "EnvironmentDomain '" + domain.getName() + "'",
                        EnvironmentDomainUtils.asInternalVariable(domain));
            }
        }
        if (manifest.getImpactedVariables() != null) {
            for (String impacted : manifest.getImpactedVariables()) {
                DeviceManifest.InternalVariable domain = EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted);
                if (domain != null) {
                    writableDomains.putIfAbsent(impacted, domain);
                }
            }
        }
        if (manifest.getWorkingStates() == null) {
            return;
        }
        for (DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || state.getDynamics() == null) {
                continue;
            }
            Set<String> seen = new LinkedHashSet<>();
            for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                String context = "WorkingState '" + state.getName() + "' Dynamics";
                if (dynamic == null || dynamic.getVariableName() == null || dynamic.getVariableName().isBlank()) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                            + " requires VariableName");
                }
                if (!seen.add(dynamic.getVariableName())) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                            + " defines variable '" + dynamic.getVariableName() + "' more than once");
                }
                DeviceManifest.InternalVariable domain = writableDomains.get(dynamic.getVariableName());
                if (domain == null) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                            + " targets unknown or non-writable variable '" + dynamic.getVariableName() + "'");
                }
                boolean numeric = domain.getLowerBound() != null && domain.getUpperBound() != null;
                if (numeric && (dynamic.getChangeRate() == null || dynamic.getValue() != null)) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                            + " must use ChangeRate (not Value) for numeric variable '"
                            + dynamic.getVariableName() + "'");
                }
                if (!numeric && (dynamic.getValue() == null || dynamic.getChangeRate() != null)) {
                    throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                            + " must use Value (not ChangeRate) for enum/boolean variable '"
                            + dynamic.getVariableName() + "'");
                }
                if (numeric) {
                    try {
                        Integer.parseInt(dynamic.getChangeRate().trim());
                    } catch (NumberFormatException exception) {
                        throw SmvGenerationException.templateInvalid(smv.getVarName(), context
                                + " has non-integer ChangeRate '" + dynamic.getChangeRate() + "'");
                    }
                } else {
                    validateDynamicValue(smv.getVarName(), context, dynamic, domain);
                }
            }
        }
    }

    private void validateVariableDomain(String deviceName,
                                        String context,
                                        DeviceManifest.InternalVariable variable) {
        if (variable.getLowerBound() != null && variable.getUpperBound() != null
                && variable.getLowerBound() > variable.getUpperBound()) {
            throw SmvGenerationException.templateInvalid(deviceName, context + " has LowerBound "
                    + variable.getLowerBound() + " greater than UpperBound " + variable.getUpperBound());
        }
        if (variable.getValues() != null) {
            Set<String> normalized = new LinkedHashSet<>();
            for (String raw : variable.getValues()) {
                String value = raw == null ? "" : raw.replace(" ", "");
                if (value.isEmpty() || !normalized.add(value)) {
                    throw SmvGenerationException.templateInvalid(deviceName, context
                            + " has empty or duplicate enum values after model normalization");
                }
            }
        }
        String naturalRate = variable.getNaturalChangeRate();
        boolean numeric = variable.getLowerBound() != null && variable.getUpperBound() != null;
        if (naturalRate != null && !naturalRate.isBlank() && !numeric) {
            throw SmvGenerationException.templateInvalid(deviceName, context
                    + " declares NaturalChangeRate, but only numeric ranges can change by a rate");
        }
        if (naturalRate != null && !naturalRate.isBlank()) {
            String[] parts = naturalRate.replace("[", "").replace("]", "").split(",", -1);
            try {
                int lowerRate;
                int upperRate;
                if (parts.length == 1) {
                    int rate = Integer.parseInt(parts[0].trim());
                    lowerRate = Math.min(0, rate);
                    upperRate = Math.max(0, rate);
                } else if (parts.length == 2) {
                    lowerRate = Integer.parseInt(parts[0].trim());
                    upperRate = Integer.parseInt(parts[1].trim());
                } else {
                    throw new NumberFormatException("wrong number of rate values");
                }
                if (lowerRate > upperRate) {
                    throw SmvGenerationException.templateInvalid(deviceName, context
                            + " has invalid or descending NaturalChangeRate '" + naturalRate + "'");
                }
            } catch (NumberFormatException exception) {
                throw SmvGenerationException.templateInvalid(deviceName, context
                        + " has invalid NaturalChangeRate '" + naturalRate + "'");
            }
        }
    }

    private void validateDynamicValue(String deviceName,
                                      String context,
                                      DeviceManifest.Dynamic dynamic,
                                      DeviceManifest.InternalVariable domain) {
        DeviceManifest.Assignment assignment = DeviceManifest.Assignment.builder()
                .attribute(dynamic.getVariableName())
                .value(dynamic.getValue())
                .build();
        validateAssignmentValue(deviceName, context, assignment, domain);
    }

    private static class EnvVarSource {
        final String name;
        final String device;
        final String role;
        final DeviceManifest.InternalVariable var;
        EnvVarSource(String name, String device, String role, DeviceManifest.InternalVariable var) {
            this.name = name;
            this.device = device;
            this.role = role;
            this.var = var;
        }
    }

    // ==================== P4: trust/privacy 值合法性 ====================

    private static final Set<String> VALID_TRUST_VALUES = Set.of("trusted", "untrusted");
    private static final Set<String> VALID_PRIVACY_VALUES = Set.of("public", "private");

    private static String normalize(String value) {
        return DeviceSmvDataFactory.normalizeTrustPrivacy(value);
    }

    private void validatePropertyValues(DeviceSmvData smv) {
        // modeStateTrust values
        for (Map.Entry<String, String> entry : smv.getModeStateTrust().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_TRUST_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': trust value '" + val + "' for key '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_TRUST_VALUES);
            }
        }
        // instanceStateTrust
        if (smv.getInstanceStateTrust() != null
                && !VALID_TRUST_VALUES.contains(normalize(smv.getInstanceStateTrust()))) {
            throw SmvGenerationException.smvGenerationError(
                    "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                            + "': instanceStateTrust '" + smv.getInstanceStateTrust()
                            + "' is invalid. Expected: " + VALID_TRUST_VALUES);
        }
        // instanceVariableTrust values
        for (Map.Entry<String, String> entry : smv.getInstanceVariableTrust().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_TRUST_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': variable trust '" + val + "' for '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_TRUST_VALUES);
            }
        }
        // instanceVariablePrivacy values
        for (Map.Entry<String, String> entry : smv.getInstanceVariablePrivacy().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_PRIVACY_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': privacy value '" + val + "' for '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
            }
        }
        // content privacy values
        for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
            if (ci.getPrivacy() == null || !VALID_PRIVACY_VALUES.contains(normalize(ci.getPrivacy()))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': content privacy '" + ci.getPrivacy() + "' for content '" + ci.getName()
                                + "' is required and must be one of " + VALID_PRIVACY_VALUES);
            }
        }
        // manifest variable trust values
        if (smv.getManifest() != null && smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                if (var.getTrust() != null && !VALID_TRUST_VALUES.contains(normalize(var.getTrust()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': manifest variable trust '" + var.getTrust() + "' for '" + var.getName()
                                    + "' is invalid. Expected: " + VALID_TRUST_VALUES);
                }
                if (var.getPrivacy() != null && !VALID_PRIVACY_VALUES.contains(normalize(var.getPrivacy()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': manifest variable privacy '" + var.getPrivacy() + "' for '" + var.getName()
                                    + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
                }
            }
        }
        // manifest workingState privacy values
        if (smv.getManifest() != null && smv.getManifest().getWorkingStates() != null) {
            for (DeviceManifest.WorkingState ws : smv.getManifest().getWorkingStates()) {
                if (ws.getPrivacy() != null && !VALID_PRIVACY_VALUES.contains(normalize(ws.getPrivacy()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': workingState privacy '" + ws.getPrivacy() + "' for state '" + ws.getName()
                                    + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
                }
            }
        }
    }

    // ==================== P3: trust/privacy 一致性校验 ====================

    private void validateTrustPrivacyConsistency(DeviceSmvData smv) {
        if (smv.isSensor()) return;
        DeviceManifest manifest = smv.getManifest();
        if (manifest.getWorkingStates() == null) return;

        Map<String, String> seenTrust = new HashMap<>();
        Map<String, String> seenPrivacy = new HashMap<>();

        for (DeviceManifest.WorkingState ws : manifest.getWorkingStates()) {
            if (ws.getName() == null) continue;
            if (smv.getModes().size() <= 1) {
                String key = (smv.getModes().isEmpty() ? "" : smv.getModes().get(0) + "_")
                        + DeviceSmvDataFactory.cleanStateName(ws.getName());
                checkConflict(seenTrust, key, ws.getTrust(), smv.getVarName(), "trust");
                checkConflict(seenPrivacy, key, ws.getPrivacy(), smv.getVarName(), "privacy");
            } else {
                String[] parts = ws.getName().split(";");
                for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                    String key = smv.getModes().get(i) + "_" + DeviceSmvDataFactory.cleanStateName(parts[i].trim());
                    checkConflict(seenTrust, key, ws.getTrust(), smv.getVarName(), "trust");
                    checkConflict(seenPrivacy, key, ws.getPrivacy(), smv.getVarName(), "privacy");
                }
            }
        }
    }

    private void checkConflict(Map<String, String> seen, String key, String value,
                               String varName, String dimension) {
        if (value == null) return;
        String normalized = normalize(value);
        String prev = seen.put(key, normalized);
        if (prev != null && !prev.equals(normalized)) {
            throw SmvGenerationException.trustPrivacyConflict(varName, key, prev, normalized);
        }
    }
}
