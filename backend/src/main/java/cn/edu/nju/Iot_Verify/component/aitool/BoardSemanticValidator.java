package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/**
 * Template-aware validation shared by AI mutation tools.
 *
 * <p>The UI, AI tools, and NuSMV generator must agree that device nodes are
 * instances and templates define the legal states, modes, variables, APIs, and
 * content keys. These checks stop AI-created board data from being accepted only
 * to fail later during simulation or verification.</p>
 */
public final class BoardSemanticValidator {

    private static final Set<String> ENUM_RELATIONS = Set.of("=", "!=", "in", "not in");

    private BoardSemanticValidator() {
    }

    public static BoardContext context(List<DeviceNodeDto> nodes, List<DeviceTemplateDto> templates) {
        Map<String, DeviceNodeDto> nodesById = new LinkedHashMap<>();
        if (nodes != null) {
            for (DeviceNodeDto node : nodes) {
                if (node != null && hasText(node.getId())) {
                    nodesById.put(node.getId().trim(), node);
                }
            }
        }

        Map<String, DeviceTemplateDto> templatesByName = new HashMap<>();
        if (templates != null) {
            for (DeviceTemplateDto template : templates) {
                if (template == null) {
                    continue;
                }
                putTemplateAlias(templatesByName, template.getName(), template);
                if (template.getManifest() != null) {
                    putTemplateAlias(templatesByName, template.getManifest().getName(), template);
                }
            }
        }
        return new BoardContext(nodesById, templatesByName, !templatesByName.isEmpty());
    }

    public static String validateRuleCondition(BoardContext context, RuleDto.Condition condition, int index) {
        DeviceTemplateDto template = templateForDevice(context, condition.getDeviceName());
        if (template == null || template.getManifest() == null) {
            return null;
        }

        String targetType = normalize(condition.getTargetType());
        String attribute = trimToNull(condition.getAttribute());
        String relation = SmvRelationUtils.normalizeRelation(condition.getRelation());
        String value = trimToNull(condition.getValue());
        String prefix = "Condition " + (index + 1);

        if ("api".equals(targetType)) {
            return hasSignalApi(template.getManifest(), attribute)
                    ? null
                    : prefix + " references unknown or non-signal API '" + attribute + "'.";
        }
        if ("variable".equals(targetType)) {
            DeviceTemplateDto.DeviceManifest.InternalVariable variable = findVariable(template.getManifest(), attribute);
            if (variable == null) {
                return prefix + " references unknown template variable '" + attribute + "'.";
            }
            return validateVariableValue(prefix, variable, relation, value);
        }
        if ("mode".equals(targetType)) {
            String mode = resolveModeName(template.getManifest(), attribute);
            if (mode == null) {
                return prefix + " references unknown mode '" + attribute + "'.";
            }
            return validateModeValue(prefix, template.getManifest(), mode, relation, value);
        }
        if ("state".equals(targetType)) {
            if (!"state".equalsIgnoreCase(attribute)) {
                return prefix + " state conditions must use attribute 'state'.";
            }
            return validateStateValue(prefix, template.getManifest(), relation, value);
        }
        return null;
    }

    public static String validateRuleCommand(BoardContext context, RuleDto.Command command) {
        DeviceTemplateDto targetTemplate = templateForDevice(context, command.getDeviceName());
        DeviceTemplateDto.DeviceManifest.API actionApi = targetTemplate != null
                ? findApi(targetTemplate.getManifest(), command.getAction()) : null;
        if (targetTemplate != null && targetTemplate.getManifest() != null && actionApi == null) {
            return "Command references unknown API '" + command.getAction() + "'.";
        }

        if (hasText(command.getContent()) && !hasText(command.getContentDevice())) {
            return "contentDevice is required when command content is provided.";
        }
        if (hasText(command.getContentDevice()) && hasText(command.getContent())) {
            if (actionApi != null && !Boolean.TRUE.equals(actionApi.getAcceptsContent())) {
                return "Action '" + actionApi.getName()
                        + "' does not accept a content-sensitivity input.";
            }
            DeviceTemplateDto contentTemplate = templateForDevice(context, command.getContentDevice());
            if (contentTemplate != null && contentTemplate.getManifest() != null
                    && !hasContent(contentTemplate.getManifest(), command.getContent())) {
                return "Command references unknown content '" + command.getContent() + "'.";
            }
        }
        return null;
    }

    public static String validateSpecCondition(BoardContext context, SpecConditionDto condition, String side, int index) {
        DeviceTemplateDto template = templateForDevice(context, condition.getDeviceId());
        if (template == null || template.getManifest() == null) {
            return null;
        }

        String targetType = normalize(condition.getTargetType());
        String key = trimToNull(condition.getKey());
        String relation = SmvRelationUtils.normalizeRelation(condition.getRelation());
        String value = trimToNull(condition.getValue());
        String displaySide = side == null ? "UNKNOWN" : side.trim().toUpperCase(Locale.ROOT);
        String prefix = "Condition " + (index + 1) + " on '" + displaySide + "'";

        if ("api".equals(targetType)) {
            if (!hasSignalApi(template.getManifest(), key)) {
                return prefix + " references unknown or non-signal API '" + key + "'.";
            }
            return validateLiteralValue(prefix, relation, value, Set.of("TRUE", "FALSE"), "TRUE or FALSE");
        }
        if ("state".equals(targetType)) {
            if (!"state".equalsIgnoreCase(key)) {
                return prefix + " state conditions must use key 'state'.";
            }
            return validateStateValue(prefix, template.getManifest(), relation, value);
        }
        if ("mode".equals(targetType)) {
            String mode = resolveModeName(template.getManifest(), key);
            if (mode == null) {
                return prefix + " references unknown mode '" + key + "'.";
            }
            return validateModeValue(prefix, template.getManifest(), mode, relation, value);
        }
        if ("variable".equals(targetType)) {
            DeviceTemplateDto.DeviceManifest.InternalVariable variable = findVariableOrEnvKey(template.getManifest(), key);
            if (variable == null) {
                return prefix + " references unknown template variable '" + key + "'.";
            }
            return validateVariableValue(prefix, variable, relation, value);
        }
        if ("trust".equals(targetType)) {
            String propertyError = validatePropertyReference(prefix, condition, template.getManifest());
            if (propertyError != null) return propertyError;
            return validateLiteralValue(prefix, relation, value, Set.of("trusted", "untrusted"), "trusted or untrusted");
        }
        if ("privacy".equals(targetType)) {
            String propertyError = validatePropertyReference(prefix, condition, template.getManifest());
            if (propertyError != null) return propertyError;
            return validateLiteralValue(prefix, relation, value, Set.of("public", "private"), "public or private");
        }
        return null;
    }

    public record BoardContext(Map<String, DeviceNodeDto> nodesById,
                               Map<String, DeviceTemplateDto> templatesByName,
                               boolean hasTemplateData) {
    }

    private static DeviceTemplateDto templateForDevice(BoardContext context, String deviceId) {
        if (context == null || !context.hasTemplateData() || !hasText(deviceId)) {
            return null;
        }
        DeviceNodeDto node = context.nodesById().get(deviceId.trim());
        if (node == null || !hasText(node.getTemplateName())) {
            return null;
        }
        return context.templatesByName().get(normalizeKey(node.getTemplateName()));
    }

    private static void putTemplateAlias(Map<String, DeviceTemplateDto> templatesByName,
                                         String rawName,
                                         DeviceTemplateDto template) {
        String key = normalizeKey(rawName);
        if (key != null) {
            templatesByName.putIfAbsent(key, template);
        }
    }

    private static String validateVariableValue(String prefix,
                                                DeviceTemplateDto.DeviceManifest.InternalVariable variable,
                                                String relation,
                                                String value) {
        if (relation == null || value == null) {
            return null;
        }
        List<String> candidates = splitValues(value, relation);
        if (candidates.isEmpty()) {
            return prefix + " has an empty value list for variable '" + variable.getName() + "'.";
        }
        if (("=".equals(relation) || "!=".equals(relation)) && candidates.size() != 1) {
            return prefix + " relation '" + relation + "' requires exactly one value.";
        }

        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            if (!ENUM_RELATIONS.contains(relation)) {
                return prefix + " enum variable '" + variable.getName() + "' supports only =, !=, in, not in.";
            }
            Set<String> allowed = new HashSet<>();
            for (String allowedValue : variable.getValues()) {
                if (hasText(allowedValue)) {
                    allowed.add(cleanEnumLiteral(allowedValue));
                }
            }
            for (String candidate : candidates) {
                if (!allowed.contains(cleanEnumLiteral(candidate))) {
                    return prefix + " illegal enum value '" + candidate + "' for variable '" + variable.getName() + "'.";
                }
            }
            return null;
        }

        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            for (String candidate : candidates) {
                try {
                    int parsed = Integer.parseInt(candidate.trim());
                    if (parsed < variable.getLowerBound() || parsed > variable.getUpperBound()) {
                        return prefix + " variable '" + variable.getName() + "' value '" + candidate
                                + "' is outside " + variable.getLowerBound() + ".." + variable.getUpperBound() + ".";
                    }
                } catch (NumberFormatException e) {
                    return prefix + " variable '" + variable.getName() + "' requires an integer value.";
                }
            }
        }
        return null;
    }

    private static String validateModeValue(String prefix,
                                            DeviceTemplateDto.DeviceManifest manifest,
                                            String mode,
                                            String relation,
                                            String value) {
        if (!ENUM_RELATIONS.contains(relation)) {
            return prefix + " mode conditions support only =, !=, in, not in.";
        }
        List<String> legalValues = modeValues(manifest).get(mode);
        if (legalValues == null || legalValues.isEmpty()) {
            return prefix + " mode '" + mode + "' has no legal values.";
        }
        List<String> candidates = splitValues(value, relation);
        for (String candidate : candidates) {
            String cleaned = DeviceSmvDataFactory.cleanStateName(candidate);
            if (!hasText(cleaned) || !legalValues.contains(cleaned)) {
                return prefix + " illegal value '" + candidate + "' for mode '" + mode + "'.";
            }
        }
        return null;
    }

    private static String validateStateValue(String prefix,
                                             DeviceTemplateDto.DeviceManifest manifest,
                                             String relation,
                                             String value) {
        if (!ENUM_RELATIONS.contains(relation)) {
            return prefix + " state conditions support only =, !=, in, not in.";
        }
        List<String> modes = modeNames(manifest);
        if (modes.isEmpty()) {
            return prefix + " references state on a template with no modes.";
        }
        List<String> candidates = ("in".equals(relation) || "not in".equals(relation))
                ? SmvRelationUtils.splitStateRuleValues(value, modes.size())
                : List.of(value == null ? "" : value.trim());
        if (candidates.isEmpty()) {
            return prefix + " has an empty state value.";
        }
        if (("=".equals(relation) || "!=".equals(relation)) && candidates.size() != 1) {
            return prefix + " relation '" + relation + "' requires exactly one state value.";
        }
        for (String candidate : candidates) {
            if (!isLegalState(manifest, candidate)) {
                return prefix + " illegal state value '" + candidate + "'.";
            }
        }
        return null;
    }

    private static String validateLiteralValue(String prefix,
                                               String relation,
                                               String value,
                                               Set<String> allowed,
                                               String label) {
        if (!ENUM_RELATIONS.contains(relation)) {
            return prefix + " supports only =, !=, in, not in.";
        }
        List<String> candidates = splitValues(value, relation);
        if (candidates.isEmpty()) {
            return prefix + " value must be " + label + ".";
        }
        for (String candidate : candidates) {
            boolean found = allowed.stream().anyMatch(item -> item.equalsIgnoreCase(candidate.trim()));
            if (!found) {
                return prefix + " value must be " + label + ": " + candidate + ".";
            }
        }
        return null;
    }

    private static boolean hasApi(DeviceTemplateDto.DeviceManifest manifest, String apiName) {
        return findApi(manifest, apiName) != null;
    }

    private static DeviceTemplateDto.DeviceManifest.API findApi(
            DeviceTemplateDto.DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || !hasText(apiName)) {
            return null;
        }
        String target = apiName.trim();
        for (DeviceTemplateDto.DeviceManifest.API api : manifest.getApis()) {
            if (api != null && target.equals(api.getName())) {
                return api;
            }
        }
        return null;
    }

    private static boolean hasSignalApi(DeviceTemplateDto.DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || !hasText(apiName)) {
            return false;
        }
        String target = apiName.trim();
        for (DeviceTemplateDto.DeviceManifest.API api : manifest.getApis()) {
            if (api != null && target.equals(api.getName()) && Boolean.TRUE.equals(api.getSignal())) {
                return true;
            }
        }
        return false;
    }

    private static boolean hasContent(DeviceTemplateDto.DeviceManifest manifest, String contentName) {
        if (manifest == null || manifest.getContents() == null || !hasText(contentName)) {
            return false;
        }
        String target = contentName.trim();
        for (DeviceTemplateDto.DeviceManifest.Content content : manifest.getContents()) {
            if (content != null && target.equals(content.getName())) {
                return true;
            }
        }
        return false;
    }

    private static DeviceTemplateDto.DeviceManifest.InternalVariable findVariable(
            DeviceTemplateDto.DeviceManifest manifest,
            String name) {
        if (manifest == null || manifest.getInternalVariables() == null || !hasText(name)) {
            return null;
        }
        String target = name.trim();
        for (DeviceTemplateDto.DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
            if (variable != null && target.equals(variable.getName())) {
                return variable;
            }
        }
        return null;
    }

    private static DeviceTemplateDto.DeviceManifest.InternalVariable findVariableOrEnvKey(
            DeviceTemplateDto.DeviceManifest manifest,
            String key) {
        if (!hasText(key)) {
            return null;
        }
        String target = key.trim();
        return findVariable(manifest, target);
    }

    private static String validatePropertyReference(String prefix,
                                                    SpecConditionDto condition,
                                                    DeviceTemplateDto.DeviceManifest manifest) {
        String scope = normalize(condition.getPropertyScope());
        String key = trimToNull(condition.getKey());
        if (!"state".equals(scope) && !"variable".equals(scope)) {
            return prefix + " requires propertyScope='state' or 'variable' for trust/privacy.";
        }
        if ("variable".equals(scope)) {
            return findVariable(manifest, key) == null
                    ? prefix + " references unknown property variable '" + key + "'."
                    : null;
        }
        return resolveModeName(manifest, key) == null
                ? prefix + " references unknown state-label mode '" + key + "'."
                : null;
    }

    private static String resolveModeName(DeviceTemplateDto.DeviceManifest manifest, String rawMode) {
        if (!hasText(rawMode)) {
            return null;
        }
        String trimmed = rawMode.trim();
        String cleaned = DeviceSmvDataFactory.cleanStateName(trimmed);
        for (String mode : modeNames(manifest)) {
            if (mode.equals(trimmed) || mode.equalsIgnoreCase(trimmed) || mode.equals(cleaned)) {
                return mode;
            }
        }
        return null;
    }

    private static boolean isLegalState(DeviceTemplateDto.DeviceManifest manifest, String rawCandidate) {
        if (!hasText(rawCandidate)) {
            return false;
        }
        List<String> modes = modeNames(manifest);
        Map<String, List<String>> statesByMode = modeValues(manifest);
        if (modes.isEmpty() || statesByMode.isEmpty()) {
            return false;
        }

        String candidate = rawCandidate.trim();
        if (candidate.contains(";")) {
            String[] segments = candidate.split(";", -1);
            if (segments.length != modes.size()) {
                return false;
            }
            boolean hasConcreteSegment = false;
            for (int i = 0; i < modes.size(); i++) {
                String cleaned = DeviceSmvDataFactory.cleanStateName(segments[i]);
                if (!hasText(cleaned) || "_".equals(cleaned)) {
                    continue;
                }
                List<String> legalStates = statesByMode.get(modes.get(i));
                if (legalStates == null || !legalStates.contains(cleaned)) {
                    return false;
                }
                hasConcreteSegment = true;
            }
            return hasConcreteSegment;
        }

        String cleaned = DeviceSmvDataFactory.cleanStateName(candidate);
        int matches = 0;
        for (String mode : modes) {
            List<String> states = statesByMode.get(mode);
            if (states != null && states.contains(cleaned)) {
                matches++;
            }
        }
        return matches == 1;
    }

    private static List<String> modeNames(DeviceTemplateDto.DeviceManifest manifest) {
        List<String> modes = new ArrayList<>();
        if (manifest == null || manifest.getModes() == null) {
            return modes;
        }
        for (String mode : manifest.getModes()) {
            if (hasText(mode)) {
                modes.add(mode.trim());
            }
        }
        return modes;
    }

    private static Map<String, List<String>> modeValues(DeviceTemplateDto.DeviceManifest manifest) {
        List<String> modes = modeNames(manifest);
        Map<String, List<String>> result = new LinkedHashMap<>();
        for (String mode : modes) {
            result.put(mode, new ArrayList<>());
        }
        if (manifest == null || manifest.getWorkingStates() == null || modes.isEmpty()) {
            return result;
        }

        for (DeviceTemplateDto.DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || !hasText(state.getName())) {
                continue;
            }
            if (modes.size() == 1) {
                addModeValue(result, modes.get(0), state.getName());
                continue;
            }
            String[] parts = state.getName().split(";", -1);
            if (parts.length == modes.size()) {
                for (int i = 0; i < modes.size(); i++) {
                    addModeValue(result, modes.get(i), parts[i]);
                }
            }
        }
        return result;
    }

    private static void addModeValue(Map<String, List<String>> valuesByMode,
                                     String mode,
                                     String rawValue) {
        if (!hasText(rawValue)) {
            return;
        }
        String clean = DeviceSmvDataFactory.cleanStateName(rawValue);
        if (!hasText(clean) || "_".equals(clean)) {
            return;
        }
        List<String> values = valuesByMode.get(mode);
        if (values != null && !values.contains(clean)) {
            values.add(clean);
        }
    }

    private static List<String> splitValues(String value, String relation) {
        if ("in".equals(relation) || "not in".equals(relation)) {
            return SmvRelationUtils.splitRuleValues(value);
        }
        return value == null ? List.of() : List.of(value.trim());
    }

    private static String cleanEnumLiteral(String value) {
        return value == null ? "" : value.trim().replace(" ", "");
    }

    private static String normalizeKey(String value) {
        if (!hasText(value)) {
            return null;
        }
        return value.trim().toLowerCase(Locale.ROOT);
    }

    private static String normalize(String value) {
        return hasText(value) ? value.trim().toLowerCase(Locale.ROOT) : "";
    }

    private static String trimToNull(String value) {
        if (!hasText(value)) {
            return null;
        }
        return value.trim();
    }

    private static boolean hasText(String value) {
        return value != null && !value.isBlank();
    }
}
