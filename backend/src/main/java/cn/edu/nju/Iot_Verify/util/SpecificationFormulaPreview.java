package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/** Formats a descriptive formula in user concepts; it never emits executable NuSMV. */
public final class SpecificationFormulaPreview {

    private SpecificationFormulaPreview() {
    }

    public static Context context(List<DeviceNodeDto> nodes, List<DeviceTemplateDto> templates) {
        Map<String, String> labelsById = new LinkedHashMap<>();
        for (DeviceNodeDto node : nodes == null ? List.<DeviceNodeDto>of() : nodes) {
            String id = node == null ? null : text(node.getId());
            if (id == null) {
                continue;
            }
            String label = text(node.getLabel());
            labelsById.put(id, label != null ? label : "Unknown device");
        }

        Map<String, DeviceTemplateDto> templatesByName = new LinkedHashMap<>();
        for (DeviceTemplateDto template : templates == null ? List.<DeviceTemplateDto>of() : templates) {
            String name = template == null ? null : text(template.getName());
            if (name != null) {
                templatesByName.putIfAbsent(name.toLowerCase(Locale.ROOT), template);
            }
        }

        Map<String, Set<String>> sharedVariablesByDeviceId = new LinkedHashMap<>();
        for (DeviceNodeDto node : nodes == null ? List.<DeviceNodeDto>of() : nodes) {
            String deviceId = node == null ? null : text(node.getId());
            String templateName = node == null ? null : text(node.getTemplateName());
            if (deviceId == null || templateName == null) {
                continue;
            }
            DeviceTemplateDto template = templatesByName.get(templateName.toLowerCase(Locale.ROOT));
            DeviceTemplateDto.DeviceManifest manifest = template == null ? null : template.getManifest();
            if (manifest == null || manifest.getInternalVariables() == null) {
                continue;
            }
            Set<String> sharedNames = new HashSet<>();
            for (DeviceTemplateDto.DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                String variableName = variable == null ? null : text(variable.getName());
                if (variableName != null && !Boolean.TRUE.equals(variable.getIsInside())) {
                    sharedNames.add(variableName.toLowerCase(Locale.ROOT));
                }
            }
            if (!sharedNames.isEmpty()) {
                sharedVariablesByDeviceId.put(deviceId, sharedNames);
            }
        }
        return new Context(labelsById, sharedVariablesByDeviceId);
    }

    public static Context labelsOnly(Map<String, String> labelsById) {
        return new Context(labelsById == null ? Map.of() : labelsById, Map.of());
    }

    /** Builds a display context from the immutable model-boundary device/template snapshot. */
    public static Context modelContext(
            List<DeviceVerificationDto> devices,
            Map<String, DeviceTemplateDto.DeviceManifest> templateManifests) {
        Map<String, String> labelsById = new LinkedHashMap<>();
        Map<String, DeviceTemplateDto.DeviceManifest> manifestsByName = new LinkedHashMap<>();
        for (Map.Entry<String, DeviceTemplateDto.DeviceManifest> entry :
                templateManifests == null
                        ? Map.<String, DeviceTemplateDto.DeviceManifest>of().entrySet()
                        : templateManifests.entrySet()) {
            String name = text(entry.getKey());
            if (name != null && entry.getValue() != null) {
                manifestsByName.putIfAbsent(name.toLowerCase(Locale.ROOT), entry.getValue());
            }
        }

        Map<String, Set<String>> sharedVariablesByDeviceId = new LinkedHashMap<>();
        for (DeviceVerificationDto device : devices == null
                ? List.<DeviceVerificationDto>of() : devices) {
            String id = device == null ? null : text(device.getVarName());
            if (id == null) {
                continue;
            }
            String label = text(device.getDeviceLabel());
            labelsById.put(id, label != null ? label : "Unknown device");
            String templateName = text(device.getTemplateName());
            DeviceTemplateDto.DeviceManifest manifest = templateName == null
                    ? null : manifestsByName.get(templateName.toLowerCase(Locale.ROOT));
            if (manifest == null || manifest.getInternalVariables() == null) {
                continue;
            }
            Set<String> sharedNames = new HashSet<>();
            for (DeviceTemplateDto.DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                String variableName = variable == null ? null : text(variable.getName());
                if (variableName != null && !Boolean.TRUE.equals(variable.getIsInside())) {
                    sharedNames.add(variableName.toLowerCase(Locale.ROOT));
                }
            }
            if (!sharedNames.isEmpty()) {
                sharedVariablesByDeviceId.put(id, sharedNames);
            }
        }
        return new Context(labelsById, sharedVariablesByDeviceId);
    }

    public static String format(SpecificationDto spec, Context context) {
        Context safeContext = context == null ? Context.empty() : context;
        String a = conditionGroup(spec.getAConditions(), safeContext);
        String antecedent = conditionGroup(spec.getIfConditions(), safeContext);
        String consequence = conditionGroup(spec.getThenConditions(), safeContext);
        return switch (text(spec.getTemplateId()) == null ? "" : spec.getTemplateId().trim()) {
            case "1" -> "CTL AG(" + a + ")";
            case "2" -> "CTL AF(" + a + ")";
            case "3" -> "CTL AG NOT (" + a + ")";
            case "4" -> "CTL AG((" + antecedent + ") -> AX(" + consequence + "))";
            case "5" -> "CTL AG((" + antecedent + ") -> AF(" + consequence + "))";
            case "6" -> "LTL G((" + antecedent + ") -> F G(" + consequence + "))";
            case "7" -> "CTL AG NOT (" + a + " AND "
                    + untrustedSourcePreview(spec.getAConditions(), safeContext) + ")";
            default -> "Structured specification";
        };
    }

    public static String templateLabel(String templateId) {
        return switch (text(templateId) == null ? "" : templateId.trim()) {
            case "1" -> "Always";
            case "2" -> "Eventually";
            case "3" -> "Never";
            case "4" -> "Immediate response";
            case "5" -> "Eventual response";
            case "6" -> "Persistence";
            case "7" -> "Untrusted-source safety";
            default -> "Formal specification";
        };
    }

    private static String conditionGroup(List<SpecConditionDto> conditions, Context context) {
        List<String> parts = new ArrayList<>();
        for (SpecConditionDto condition : conditions == null ? List.<SpecConditionDto>of() : conditions) {
            if (condition != null) {
                parts.add(condition(condition, context));
            }
        }
        return parts.isEmpty() ? "TRUE" : String.join(" AND ", parts);
    }

    private static String condition(SpecConditionDto condition, Context context) {
        String target = target(condition, context);
        if ("api".equalsIgnoreCase(condition.getTargetType())) {
            return target;
        }
        String relation = SmvRelationUtils.normalizeRelation(condition.getRelation());
        if (relation == null || relation.isBlank()) {
            relation = "=";
        }
        return target + " " + relation + " "
                + value(condition.getValue(), relation, condition.getTargetType());
    }

    private static String target(SpecConditionDto condition, Context context) {
        String deviceId = text(condition.getDeviceId());
        String device = quote(context.displayLabel(condition));
        String keyText = text(condition.getKey());
        String key = quote(keyText == null ? "property" : keyText);
        String targetType = text(condition.getTargetType());
        targetType = targetType == null ? "" : targetType.toLowerCase(Locale.ROOT);
        if ("state".equals(targetType)) {
            return device + ".state";
        }
        if ("api".equals(targetType)) {
            return "actionEvent(" + device + ", " + key + ")";
        }

        String variableTarget = context.isSharedVariable(deviceId, keyText)
                ? "Environment." + key
                : device + "." + key;
        if ("trust".equals(targetType)) {
            String source = "state".equalsIgnoreCase(condition.getPropertyScope())
                    ? device + ".current " + key + " state"
                    : variableTarget;
            return "controlSource(" + source + ")";
        }
        if ("privacy".equals(targetType)) {
            String source = "state".equalsIgnoreCase(condition.getPropertyScope())
                    ? device + ".current " + key + " state"
                    : variableTarget;
            return "sensitivity(" + source + ")";
        }
        return variableTarget;
    }

    private static String untrustedSourcePreview(List<SpecConditionDto> conditions, Context context) {
        List<String> sources = new ArrayList<>();
        for (SpecConditionDto condition : conditions == null ? List.<SpecConditionDto>of() : conditions) {
            if (condition != null) {
                sources.add("controlSource(" + target(condition, context) + ") = untrusted");
            }
        }
        if (sources.isEmpty()) {
            return "untrustedSource(TRUE)";
        }
        return sources.size() == 1 ? sources.get(0) : "(" + String.join(" OR ", sources) + ")";
    }

    private static String value(String rawValue, String relation, String targetType) {
        String value = rawValue == null ? "" : rawValue.trim();
        if ("in".equals(relation) || "not in".equals(relation)) {
            String separator = "state".equalsIgnoreCase(targetType) ? "[,|]" : "[,;|]";
            List<String> values = java.util.Arrays.stream(value.split(separator))
                    .map(String::trim)
                    .filter(item -> !item.isEmpty())
                    .map(SpecificationFormulaPreview::scalar)
                    .toList();
            return "{" + String.join(", ", values) + "}";
        }
        return scalar(value);
    }

    private static String scalar(String value) {
        if (value != null && value.matches("-?\\d+(?:\\.\\d+)?")) {
            return value;
        }
        if ("TRUE".equalsIgnoreCase(value) || "FALSE".equalsIgnoreCase(value)) {
            return value.toUpperCase(Locale.ROOT);
        }
        if ("trusted".equalsIgnoreCase(value) || "untrusted".equalsIgnoreCase(value)
                || "public".equalsIgnoreCase(value) || "private".equalsIgnoreCase(value)) {
            return value.toLowerCase(Locale.ROOT);
        }
        return quote(value);
    }

    private static String quote(String value) {
        String text = value == null ? "?" : value;
        return "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    private static String text(String value) {
        return value == null || value.isBlank() ? null : value.trim();
    }

    public record Context(Map<String, String> labelsById,
                          Map<String, Set<String>> sharedVariablesByDeviceId) {
        private static Context empty() {
            return new Context(Map.of(), Map.of());
        }

        public String displayLabel(SpecConditionDto condition) {
            String id = condition == null ? null : text(condition.getDeviceId());
            if (id != null && text(labelsById.get(id)) != null) {
                return labelsById.get(id).trim();
            }
            String snapshot = condition == null ? null : text(condition.getDeviceLabel());
            return snapshot != null ? snapshot : "Unknown device";
        }

        public boolean isSharedVariable(String deviceId, String variableName) {
            String id = text(deviceId);
            String name = text(variableName);
            if (id == null || name == null) {
                return false;
            }
            return sharedVariablesByDeviceId.getOrDefault(id, Set.of())
                    .contains(name.toLowerCase(Locale.ROOT));
        }
    }
}
