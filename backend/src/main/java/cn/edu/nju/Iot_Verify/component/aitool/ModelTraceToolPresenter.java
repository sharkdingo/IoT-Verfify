package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTriggeredRuleDto;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/** User-semantic projections for chat tools; persistence/model ids stay out of ordinary output. */
public final class ModelTraceToolPresenter {

    private ModelTraceToolPresenter() {
    }

    public static Map<String, Object> violatedSpecification(TraceDto trace) {
        SpecificationDto specification = trace != null ? trace.getViolatedSpec() : null;
        Map<String, Object> result = violatedSpecification(specification);
        String checkedExpression = trace != null ? trace.getCheckedExpression() : null;
        putText(result, "formulaKind", formulaKind(checkedExpression,
                specification != null ? specification.getTemplateId() : null));
        putText(result, "checkedExpression", checkedExpression);
        return result;
    }

    public static Map<String, Object> violatedSpecification(SpecificationDto specification) {
        Map<String, Object> result = new LinkedHashMap<>();
        if (specification != null) {
            putText(result, "specificationLabel", specification.getTemplateLabel());
            putText(result, "formulaPreview", specification.getFormula());
            putConditions(result, "aConditions", specification.getAConditions());
            putConditions(result, "ifConditions", specification.getIfConditions());
            putConditions(result, "thenConditions", specification.getThenConditions());
            putText(result, "formulaKind", formulaKind(null, specification.getTemplateId()));
        }
        return result;
    }

    public static List<Map<String, Object>> states(List<TraceStateDto> states) {
        if (states == null || states.isEmpty()) return List.of();
        List<Map<String, Object>> presented = new ArrayList<>(states.size());
        for (TraceStateDto state : states) {
            if (state == null) continue;
            Map<String, Object> item = new LinkedHashMap<>();
            item.put("stateIndex", state.getStateIndex());
            item.put("devices", devices(state.getDevices()));
            item.put("triggeredRules", rules(state.getTriggeredRules()));
            item.put("compromisedAutomationLinks", rules(state.getCompromisedAutomationLinks()));
            item.put("trustPrivacies", safeList(state.getTrustPrivacies()));
            item.put("environmentVariables", safeList(state.getEnvVariables()));
            item.put("globalVariables", safeList(state.getGlobalVariables()));
            presented.add(item);
        }
        return List.copyOf(presented);
    }

    private static List<Map<String, Object>> devices(List<TraceDeviceDto> devices) {
        if (devices == null || devices.isEmpty()) return List.of();
        List<Map<String, Object>> presented = new ArrayList<>(devices.size());
        for (TraceDeviceDto device : devices) {
            if (device == null) continue;
            Map<String, Object> item = new LinkedHashMap<>();
            putText(item, "deviceLabel", device.getDeviceLabel());
            putText(item, "deviceType", device.getTemplateName());
            putText(item, "state", device.getState());
            putText(item, "mode", device.getMode());
            if (device.getCompromised() != null) item.put("compromised", device.getCompromised());
            item.put("variables", safeList(device.getVariables()));
            item.put("trustPrivacyLabels", safeList(device.getTrustPrivacy()));
            item.put("privacyLabels", safeList(device.getPrivacies()));
            presented.add(item);
        }
        return List.copyOf(presented);
    }

    private static List<Map<String, Object>> rules(List<TraceTriggeredRuleDto> rules) {
        if (rules == null || rules.isEmpty()) return List.of();
        List<Map<String, Object>> presented = new ArrayList<>(rules.size());
        for (TraceTriggeredRuleDto rule : rules) {
            if (rule == null) continue;
            Map<String, Object> item = new LinkedHashMap<>();
            putText(item, "ruleLabel", rule.getRuleLabel());
            if (!item.isEmpty()) presented.add(item);
        }
        return List.copyOf(presented);
    }

    private static void putConditions(Map<String, Object> target,
                                      String field,
                                      List<SpecConditionDto> conditions) {
        if (conditions == null || conditions.isEmpty()) return;
        List<Map<String, Object>> presented = new ArrayList<>(conditions.size());
        for (SpecConditionDto condition : conditions) {
            if (condition == null) continue;
            Map<String, Object> item = new LinkedHashMap<>();
            putText(item, "deviceLabel", condition.getDeviceLabel());
            putText(item, "targetType", condition.getTargetType());
            putText(item, "propertyScope", condition.getPropertyScope());
            putText(item, "key", condition.getKey());
            putText(item, "relation", condition.getRelation());
            putText(item, "value", condition.getValue());
            if (!item.isEmpty()) presented.add(item);
        }
        if (!presented.isEmpty()) target.put(field, List.copyOf(presented));
    }

    private static String formulaKind(String checkedExpression, String templateId) {
        String normalized = checkedExpression == null
                ? "" : checkedExpression.trim().toUpperCase(Locale.ROOT);
        if (normalized.startsWith("LTLSPEC") || normalized.startsWith("LTL SPEC")) return "LTL";
        if (normalized.startsWith("CTLSPEC") || normalized.startsWith("CTL SPEC")
                || normalized.startsWith("SPEC")) return "CTL";
        if (templateId == null || templateId.isBlank()) return null;
        return "6".equals(templateId) ? "LTL" : "CTL";
    }

    private static void putText(Map<String, Object> target, String field, String value) {
        if (value != null && !value.isBlank()) target.put(field, value);
    }

    private static <T> List<T> safeList(List<T> values) {
        return values == null || values.isEmpty() ? List.of() : List.copyOf(values);
    }
}
