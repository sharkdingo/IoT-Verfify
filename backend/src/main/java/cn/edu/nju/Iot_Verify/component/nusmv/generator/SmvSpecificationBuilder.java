package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Map;

@Slf4j
@Component
public class SmvSpecificationBuilder {

    private static final String PERSISTENCE_TEMPLATE_ID = "6";
    private static final String CONDITION_SEPARATOR = " & ";

    public String build(java.util.List<SpecificationDto> specs, boolean isAttack, int intensity, 
                       Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder content = new StringBuilder();
        
        if (specs == null || specs.isEmpty()) {
            log.debug("No specifications provided - skipping SPECIFICATION section");
            return content.toString();
        }
        
        content.append("\nSPECIFICATION\n");

        int generatedSpecs = 0;
        for (SpecificationDto spec : specs) {
            if (spec == null) continue;
            if ((spec.getAConditions() == null || spec.getAConditions().isEmpty()) &&
                (spec.getIfConditions() == null || spec.getIfConditions().isEmpty())) continue;

            String specString = generateSpecString(spec, isAttack, intensity, deviceSmvMap);
            content.append("\t").append(specString).append("\n");
            generatedSpecs++;
        }
        
        log.debug("Generated {} specifications", generatedSpecs);
        return content.toString();
    }

    /**
     * 生成单个规格字符串（预览用，需要传入 deviceSmvMap）
     */
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity) {
        log.warn("generateSpecString called without deviceSmvMap - results may be incomplete");
        return generateSpecString(spec, isAttack, intensity, null);
    }

    private String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity, 
                                     Map<String, DeviceSmvData> deviceSmvMap) {
        if (PERSISTENCE_TEMPLATE_ID.equals(spec.getTemplateId())) {
            return generateLtlSpec(spec, isAttack, intensity, deviceSmvMap);
        }
        return generateCtlSpec(spec, isAttack, intensity, deviceSmvMap);
    }

    private String generateLtlSpec(SpecificationDto spec, boolean isAttack, int intensity, 
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder aBuilder = new StringBuilder();
        StringBuilder bBuilder = new StringBuilder();

        if (spec.getIfConditions() != null) {
            for (SpecConditionDto cond : spec.getIfConditions()) {
                aBuilder.append(genConditionSpec(cond, deviceSmvMap)).append(CONDITION_SEPARATOR);
            }
        }

        if (spec.getThenConditions() != null) {
            for (SpecConditionDto cond : spec.getThenConditions()) {
                bBuilder.append(genConditionSpec(cond, deviceSmvMap)).append(CONDITION_SEPARATOR);
            }
        }

        removeTrailingSeparator(aBuilder);
        removeTrailingSeparator(bBuilder);

        StringBuilder constraintBuilder = new StringBuilder();
        if (isAttack && intensity > 0) {
            constraintBuilder.append(" & intensity<=").append(intensity);
        }

        return "LTLSPEC G(" + aBuilder + " -> F G(" + bBuilder + "))" + constraintBuilder.toString();
    }

    private String generateCtlSpec(SpecificationDto spec, boolean isAttack, int intensity, 
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder conditionBuilder = new StringBuilder();

        if (spec.getAConditions() != null) {
            for (SpecConditionDto cond : spec.getAConditions()) {
                conditionBuilder.append(genConditionSpec(cond, deviceSmvMap)).append(CONDITION_SEPARATOR);
            }
        }

        removeTrailingSeparator(conditionBuilder);

        if (isAttack && intensity > 0) {
            conditionBuilder.append(" & intensity<=").append(intensity);
        }

        return "CTLSPEC AG(" + conditionBuilder + ")";
    }

    private String genConditionSpec(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder sb = new StringBuilder();
        
        if (cond == null || cond.getDeviceId() == null) {
            log.warn("Invalid condition: deviceId is null");
            return "TRUE";
        }
        
        DeviceSmvData smv = deviceSmvMap != null ? deviceSmvMap.get(cond.getDeviceId()) : null;
        String varName = smv != null ? smv.getVarName() : cond.getDeviceId();
        sb.append(varName).append(".");

        if ("state".equals(cond.getTargetType())) {
            sb.append("state");
        } else if ("variable".equals(cond.getTargetType())) {
            if (cond.getKey() == null) {
                log.warn("Condition key is null for variable targetType");
                return sb.toString();
            }
            sb.append(cond.getKey());
        } else if ("trust".equals(cond.getTargetType())) {
            if (cond.getKey() == null) {
                log.warn("Condition key is null for trust targetType");
                return sb.toString();
            }
            sb.append("trust_").append(cond.getKey());
        } else if ("privacy".equals(cond.getTargetType())) {
            if (cond.getKey() == null) {
                log.warn("Condition key is null for privacy targetType");
                return sb.toString();
            }
            sb.append("privacy_").append(cond.getKey());
        } else {
            sb.append(cond.getTargetType() != null ? cond.getTargetType() : "state");
        }
        
        if (cond.getRelation() == null || cond.getValue() == null) {
            log.warn("Condition relation or value is null for device: {}", cond.getDeviceId());
            return sb.toString();
        }
        
        sb.append(cond.getRelation()).append(cond.getValue());
        return sb.toString();
    }
    


    private void removeTrailingSeparator(StringBuilder builder) {
        if (builder.length() > CONDITION_SEPARATOR.length()) {
            builder.setLength(builder.length() - CONDITION_SEPARATOR.length());
        }
    }
}
