package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class SmvRulesModuleBuilder {

    public String build(List<RuleDto> rules, Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder content = new StringBuilder();
        
        appendRulesAsComments(content, rules);
        
        return content.toString();
    }
    
    private void appendRulesAsComments(StringBuilder content, List<RuleDto> rules) {
        if (rules == null || rules.isEmpty()) {
            content.append("--No rules defined\n\n");
            return;
        }

        for (RuleDto rule : rules) {
            if (rule.getRuleString() != null && !rule.getRuleString().isEmpty()) {
                content.append("--").append(rule.getRuleString()).append("\n");
            } else {
                content.append("--IF ");
                if (rule.getConditions() != null) {
                    boolean first = true;
                    for (RuleDto.Condition cond : rule.getConditions()) {
                        if (!first) content.append(" & ");
                        first = false;
                        content.append(cond.getDeviceName()).append(".")
                               .append(cond.getAttribute());
                        if (cond.getRelation() != null) {
                            content.append(cond.getRelation()).append(cond.getValue());
                        }
                    }
                }
                content.append(" THEN ");
                if (rule.getCommand() != null) {
                    content.append(rule.getCommand().getDeviceName())
                           .append(".").append(rule.getCommand().getAction());
                }
                content.append("\n");
            }
        }
        content.append("\n");
    }
}
