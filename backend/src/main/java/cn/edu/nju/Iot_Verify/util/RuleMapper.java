package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto.Command;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto.Condition;
import cn.edu.nju.Iot_Verify.po.RulePo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.List;

@Slf4j
@Component
@RequiredArgsConstructor
public class RuleMapper {

    private final ObjectMapper objectMapper;

    public RuleDto toDto(RulePo po) {
        if (po == null) {
            return null;
        }

        List<Condition> conditions = parseConditions(po.getConditionsJson());
        Command command = parseCommand(po.getCommandJson());

        return RuleDto.builder()
                .id(po.getId())
                .userId(po.getUserId())
                .conditions(conditions)
                .command(command)
                .ruleString(po.getRuleString())
                .build();
    }

    public RulePo toPo(RuleDto dto, Long userId) {
        if (dto == null) {
            return null;
        }

        return RulePo.builder()
                .id(dto.getId())
                .userId(userId)
                .conditionsJson(writeConditions(dto.getConditions()))
                .commandJson(writeCommand(dto.getCommand()))
                .ruleString(dto.getRuleString())
                .build();
    }

    private List<Condition> parseConditions(String json) {
        if (json == null || json.isEmpty()) {
            return new ArrayList<>();
        }
        try {
            return objectMapper.readValue(json, new TypeReference<List<Condition>>() {});
        } catch (Exception e) {
            log.error("Failed to parse conditions JSON: {}", e.getMessage());
            return new ArrayList<>();
        }
    }

    private Command parseCommand(String json) {
        if (json == null || json.isEmpty()) {
            return null;
        }
        try {
            return objectMapper.readValue(json, Command.class);
        } catch (Exception e) {
            log.error("Failed to parse command JSON: {}", e.getMessage());
            return null;
        }
    }

    private String writeConditions(List<Condition> conditions) {
        if (conditions == null || conditions.isEmpty()) {
            return "[]";
        }
        try {
            return objectMapper.writeValueAsString(conditions);
        } catch (Exception e) {
            log.error("Failed to write conditions JSON: {}", e.getMessage());
            return "[]";
        }
    }

    private String writeCommand(Command command) {
        if (command == null) {
            return null;
        }
        try {
            return objectMapper.writeValueAsString(command);
        } catch (Exception e) {
            log.error("Failed to write command JSON: {}", e.getMessage());
            return null;
        }
    }
}
