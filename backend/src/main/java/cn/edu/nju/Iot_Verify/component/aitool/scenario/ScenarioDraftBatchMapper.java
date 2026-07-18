package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.component.board.BoardBatchRequestParser;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

/** Converts the portable scene returned by {@code recommend_scenario} into the board batch DTO. */
@Component
@RequiredArgsConstructor
public class ScenarioDraftBatchMapper {

    private final ObjectMapper objectMapper;
    private final BoardBatchRequestParser boardBatchRequestParser;

    public BoardBatchDto toBatch(JsonNode scene, String impactToken) {
        if (scene == null || !scene.isObject()) {
            throw new BadRequestException("The stored scenario draft is invalid; no board data was changed.");
        }
        ObjectNode body = objectMapper.createObjectNode();
        body.put("impactToken", requiredText(impactToken, "impactToken"));
        body.set("nodes", requiredArray(scene, "devices"));
        body.set("environmentVariables", requiredArray(scene, "environmentVariables"));
        body.set("templateSnapshots", requiredArray(scene, "templates"));
        body.set("rules", mapRules(requiredArray(scene, "rules")));
        body.set("specs", mapSpecs(requiredArray(scene, "specs")));
        return boardBatchRequestParser.parse(body);
    }

    private ArrayNode mapRules(JsonNode portableRules) {
        ArrayNode rules = objectMapper.createArrayNode();
        for (JsonNode portable : portableRules) {
            if (portable == null || !portable.isObject()) {
                throw new BadRequestException("The stored scenario contains an invalid rule; no board data was changed.");
            }
            ObjectNode rule = objectMapper.createObjectNode();
            ArrayNode conditions = objectMapper.createArrayNode();
            JsonNode sources = requiredArray(portable, "sources");
            for (JsonNode source : sources) {
                if (source == null || !source.isObject()) {
                    throw new BadRequestException("The stored scenario contains an invalid rule source; no board data was changed.");
                }
                ObjectNode condition = objectMapper.createObjectNode();
                condition.put("deviceName", requiredText(source, "fromId"));
                String targetType = requiredText(source, "itemType");
                condition.put("targetType", targetType);
                condition.put("attribute", "state".equalsIgnoreCase(targetType)
                        ? "state" : requiredText(source, "fromApi"));
                if (!"api".equalsIgnoreCase(targetType)) {
                    condition.put("relation", requiredText(source, "relation"));
                    condition.put("value", requiredText(source, "value"));
                }
                conditions.add(condition);
            }
            rule.set("conditions", conditions);
            ObjectNode command = objectMapper.createObjectNode();
            command.put("deviceName", requiredText(portable, "toId"));
            command.put("action", requiredText(portable, "toApi"));
            copyOptionalText(portable, command, "contentDevice");
            copyOptionalText(portable, command, "content");
            rule.set("command", command);
            rule.put("ruleString", portable.path("name").isTextual()
                    ? portable.path("name").asText() : "");
            rules.add(rule);
        }
        return rules;
    }

    private ArrayNode mapSpecs(JsonNode portableSpecs) {
        ArrayNode specs = objectMapper.createArrayNode();
        int index = 1;
        for (JsonNode portable : portableSpecs) {
            if (portable == null || !portable.isObject()) {
                throw new BadRequestException("The stored scenario contains an invalid specification; no board data was changed.");
            }
            ObjectNode spec = objectMapper.createObjectNode();
            spec.put("id", "chat_scene_spec_" + index++);
            spec.put("templateId", requiredText(portable, "templateId"));
            spec.set("aConditions", mapConditions(requiredArray(portable, "aConditions")));
            spec.set("ifConditions", mapConditions(requiredArray(portable, "ifConditions")));
            spec.set("thenConditions", mapConditions(requiredArray(portable, "thenConditions")));
            specs.add(spec);
        }
        return specs;
    }

    private ArrayNode mapConditions(JsonNode portableConditions) {
        ArrayNode conditions = objectMapper.createArrayNode();
        for (JsonNode portable : portableConditions) {
            if (portable == null || !portable.isObject()) {
                throw new BadRequestException("The stored scenario contains an invalid specification condition; no board data was changed.");
            }
            ObjectNode condition = objectMapper.createObjectNode();
            condition.put("deviceId", requiredText(portable, "deviceId"));
            condition.put("targetType", requiredText(portable, "targetType"));
            condition.put("key", requiredText(portable, "key"));
            copyOptionalText(portable, condition, "propertyScope");
            condition.put("relation", requiredText(portable, "relation"));
            condition.put("value", requiredText(portable, "value"));
            conditions.add(condition);
        }
        return conditions;
    }

    private ArrayNode requiredArray(JsonNode object, String field) {
        JsonNode value = object.path(field);
        if (!value.isArray()) {
            throw new BadRequestException("The stored scenario is missing its " + field
                    + " collection; no board data was changed.");
        }
        return (ArrayNode) value.deepCopy();
    }

    private String requiredText(JsonNode object, String field) {
        return requiredText(object.path(field).isTextual() ? object.path(field).asText() : null, field);
    }

    private String requiredText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new BadRequestException("The stored scenario is missing " + field
                    + "; no board data was changed.");
        }
        return value.trim();
    }

    private void copyOptionalText(JsonNode source, ObjectNode target, String field) {
        JsonNode value = source.path(field);
        if (value.isTextual() && !value.asText().isBlank()) {
            target.put(field, value.asText());
        }
    }
}
