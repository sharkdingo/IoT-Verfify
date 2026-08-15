package cn.edu.nju.Iot_Verify.component.board;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

/**
 * The one converter from the portable scene format to the internal board write contract.
 *
 * <p>Every producer of a portable scene shares it: an uploaded scene file
 * ({@code POST /api/board/scene}) and a chat-generated draft ({@code apply_scenario}). It was
 * previously implemented twice — once here for the chat tool and once in the frontend's
 * {@code api/board.ts} for file import — so the same scene could be admitted differently
 * depending on which button the user pressed. The {@code variableSource} field was dropped by
 * each copy independently, producing three separate user-visible failures before all three copies
 * agreed.</p>
 *
 * <p>{@code specIdPrefix} is the caller's provenance marker for the generated specification ids.
 * Portable scenes carry no database ids by design, so ids are minted here; the prefix records
 * which entry point minted them and keeps the two sources distinguishable in stored data.</p>
 */
@Component
@RequiredArgsConstructor
public class PortableSceneBatchMapper {

    private final ObjectMapper objectMapper;
    private final BoardBatchRequestParser boardBatchRequestParser;

    /**
     * Converts a portable scene into a validated batch command.
     *
     * @param scene        the portable scene object; its {@code schema}/{@code version} must already
     *                     have been admitted by the caller that knows where it came from
     * @param impactToken  the token from the replacement preview the user confirmed
     * @param specIdPrefix provenance prefix for minted specification ids
     */
    public BoardBatchDto toBatch(JsonNode scene, String impactToken, String specIdPrefix) {
        if (scene == null || !scene.isObject()) {
            throw new BadRequestException("The scene is invalid; no board data was changed.");
        }
        ObjectNode body = objectMapper.createObjectNode();
        body.put("impactToken", requiredText(impactToken, "impactToken"));
        body.set("nodes", requiredArray(scene, "devices"));
        body.set("environmentVariables", requiredArray(scene, "environmentVariables"));
        body.set("templateSnapshots", requiredArray(scene, "templates"));
        body.set("rules", mapRules(requiredArray(scene, "rules")));
        body.set("specs", mapSpecs(requiredArray(scene, "specs"), specIdPrefix));
        return boardBatchRequestParser.parse(body);
    }

    private ArrayNode mapRules(JsonNode portableRules) {
        ArrayNode rules = objectMapper.createArrayNode();
        for (JsonNode portable : portableRules) {
            if (portable == null || !portable.isObject()) {
                throw new BadRequestException("The scene contains an invalid rule; no board data was changed.");
            }
            ObjectNode rule = objectMapper.createObjectNode();
            rule.set("conditions", mapRuleSources(requiredArray(portable, "sources")));
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

    private ArrayNode mapRuleSources(JsonNode sources) {
        ArrayNode conditions = objectMapper.createArrayNode();
        for (JsonNode source : sources) {
            if (source == null || !source.isObject()) {
                throw new BadRequestException("The scene contains an invalid rule source; no board data was changed.");
            }
            ObjectNode condition = objectMapper.createObjectNode();
            condition.put("deviceName", requiredText(source, "fromId"));
            String targetType = requiredText(source, "itemType");
            condition.put("targetType", targetType);
            condition.put("attribute", "state".equalsIgnoreCase(targetType)
                    ? "state" : requiredText(source, "fromApi"));
            // An `api` source is a signal event: RuleDto.isApiSignalShapeValid rejects it outright if
            // it carries a relation or value, so these two must be omitted rather than blanked.
            if (!"api".equalsIgnoreCase(targetType)) {
                condition.put("relation", requiredText(source, "relation"));
                condition.put("value", requiredText(source, "value"));
            }
            conditions.add(condition);
        }
        return conditions;
    }

    private ArrayNode mapSpecs(JsonNode portableSpecs, String specIdPrefix) {
        String prefix = requiredText(specIdPrefix, "specIdPrefix");
        ArrayNode specs = objectMapper.createArrayNode();
        int index = 1;
        for (JsonNode portable : portableSpecs) {
            if (portable == null || !portable.isObject()) {
                throw new BadRequestException("The scene contains an invalid specification; no board data was changed.");
            }
            ObjectNode spec = objectMapper.createObjectNode();
            spec.put("id", prefix + index++);
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
                throw new BadRequestException("The scene contains an invalid specification condition; "
                        + "no board data was changed.");
            }
            ObjectNode condition = objectMapper.createObjectNode();
            condition.put("deviceId", requiredText(portable, "deviceId"));
            condition.put("targetType", requiredText(portable, "targetType"));
            condition.put("key", requiredText(portable, "key"));
            copyOptionalText(portable, condition, "propertyScope");
            // Carried, not dropped: a `variable` condition is required to state which question it asks,
            // and stripping it here made the scene fail admission on a field the scene actually had —
            // an error naming a field the user never wrote and cannot fix.
            copyOptionalText(portable, condition, "variableSource");
            condition.put("relation", requiredText(portable, "relation"));
            condition.put("value", requiredText(portable, "value"));
            conditions.add(condition);
        }
        return conditions;
    }

    private ArrayNode requiredArray(JsonNode object, String field) {
        JsonNode value = object.path(field);
        if (!value.isArray()) {
            throw new BadRequestException("The scene is missing its " + field
                    + " collection; no board data was changed.");
        }
        return (ArrayNode) value.deepCopy();
    }

    private String requiredText(JsonNode object, String field) {
        return requiredText(object.path(field).isTextual() ? object.path(field).asText() : null, field);
    }

    private String requiredText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new BadRequestException("The scene is missing " + field
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
