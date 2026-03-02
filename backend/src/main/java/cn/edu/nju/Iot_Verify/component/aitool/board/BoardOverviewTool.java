package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

@Slf4j
@Component
@RequiredArgsConstructor
public class BoardOverviewTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "board_overview";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", Collections.emptyMap(), Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Get an overview of the current board: devices, rules, and specifications summary.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            List<DeviceNodeDto> nodes = safeList(boardStorageService.getNodes(userId));
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));

            Map<String, Object> overview = new LinkedHashMap<>();
            overview.put("deviceCount", nodes.size());
            overview.put("ruleCount", rules.size());
            overview.put("specCount", specs.size());

            List<Map<String, Object>> deviceSummaries = nodes.stream()
                    .filter(Objects::nonNull)
                    .map(n -> {
                Map<String, Object> d = new LinkedHashMap<>();
                d.put("id", n.getId());
                d.put("label", n.getLabel());
                d.put("templateName", n.getTemplateName());
                d.put("state", n.getState());
                return d;
            }).toList();
            overview.put("devices", deviceSummaries);

            List<Map<String, Object>> ruleSummaries = rules.stream()
                    .filter(Objects::nonNull)
                    .map(r -> {
                Map<String, Object> rs = new LinkedHashMap<>();
                rs.put("id", r.getId());

                List<RuleDto.Condition> conditions = r.getConditions() == null ? List.of() : r.getConditions();
                String condStr = conditions.stream()
                        .filter(Objects::nonNull)
                        .map(c -> safe(c.getDeviceName()) + "." + safe(c.getAttribute())
                                + (c.getRelation() != null ? c.getRelation() : "=")
                                + (c.getValue() != null ? c.getValue() : ""))
                        .collect(Collectors.joining(" AND "));
                rs.put("condition", condStr);

                RuleDto.Command command = r.getCommand();
                if (command != null) {
                    rs.put("action", safe(command.getDeviceName()) + "." + safe(command.getAction()));
                } else {
                    rs.put("action", "");
                }
                return rs;
            }).toList();
            overview.put("rules", ruleSummaries);

            List<Map<String, Object>> specSummaries = specs.stream()
                    .filter(Objects::nonNull)
                    .map(s -> {
                Map<String, Object> ss = new LinkedHashMap<>();
                ss.put("id", s.getId());
                ss.put("label", s.getTemplateLabel());
                ss.put("thenConditionCount", s.getThenConditions() != null ? s.getThenConditions().size() : 0);
                ss.put("ifConditionCount", s.getIfConditions() != null ? s.getIfConditions().size() : 0);
                ss.put("aConditionCount", s.getAConditions() != null ? s.getAConditions().size() : 0);
                return ss;
            }).toList();
            overview.put("specs", specSummaries);

            return objectMapper.writeValueAsString(overview);
        } catch (Exception e) {
            log.error("board_overview failed", e);
            return errorJson("Failed to get board overview. Please retry.");
        }
    }

    private <T> List<T> safeList(List<T> values) {
        return values == null ? List.of() : values;
    }

    private String safe(String value) {
        return value == null ? "" : value;
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception ex) {
            return "{\"error\":\"" + message + "\"}";
        }
    }
}
