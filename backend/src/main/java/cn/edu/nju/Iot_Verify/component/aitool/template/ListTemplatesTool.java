package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.stream.Collectors;

@Slf4j
@Component
@RequiredArgsConstructor
public class ListTemplatesTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "list_templates";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "description", "Optional keyword to filter templates by name. Leave empty to return all."
        ));
        props.put("detail", Map.of(
                "type", "boolean",
                "description", "If true, return full manifest details (modes, variables, APIs, transitions). Default false (summary only)."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("List available device templates. Templates define device behavior: modes, variables, transitions, and APIs.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return "{\"error\": \"User not logged in\"}";
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String keyword = args.path("keyword").asText("").trim();
            boolean detail = args.path("detail").asBoolean(false);

            List<DeviceTemplateDto> templates = safeList(boardStorageService.getDeviceTemplates(userId));

            if (!keyword.isBlank()) {
                String kw = keyword.toLowerCase(Locale.ROOT);
                templates = templates.stream()
                        .filter(t -> t.getName() != null && t.getName().toLowerCase(Locale.ROOT).contains(kw))
                        .collect(Collectors.toList());
            }

            if (templates.isEmpty()) {
                return "{\"message\": \"No templates found.\", \"count\": 0}";
            }

            if (detail) {
                return objectMapper.writeValueAsString(Map.of("count", templates.size(), "templates", templates));
            }

            // Summary mode: name + description + modes + API names
            List<Map<String, Object>> summaries = templates.stream().map(t -> {
                Map<String, Object> summary = new LinkedHashMap<>();
                summary.put("id", t.getId());
                summary.put("name", t.getName());
                if (t.getManifest() != null) {
                    summary.put("description", t.getManifest().getDescription());
                    summary.put("modes", t.getManifest().getModes());
                    if (t.getManifest().getApis() != null) {
                        summary.put("apis", t.getManifest().getApis().stream()
                                .map(DeviceTemplateDto.DeviceManifest.API::getName)
                                .toList());
                    }
                }
                return summary;
            }).toList();

            return objectMapper.writeValueAsString(Map.of("count", summaries.size(), "templates", summaries));
        } catch (Exception e) {
            log.error("list_templates failed", e);
            return "{\"error\": \"Failed to list templates: " + e.getMessage() + "\"}";
        }
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }
}
