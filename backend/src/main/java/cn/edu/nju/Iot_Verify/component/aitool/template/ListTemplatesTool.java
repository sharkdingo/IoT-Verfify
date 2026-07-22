package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.stream.Collectors;

@Slf4j
@Component
public class ListTemplatesTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public ListTemplatesTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "list_templates";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "maxLength", 100,
                "description", "Optional keyword to filter templates by name. Leave empty to return all."
        ));
        props.put("detail", Map.of(
                "type", "boolean",
                "description", "If true, return semantic manifest details (modes, variables, APIs, transitions) without the UI-only Icon. Default false (summary only)."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return LlmToolSpec.of(getName(), "List available device templates. Templates define device behavior: modes, variables, transitions, and APIs.", schema);
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            requireOnlyFields(args, "arguments", Set.of("keyword", "detail"));
            String keyword = optionalTextArg(args, "keyword", "", 100);
            boolean detail = booleanArg(args, "detail", false);

            List<DeviceTemplateDto> templates = safeList(boardStorageService.getDeviceTemplates(userId));

            if (!keyword.isBlank()) {
                String kw = keyword.toLowerCase(Locale.ROOT);
                templates = templates.stream()
                        .filter(t -> t.getName() != null && t.getName().toLowerCase(Locale.ROOT).contains(kw))
                        .collect(Collectors.toList());
            }

            if (templates.isEmpty()) {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No templates found.",
                        "count", 0
                ));
            }

            if (detail) {
                List<Map<String, Object>> details = templates.stream()
                        .map(this::detailView)
                        .toList();
                return objectMapper.writeValueAsString(Map.of("count", details.size(), "templates", details));
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
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("list_templates busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("list_templates business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("list_templates failed", e);
            return errorJson("Failed to list templates.", "INTERNAL_ERROR", 500);
        }
    }

    private Map<String, Object> detailView(DeviceTemplateDto template) {
        Map<String, Object> detail = new LinkedHashMap<>();
        detail.put("id", template.getId());
        detail.put("name", template.getName());
        detail.put("defaultTemplate", template.getDefaultTemplate());
        if (template.getManifest() != null) {
            Map<String, Object> manifest = objectMapper.convertValue(
                    template.getManifest(), new TypeReference<LinkedHashMap<String, Object>>() { });
            manifest.remove("Icon");
            detail.put("manifest", manifest);
        }
        return detail;
    }
}
