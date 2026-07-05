package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * 智能设备推荐工具
 * 根据用户画布中现有的所有设备，从系统可用模板中推荐最合适的设备来完善整个物联网系统
 */
@Slf4j
@Component
public class RecommendRelatedDevicesTool extends AbstractAiTool {

    private final PromptCompletionService promptCompletionService;

    private static final double TEMPERATURE = 0.7;
    private static final int MAX_TOKENS = 4000;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)设备推荐助手。你的任务是分析用户画布中现有的设备，
从系统可用模板中推荐最合适的设备来完善整个物联网系统。

## 输入信息
- 用户画布中现有的设备列表
- 系统可用的设备模板列表

## 输出要求
请分析现有设备的功能和布局，推荐可以增强系统功能的设备，返回符合以下JSON格式的推荐：

```json
{
  "recommendations": [
    {
      "templateName": "设备模板名称（必须是系统中存在的模板）",
      "description": "设备描述",
      "reason": "推荐理由，用自然语言描述为什么推荐这个设备",
      "confidence": 0.0-1.0
    }
  ]
}
```

## 重要约束
- 推荐模板必须是系统中已加载的真实模板名称
- 不要推荐画布中已存在的设备
- 基于现有设备的功能缺口进行推荐
- 每个推荐都必须有合理的置信度
- 如果没有找到合适的推荐，返回空的recommendations数组
- 最多返回5个推荐
""";

    public RecommendRelatedDevicesTool(PromptCompletionService promptCompletionService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.promptCompletionService = promptCompletionService;
    }

    @Override
    public String getName() {
        return "recommend_related_devices";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("devices", Map.of(
                "type", "array",
                "description", "List of current devices on the board"
        ));

        props.put("templates", Map.of(
                "type", "array",
                "description", "List of available device templates"
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("devices", "templates")
        );

        return LlmToolSpec.of(getName(),
                "Analyze current board devices and recommend new devices from available templates. " +
                        "This tool uses AI to find suitable devices that can enhance the IoT system.",
                schema);
    }

    /**
     * 根据画布中所有设备推荐新设备（公开入口，保留原有签名供外部调用）
     */
    public String executeBoardRecommendations(String argsJson) {
        // Delegate to the standard execute() flow (auth + doExecute)
        return execute(argsJson);
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }

            // 获取前端传来的设备列表和模板列表
            JsonNode devicesNode = args.path("devices");
            JsonNode templatesNode = args.path("templates");

            if (devicesNode.isMissingNode() || !devicesNode.isArray()) {
                return errorJson("devices is required and must be an array", "VALIDATION_ERROR", 400);
            }
            if (templatesNode.isMissingNode() || !templatesNode.isArray()) {
                return errorJson("templates is required and must be an array", "VALIDATION_ERROR", 400);
            }

            log.info("=== BOARD DEVICE RECOMMENDATION DEBUG ===");
            log.info("User ID: {}", userId);
            log.info("Devices count: {}", devicesNode.size());
            log.info("Templates count: {}", templatesNode.size());

            // 构建当前画布设备信息
            String currentDevicesInfo = buildCurrentDevicesJson(devicesNode);

            // 构建可用模板信息
            String availableTemplatesInfo = buildAvailableTemplatesJson(templatesNode);

            // 调用 AI 生成推荐
            String aiResponse = generateBoardRecommendationsWithAI(
                    currentDevicesInfo,
                    availableTemplatesInfo
            );

            log.info("AI Response: {}", aiResponse);

            // 解析 AI 响应
            String result = parseBoardRecommendationsResponse(aiResponse, templatesNode, devicesNode);

            log.info("Final Result: {}", result);

            return result;

        } catch (ServiceUnavailableException e) {
            log.warn("recommend_board_devices busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("recommend_board_devices business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("recommend_board_devices failed", e);
            return errorJson("Failed to generate device recommendations.", "INTERNAL_ERROR", 500);
        }
    }

    private String buildCurrentDevicesJson(JsonNode devicesNode) {
        try {
            List<Map<String, Object>> devicesList = new ArrayList<>();
            for (JsonNode device : devicesNode) {
                Map<String, Object> deviceMap = new LinkedHashMap<>();
                deviceMap.put("label", device.path("label").asText(""));
                deviceMap.put("templateName", device.path("templateName").asText(""));
                deviceMap.put("state", device.path("state").asText(""));
                devicesList.add(deviceMap);
            }
            return objectMapper.writeValueAsString(devicesList);
        } catch (Exception e) {
            log.error("Failed to build current devices JSON", e);
            return "[]";
        }
    }

    private String buildAvailableTemplatesJson(JsonNode templatesNode) {
        try {
            List<Map<String, Object>> templatesList = new ArrayList<>();
            for (JsonNode template : templatesNode) {
                Map<String, Object> templateMap = new LinkedHashMap<>();
                templateMap.put("name", template.path("name").asText(""));
                templateMap.put("description", template.path("description").asText(""));

                // 处理变量
                JsonNode variablesNode = template.path("variables");
                if (!variablesNode.isMissingNode() && variablesNode.isArray()) {
                    List<String> vars = new ArrayList<>();
                    for (JsonNode v : variablesNode) {
                        vars.add(v.asText());
                    }
                    templateMap.put("variables", vars);
                }

                // 处理 APIs
                JsonNode apisNode = template.path("apis");
                if (!apisNode.isMissingNode() && apisNode.isArray()) {
                    List<Map<String, String>> apis = new ArrayList<>();
                    for (JsonNode api : apisNode) {
                        Map<String, String> apiMap = new LinkedHashMap<>();
                        apiMap.put("name", api.path("name").asText(""));
                        apiMap.put("description", api.path("description").asText(""));
                        apis.add(apiMap);
                    }
                    templateMap.put("apis", apis);
                }

                // 处理工作状态
                JsonNode statesNode = template.path("workingStates");
                if (!statesNode.isMissingNode() && statesNode.isArray()) {
                    List<String> states = new ArrayList<>();
                    for (JsonNode s : statesNode) {
                        states.add(s.asText());
                    }
                    templateMap.put("workingStates", states);
                }

                templatesList.add(templateMap);
            }
            return objectMapper.writeValueAsString(templatesList);
        } catch (Exception e) {
            log.error("Failed to build available templates JSON", e);
            return "[]";
        }
    }

    private String generateBoardRecommendationsWithAI(String currentDevicesInfo, String availableTemplatesInfo) {
        String userPrompt = "## 现有设备\n" + currentDevicesInfo + "\n\n## 可用模板\n" + availableTemplatesInfo + "\n\n请直接返回JSON格式的推荐结果，不要包含其他文字。";

        log.info("Calling LLM for board device recommendations...");
        String content = promptCompletionService.complete(SYSTEM_PROMPT, userPrompt, TEMPERATURE, MAX_TOKENS);

        if (content == null || content.isBlank()) {
            return "{\"recommendations\": []}";
        }
        return content;
    }

    private String parseBoardRecommendationsResponse(String aiResponse, JsonNode availableTemplatesNode, JsonNode currentDevicesNode) {
        try {
            // 清理 AI 返回的内容
            String cleanedResponse = aiResponse.trim();
            if (cleanedResponse.startsWith("```")) {
                int firstNewline = cleanedResponse.indexOf('\n');
                if (firstNewline > 0) {
                    cleanedResponse = cleanedResponse.substring(firstNewline).trim();
                }
            }
            if (cleanedResponse.endsWith("```")) {
                cleanedResponse = cleanedResponse.substring(0, cleanedResponse.lastIndexOf("```")).trim();
            }

            // 构建可用模板名称映射
            Set<String> availableTemplateNames = new HashSet<>();
            for (JsonNode t : availableTemplatesNode) {
                availableTemplateNames.add(t.path("name").asText("").toLowerCase());
            }

            // 获取当前设备模板名称列表（用于排除已存在的设备）
            Set<String> existingDeviceTemplateNames = new HashSet<>();
            if (!currentDevicesNode.isMissingNode() && currentDevicesNode.isArray()) {
                for (JsonNode device : currentDevicesNode) {
                    String templateName = device.path("templateName").asText("");
                    if (!templateName.isBlank()) {
                        existingDeviceTemplateNames.add(templateName.toLowerCase());
                    }
                }
            }
            log.info("Existing device templates: {}", existingDeviceTemplateNames);

            // 解析 JSON
            JsonNode root = objectMapper.readTree(cleanedResponse);

            JsonNode recommendationsNode = root.path("recommendations");
            if (recommendationsNode.isMissingNode() || !recommendationsNode.isArray()) {
                recommendationsNode = root;
            }

            List<Map<String, Object>> recommendations = new ArrayList<>();
            Set<String> addedTemplates = new HashSet<>();
            int count = 0;

            for (JsonNode rec : recommendationsNode) {
                if (count >= 5) break;

                try {
                    String templateName = rec.path("templateName").asText();
                    if (templateName == null || templateName.isBlank()) {
                        continue;
                    }

                    // 检查模板是否存在于系统中
                    if (!availableTemplateNames.contains(templateName.toLowerCase())) {
                        log.debug("Template {} not found in available templates", templateName);
                        continue;
                    }

                    // 排除已存在的设备
                    if (existingDeviceTemplateNames.contains(templateName.toLowerCase())) {
                        log.debug("Template {} already exists on board, skipping", templateName);
                        continue;
                    }

                    // 避免重复推荐
                    if (addedTemplates.contains(templateName.toLowerCase())) {
                        continue;
                    }

                    Map<String, Object> recommendation = new LinkedHashMap<>();
                    recommendation.put("templateName", templateName);
                    recommendation.put("description", rec.path("description").asText(""));
                    recommendation.put("reason", rec.path("reason").asText(""));
                    recommendation.put("confidence", rec.path("confidence").asDouble(0.5));

                    recommendations.add(recommendation);
                    addedTemplates.add(templateName.toLowerCase());
                    count++;
                } catch (Exception e) {
                    log.warn("Failed to parse recommendation: {}", rec);
                }
            }

            Map<String, Object> result = new LinkedHashMap<>();
            if (recommendations.isEmpty()) {
                result.put("message", "No suitable devices found for your board.");
            } else {
                result.put("message", String.format("Found %d recommended devices for your board.", recommendations.size()));
            }
            result.put("recommendations", recommendations);

            return objectMapper.writeValueAsString(result);

        } catch (Exception e) {
            log.error("Failed to parse AI response", e);
            return "{\"message\":\"Failed to parse recommendations\",\"recommendations\":[]}";
        }
    }
}
