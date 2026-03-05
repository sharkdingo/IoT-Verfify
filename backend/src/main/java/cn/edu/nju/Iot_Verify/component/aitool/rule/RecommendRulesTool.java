package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionResult;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.stream.Collectors;

/**
 * 智能规则推荐工具
 * 基于 Ark AI 实现智能规则推荐，根据当前面板上的设备信息生成自动化规则建议
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class RecommendRulesTool implements AiTool {

    private final DeviceInfoHelper deviceInfoHelper;
    private final BoardStorageService boardStorageService;
    private final ArkAiClient arkAiClient;
    private final ObjectMapper objectMapper;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)自动化规则推荐助手。你的任务是根据用户面板上的设备信息，
分析设备之间的联动可能性，并生成有价值的自动化规则建议。

## 输入信息
- 用户面板上的所有设备列表（包括设备名称、模板类型、可用变量、可用API等）
- 现有的自动化规则（用于避免重复推荐）

## 输出要求
请分析设备之间的联动场景，生成符合以下JSON格式的规则推荐：

```json
{
  "recommendations": [
    {
      "category": "security|energy_saving|comfort|automation",
      "description": "用自然语言描述这条规则",
      "priority": "high|medium|low",
      "confidence": 0.0-1.0,
      "requiresUserInput": true|false,
      "conditions": [
        {
          "deviceName": "设备节点ID",
          "attribute": "触发属性（必须是该设备实际存在的变量）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "触发值"
        }
      ],
      "command": {
        "deviceName": "目标设备节点ID",
        "action": "动作名称（必须是该设备实际存在的API）",
        "contentDevice": null或"内容设备节点ID",
        "content": null或"内容值"
      }
    }
  ]
}
```

## 推荐策略
1. **安全类**: 燃气泄漏、烟雾检测、门窗异常等安全相关联动
2. **节能类**: 无人时自动关闭灯光、设备等
3. **舒适类**: 根据温度、湿度、光照自动调节环境
4. **自动化类**: 人体感应、门磁触发等日常自动化场景

## 重要约束
- conditions中的attribute必须是该设备实际存在的变量名
- command中的action必须是该设备实际存在的API名称
- 确保每个推荐都有合理的置信度(confidence)
- 优先推荐置信度高、实用性强的规则
- 不要推荐与现有规则重复的规则
- 如果设备信息不足，返回空的recommendations数组
""";

    @Override
    public String getName() {
        return "recommend_rules";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("maxRecommendations", Map.of(
                "type", "integer",
                "description", "Maximum number of rule recommendations to return. Default 5."
        ));

        props.put("category", Map.of(
                "type", "string",
                "enum", List.of("all", "security", "energy_saving", "comfort", "automation"),
                "description", "Filter recommendations by category: all, security, energy_saving, comfort, automation. Default all."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Analyze current board devices and recommend intelligent automation rules using AI. " +
                                "This tool uses AI to analyze each device's capabilities (APIs, variables, states) and suggests " +
                                "meaningful rules based on device联动, security, energy saving, or comfort scenarios.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in", "UNAUTHORIZED", 401);
            }

            JsonNode args;
            try {
                args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            } catch (Exception parseEx) {
                return errorJson("Invalid JSON arguments.", "VALIDATION_ERROR", 400);
            }

            int maxRecommendations = args.path("maxRecommendations").asInt(5);
            String category = args.path("category").asText("all");

            // 获取当前面板上的所有设备信息（包含模板详情）
            List<DeviceInfoHelper.DeviceInfo> devices = deviceInfoHelper.getDevicesWithTemplateInfo(userId);

            log.info("=== RULE RECOMMENDATION DEBUG ===");
            log.info("User ID: {}", userId);
            log.info("Devices found: {}", devices.size());
            
            // 打印每个设备的详细信息
            for (DeviceInfoHelper.DeviceInfo device : devices) {
                log.info("Device: nodeId={}, label={}, templateName={}", 
                    device.nodeId(), device.label(), device.templateName());
                
                // 打印变量
                if (device.variables() != null && !device.variables().isEmpty()) {
                    List<String> varNames = device.variables().stream()
                        .map(DeviceInfoHelper.VariableInfo::name)
                        .collect(Collectors.toList());
                    log.info("  Variables: {}", varNames);
                }
                
                // 打印 APIs
                if (device.apis() != null && !device.apis().isEmpty()) {
                    List<String> apiNames = device.apis().stream()
                        .map(DeviceInfoHelper.ApiInfo::name)
                        .collect(Collectors.toList());
                    log.info("  APIs: {}", apiNames);
                }
            }
            log.info("===================================");

            if (devices.isEmpty()) {
                log.warn("=== RULE RECOMMENDATION DEBUG ===");
                log.warn("No devices found on board for user {}", userId);
                log.warn("===================================");
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No devices found on the board. Please add devices first before requesting rule recommendations.",
                        "count", 0,
                        "recommendations", Collections.emptyList()
                ));
            }

            // 获取现有规则，避免推荐重复的
            List<cn.edu.nju.Iot_Verify.dto.rule.RuleDto> existingRules = 
                    safeList(boardStorageService.getRules(userId));

            log.info("Generating AI-based rule recommendations for user {}: {} devices, max {} recommendations, category: {}",
                    userId, devices.size(), maxRecommendations, category);

            // 构建详细的设备信息字符串供 AI 分析
            String deviceInfoJson = buildDeviceInfoJson(devices);
            
            // 构建现有规则的简要信息
            String existingRulesInfo = buildExistingRulesInfo(existingRules);

            // 调用 Ark AI 生成智能推荐
            String aiResponse = generateRecommendationsWithAI(
                    devices,
                    existingRulesInfo, 
                    maxRecommendations, 
                    category
            );

            log.info("AI Response: {}", aiResponse);

            // 解析 AI 响应并进行验证
            String result = parseAiResponse(aiResponse, devices, maxRecommendations);
            
            log.info("Final Result: {}", result);
            
            return result;

        } catch (ServiceUnavailableException e) {
            log.warn("recommend_rules busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("recommend_rules business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("recommend_rules failed", e);
            return errorJson("Failed to generate rule recommendations.", "INTERNAL_ERROR", 500);
        }
    }

    /**
     * 调用 Ark AI 生成智能推荐
     */
    private String generateRecommendationsWithAI(
            List<DeviceInfoHelper.DeviceInfo> devices, 
            String existingRulesInfo, 
            int maxRecommendations,
            String category) {

        String deviceInfoJson = buildDeviceInfoJson(devices);
        String userPrompt = buildUserPrompt(deviceInfoJson, existingRulesInfo, maxRecommendations, category);

        List<ChatMessage> messages = new ArrayList<>();
        messages.add(ChatMessage.builder().role(ChatMessageRole.SYSTEM).content(SYSTEM_PROMPT).build());
        messages.add(ChatMessage.builder().role(ChatMessageRole.USER).content(userPrompt).build());

        ChatCompletionRequest request = ChatCompletionRequest.builder()
                .model(arkAiClient.getModelId())
                .messages(messages)
                .temperature(0.7)
                .maxTokens(4000)
                .build();

        try {
            log.info("Calling Ark AI for recommendations...");
            ChatCompletionResult result = arkAiClient.getArkService().createChatCompletion(request);
            if (result.getChoices() == null || result.getChoices().isEmpty()) {
                log.warn("AI returned empty choices");
                return "{\"recommendations\": []}";
            }
            
            ChatMessage responseMsg = result.getChoices().get(0).getMessage();
            if (responseMsg == null || responseMsg.getContent() == null) {
                log.warn("AI returned null message content");
                return "{\"recommendations\": []}";
            }
            
            String content = responseMsg.getContent().toString();
            log.info("AI response content length: {}", content.length());
            return content;
        } catch (Exception e) {
            log.error("Failed to call Ark AI for recommendations", e);
            throw new RuntimeException("AI service unavailable: " + e.getMessage());
        }
    }

    /**
     * 构建用户提示词
     */
    private String buildUserPrompt(String deviceInfoJson, String existingRulesInfo, int maxRecommendations, String category) {
        StringBuilder prompt = new StringBuilder();
        prompt.append("请根据以下设备信息生成智能自动化规则推荐。\n\n");
        
        prompt.append("## 设备列表\n");
        prompt.append(deviceInfoJson);
        prompt.append("\n\n");
        
        if (existingRulesInfo != null && !existingRulesInfo.isEmpty()) {
            prompt.append("## 现有规则（避免重复推荐）\n");
            prompt.append(existingRulesInfo);
            prompt.append("\n\n");
        }
        
        prompt.append("## 推荐要求\n");
        prompt.append("- 最大推荐数量: ").append(maxRecommendations).append("\n");
        
        if (!"all".equals(category)) {
            prompt.append("- 分类筛选: ").append(category).append("\n");
        }
        
        prompt.append("\n请直接返回JSON格式的推荐结果，不要包含其他文字。");
        
        return prompt.toString();
    }

    /**
     * 构建设备详细信息 JSON，用于 AI 分析
     */
    private String buildDeviceInfoJson(List<DeviceInfoHelper.DeviceInfo> devices) {
        try {
            List<Map<String, Object>> deviceList = new ArrayList<>();

            for (DeviceInfoHelper.DeviceInfo device : devices) {
                Map<String, Object> deviceMap = new LinkedHashMap<>();
                deviceMap.put("nodeId", device.nodeId());
                deviceMap.put("label", device.label());
                deviceMap.put("templateName", device.templateName());
                deviceMap.put("currentState", device.currentState());

                // 提取可用的触发属性（内部变量）
                List<String> triggerableAttributes = new ArrayList<>();
                if (device.variables() != null) {
                    for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                        triggerableAttributes.add(var.name());
                    }
                }
                deviceMap.put("triggerableAttributes", triggerableAttributes);

                // 提取可用的 API（可执行的动作为"控制"）
                List<Map<String, Object>> actionableApis = new ArrayList<>();
                if (device.apis() != null) {
                    for (DeviceInfoHelper.ApiInfo api : device.apis()) {
                        Map<String, Object> apiMap = new LinkedHashMap<>();
                        apiMap.put("name", api.name());
                        apiMap.put("description", api.description());
                        actionableApis.add(apiMap);
                    }
                }
                deviceMap.put("actionableApis", actionableApis);

                // 可用的工作状态
                deviceMap.put("workingStates", device.workingStates() != null ? device.workingStates() : Collections.emptyList());

                deviceList.add(deviceMap);
            }

            return objectMapper.writeValueAsString(deviceList);
        } catch (Exception e) {
            log.error("Failed to build device info JSON", e);
            return "[]";
        }
    }

    /**
     * 构建现有规则的简要信息
     */
    private String buildExistingRulesInfo(List<cn.edu.nju.Iot_Verify.dto.rule.RuleDto> existingRules) {
        if (existingRules == null || existingRules.isEmpty()) {
            return "无现有规则";
        }

        try {
            List<Map<String, Object>> rulesInfo = new ArrayList<>();
            for (var rule : existingRules) {
                Map<String, Object> ruleInfo = new LinkedHashMap<>();
                if (rule.getConditions() != null && !rule.getConditions().isEmpty()) {
                    var cond = rule.getConditions().get(0);
                    ruleInfo.put("triggerDevice", cond.getDeviceName());
                    ruleInfo.put("triggerAttribute", cond.getAttribute());
                }
                if (rule.getCommand() != null) {
                    ruleInfo.put("actionDevice", rule.getCommand().getDeviceName());
                    ruleInfo.put("action", rule.getCommand().getAction());
                }
                rulesInfo.add(ruleInfo);
            }
            return objectMapper.writeValueAsString(rulesInfo);
        } catch (Exception e) {
            log.warn("Failed to build existing rules info", e);
            return "无现有规则";
        }
    }

    /**
     * 解析 AI 响应并验证设备变量和API
     */
    @SuppressWarnings("unchecked")
    private String parseAiResponse(String aiResponse, List<DeviceInfoHelper.DeviceInfo> devices, int maxRecommendations) {
        try {
            // 清理 AI 返回的内容，去除 Markdown 代码块标记
            String cleanedResponse = aiResponse.trim();
            if (cleanedResponse.startsWith("```")) {
                // 去除开头的 ```json 或 ```
                int firstNewline = cleanedResponse.indexOf('\n');
                if (firstNewline > 0) {
                    cleanedResponse = cleanedResponse.substring(firstNewline).trim();
                }
            }
            if (cleanedResponse.endsWith("```")) {
                cleanedResponse = cleanedResponse.substring(0, cleanedResponse.lastIndexOf("```")).trim();
            }
            
            // 构建设备能力映射，用于验证
            Map<String, DeviceInfoHelper.DeviceInfo> deviceMap = new HashMap<>();
            for (DeviceInfoHelper.DeviceInfo device : devices) {
                deviceMap.put(device.nodeId(), device);
            }
            
            // 尝试解析 AI 返回的 JSON
            JsonNode root = objectMapper.readTree(cleanedResponse);
            
            JsonNode recommendationsNode = root.path("recommendations");
            if (recommendationsNode.isMissingNode() || !recommendationsNode.isArray()) {
                // 如果AI没有返回正确格式，尝试直接使用整个响应
                recommendationsNode = root;
            }
            
            List<Map<String, Object>> recommendations = new ArrayList<>();
            int count = 0;
            
            for (JsonNode rec : recommendationsNode) {
                if (count >= maxRecommendations) break;
                
                try {
                    Map<String, Object> recommendation = objectMapper.convertValue(rec, Map.class);
                    
                    // 验证并过滤推荐
                    if (isValidRecommendation(recommendation, deviceMap)) {
                        recommendations.add(recommendation);
                        count++;
                    } else {
                        log.debug("Filtered out invalid recommendation: {}", recommendation);
                    }
                } catch (Exception e) {
                    log.warn("Failed to parse recommendation: {}", rec);
                }
            }

            Map<String, Object> result = new LinkedHashMap<>();
            if (recommendations.isEmpty()) {
                result.put("message", "No valid recommendations available. AI suggestions did not match actual device capabilities.");
            } else {
                result.put("message", String.format("Found %d validated rule recommendations based on your current devices.", 
                        recommendations.size()));
            }
            result.put("count", recommendations.size());
            result.put("recommendations", recommendations);

            return objectMapper.writeValueAsString(result);
            
        } catch (Exception e) {
            log.error("Failed to parse AI response", e);
            // 返回空结果而不是错误
            try {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "Failed to parse AI recommendations. Please try again.",
                        "count", 0,
                        "recommendations", Collections.emptyList()
                ));
            } catch (Exception ex) {
                // 如果序列化也失败，返回最简结果
                return "{\"message\":\"Failed to parse AI recommendations\",\"count\":0,\"recommendations\":[]}";
            }
        }
    }

    /**
     * 验证推荐是否使用设备实际存在的变量和API
     */
    @SuppressWarnings("unchecked")
    private boolean isValidRecommendation(Map<String, Object> recommendation, 
            Map<String, DeviceInfoHelper.DeviceInfo> deviceMap) {
        
        if (!recommendation.containsKey("conditions") || !recommendation.containsKey("command")) {
            return false;
        }
        
        List<Map<String, Object>> conditions = (List<Map<String, Object>>) recommendation.get("conditions");
        Map<String, Object> command = (Map<String, Object>) recommendation.get("command");
        
        if (conditions == null || conditions.isEmpty() || command == null) {
            return false;
        }
        
        // 验证每个触发条件
        for (Map<String, Object> condition : conditions) {
            String deviceName = (String) condition.get("deviceName");
            String attribute = (String) condition.get("attribute");
            
            if (deviceName == null || attribute == null) {
                return false;
            }
            
            // 检查设备是否存在
            DeviceInfoHelper.DeviceInfo device = deviceMap.get(deviceName);
            if (device == null) {
                log.debug("Device {} not found in board", deviceName);
                return false;
            }
            
            // 检查属性是否存在于设备的变量中
            boolean attrExists = false;
            if (device.variables() != null) {
                for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                    if (var.name() != null && var.name().equalsIgnoreCase(attribute)) {
                        attrExists = true;
                        break;
                    }
                }
            }
            
            if (!attrExists) {
                log.debug("Attribute {} not found in device {} variables", attribute, deviceName);
                return false;
            }
        }
        
        // 验证执行动作
        String actionDeviceName = (String) command.get("deviceName");
        String action = (String) command.get("action");
        
        if (actionDeviceName == null || action == null) {
            return false;
        }
        
        DeviceInfoHelper.DeviceInfo actionDevice = deviceMap.get(actionDeviceName);
        if (actionDevice == null) {
            log.debug("Action device {} not found in board", actionDeviceName);
            return false;
        }
        
        // 检查动作是否存在于设备的API中
        boolean actionExists = false;
        if (actionDevice.apis() != null) {
            for (DeviceInfoHelper.ApiInfo api : actionDevice.apis()) {
                if (api.name() != null && api.name().equalsIgnoreCase(action)) {
                    actionExists = true;
                    break;
                }
            }
        }
        
        if (!actionExists) {
            log.debug("Action {} not found in device {} APIs", action, actionDeviceName);
            return false;
        }
        
        return true;
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? Collections.emptyList() : list;
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }
}
