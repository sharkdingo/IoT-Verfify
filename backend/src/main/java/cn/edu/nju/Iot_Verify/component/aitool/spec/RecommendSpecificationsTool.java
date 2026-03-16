package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.DeviceInfoHelper;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
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
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * 智能规约推荐工具
 * 根据用户画布中现有的设备、规则和规约，从系统可用规约模板中推荐最合适的规约来完善整个物联网系统
 */
@Slf4j
@Component
public class RecommendSpecificationsTool extends AbstractAiTool {

    private final DeviceInfoHelper deviceInfoHelper;
    private final BoardStorageService boardStorageService;
    private final ArkAiClient arkAiClient;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)规约推荐助手。你的任务是分析用户面板中现有的设备、规则和规约，
从系统可用规约模板中推荐最合适的规约来完善整个物联网系统的安全性和可靠性验证。

## 输入信息
- 用户画布中现有的设备列表（包含每个设备的变量和可用的工作状态）
- 用户画布中现有的自动化规则
- 用户画布中现有的规约列表

## 设备属性结构说明（非常重要！）
每个设备的信息结构如下：
- **nodeId**: 设备节点ID（如 "AC", "ts"）
- **label**: 设备显示名称
- **templateName**: 设备模板名称
- **currentState**: 设备当前状态值
- **variables**: 设备的内部变量列表，每个变量包含：
  - name: 变量名称（如 "temperature", "humidity", "contact"）
  - values: 可选值列表（如 ["open", "closed"]）
  - range: 数值范围（如 "0..100"）
- **states**: 设备的工作状态可能值列表（如 ["auto", "cool", "dry", "off", "heat", "fanOnly"]）

## 重要约束：如何正确引用设备属性
1. **引用变量**：使用 variables 中的变量名作为 key，如：
   - targetType: "variable", key: "temperature", relation: ">=", value: 25
   - targetType: "variable", key: "humidity", relation: ">=", value: 70
   - targetType: "variable", key: "contact", relation: "=", value: "open"

2. **引用工作状态**：使用 states 列表中的值作为 key 和 value，如：
   - 如果要检查空调是否开启，应该用：
     targetType: "variable", key: "thermostatMode", relation: "!=", value: "off"
   - 而不是用 "currentState"，因为 currentState 不是有效的属性名

3. **禁止使用 currentState 作为 key**，因为它不是设备模板中定义的属性名

4. 确保 targetType 和 key 的组合在设备的 variables 或 states 中确实存在

## 输出要求
请分析现有设备和规则的功能，推荐可以验证系统正确性的规约，返回符合以下JSON格式的推荐：

```json
{
  "recommendations": [
    {
      "description": "用自然语言描述这条规约的作用",
      "priority": "high|medium|low",
      "confidence": 0.0-1.0,
      "templateId": "规约模板ID（可选）",
      "templateLabel": "规约模板标签（可选）",
      "aConditions": [
        {
          "deviceId": "设备节点ID",
          "deviceLabel": "设备名称",
          "targetType": "variable|api|trust|privacy",
          "key": "变量名称（必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ],
      "ifConditions": [
        {
          "deviceId": "设备节点ID",
          "deviceLabel": "设备名称",
          "targetType": "variable|api|trust|privacy",
          "key": "变量名称（必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ],
      "thenConditions": [
        {
          "deviceId": "设备节点ID",
          "deviceLabel": "设备名称",
          "targetType": "variable|api|trust|privacy",
          "key": "变量名称（必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ]
    }
  ]
}
```

注意：不要使用 targetType: "state"，应该使用 "variable"。key 必须是设备 variables 列表中定义的变量名，或者参考设备的 states 列表来理解可用的状态值。

## 规约模板类型
1. **always (AG)**: 总是满足 - "如果条件A满足，则状态B必须始终保持"
2. **eventually (EF)**: 最终满足 - "条件A满足后，最终状态B会达成"
3. **never (AG !)**: 永不发生 - "状态A永远不应该发生"
4. **immediate (A)**: 立即响应 - "当条件A满足时，立即执行动作B"
5. **response (A->)**: 响应 - "当条件A满足后，动作B最终会执行"
6. **persistence (GF)**: 持续满足 - "状态A最终会持续保持"
7. **safety (AG)**: 安全 - "危险状态永远不会发生"

## 推荐策略
1. **安全类**: 燃气泄漏、烟雾检测、门窗异常等安全相关规约
2. **响应类**: 设备联动的正确性验证
3. **一致性类**: 设备状态一致性验证
4. **隐私类**: 敏感数据隐私保护验证

## 重要约束
- aConditions、ifConditions、thenConditions 中的 targetType、key 必须是该设备 variables 中实际存在的变量名
- 禁止使用 "currentState" 作为 key，它不是有效的属性名
- 确保每个推荐都有合理的置信度(confidence)
- 优先推荐置信度高、实用性强的规约
- 不要推荐与现有规约重复的规约
- 如果没有找到合适的推荐，返回空的recommendations数组
- 最多返回5个推荐
- 推荐中需要包含对设备ID和变量的准确引用
""";

    public RecommendSpecificationsTool(DeviceInfoHelper deviceInfoHelper,
                                       BoardStorageService boardStorageService,
                                       ArkAiClient arkAiClient,
                                       ObjectMapper objectMapper) {
        super(objectMapper);
        this.deviceInfoHelper = deviceInfoHelper;
        this.boardStorageService = boardStorageService;
        this.arkAiClient = arkAiClient;
    }

    @Override
    public String getName() {
        return "recommend_specifications";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("maxRecommendations", Map.of(
                "type", "integer",
                "description", "Maximum number of specification recommendations to return. Default 5."
        ));

        props.put("category", Map.of(
                "type", "string",
                "enum", List.of("all", "safety", "response", "consistency", "privacy"),
                "description", "Filter recommendations by category: all, safety, response, consistency, privacy. Default all."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Analyze current board devices, rules, and existing specifications to recommend new formal specifications using AI. " +
                                "This tool uses AI to find suitable specifications that can verify system correctness, safety, and reliability.")
                        .parameters(schema)
                        .build()
        );
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }

            int maxRecommendations = args.path("maxRecommendations").asInt(5);
            String category = args.path("category").asText("all");

            // 获取当前面板上的所有设备信息（包含模板详情）
            List<DeviceInfoHelper.DeviceInfo> devices = deviceInfoHelper.getDevicesWithTemplateInfo(userId);

            log.info("=== SPECIFICATION RECOMMENDATION DEBUG ===");
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
                        .toList();
                    log.info("  Variables: {}", varNames);
                }

                // 打印工作状态
                if (device.workingStates() != null && !device.workingStates().isEmpty()) {
                    log.info("  States: {}", device.workingStates());
                }
            }
            log.info("===========================================");

            if (devices.isEmpty()) {
                log.warn("=== SPECIFICATION RECOMMENDATION DEBUG ===");
                log.warn("No devices found on board for user {}", userId);
                log.warn("===========================================");
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No devices found on the board. Please add devices first before requesting specification recommendations.",
                        "count", 0,
                        "recommendations", Collections.emptyList()
                ));
            }

            // 获取现有规则，避免推荐与规则冲突的规约
            List<cn.edu.nju.Iot_Verify.dto.rule.RuleDto> existingRules =
                    safeList(boardStorageService.getRules(userId));

            // 获取现有规约，避免推荐重复的
            List<SpecificationDto> existingSpecs =
                    safeList(boardStorageService.getSpecs(userId));

            log.info("Generating AI-based specification recommendations for user {}: {} devices, max {} recommendations, category: {}",
                    userId, devices.size(), maxRecommendations, category);

            // 构建现有规则和规约的简要信息
            String existingRulesInfo = buildExistingRulesInfo(existingRules);
            String existingSpecsInfo = buildExistingSpecsInfo(existingSpecs);

            // 调用 Ark AI 生成智能推荐
            String aiResponse = generateRecommendationsWithAI(
                    devices,
                    existingRulesInfo,
                    existingSpecsInfo,
                    maxRecommendations,
                    category
            );

            log.info("AI Response: {}", aiResponse);

            // 解析 AI 响应并进行验证
            String result = parseAiResponse(aiResponse, devices, maxRecommendations);

            log.info("Final Result: {}", result);

            return result;

        } catch (ServiceUnavailableException e) {
            log.warn("recommend_specifications busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("recommend_specifications business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("recommend_specifications failed", e);
            return errorJson("Failed to generate specification recommendations.", "INTERNAL_ERROR", 500);
        }
    }

    /**
     * 调用 Ark AI 生成智能推荐
     */
    private String generateRecommendationsWithAI(
            List<DeviceInfoHelper.DeviceInfo> devices,
            String existingRulesInfo,
            String existingSpecsInfo,
            int maxRecommendations,
            String category) {

        String deviceInfoJson = buildDeviceInfoJson(devices);
        String userPrompt = buildUserPrompt(deviceInfoJson, existingRulesInfo, existingSpecsInfo, maxRecommendations, category);

        List<ChatMessage> messages = new ArrayList<>();
        messages.add(ChatMessage.builder().role(ChatMessageRole.SYSTEM).content(SYSTEM_PROMPT).build());
        messages.add(ChatMessage.builder().role(ChatMessageRole.USER).content(userPrompt).build());

        ChatCompletionRequest request = ChatCompletionRequest.builder()
                .model(arkAiClient.getModelId())
                .messages(messages)
                .temperature(0.7)
                .maxTokens(4000)
                .build();

        ChatCompletionResult result;
        try {
            log.info("Calling Ark AI for specification recommendations...");
            result = arkAiClient.getArkService().createChatCompletion(request);
        } catch (Exception e) {
            log.error("Failed to call Ark AI for specification recommendations", e);
            throw ServiceUnavailableException.aiService();
        }

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
    }

    /**
     * 构建用户提示词
     */
    private String buildUserPrompt(String deviceInfoJson, String existingRulesInfo, String existingSpecsInfo,
                                   int maxRecommendations, String category) {
        StringBuilder prompt = new StringBuilder();
        prompt.append("请根据以下设备信息生成智能规约推荐。\n\n");

        prompt.append("## 设备列表\n");
        prompt.append(deviceInfoJson);
        prompt.append("\n\n");

        if (existingRulesInfo != null && !existingRulesInfo.isEmpty()) {
            prompt.append("## 现有规则\n");
            prompt.append(existingRulesInfo);
            prompt.append("\n\n");
        }

        if (existingSpecsInfo != null && !existingSpecsInfo.isEmpty()) {
            prompt.append("## 现有规约（避免重复推荐）\n");
            prompt.append(existingSpecsInfo);
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

                // 提取可用的变量
                List<Map<String, Object>> variables = new ArrayList<>();
                if (device.variables() != null) {
                    for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                        Map<String, Object> varMap = new LinkedHashMap<>();
                        varMap.put("name", var.name());
                        varMap.put("description", var.description());
                        if (var.values() != null && !var.values().isEmpty()) {
                            varMap.put("values", var.values());
                        }
                        if (var.lowerBound() != null && var.upperBound() != null) {
                            varMap.put("range", var.lowerBound() + ".." + var.upperBound());
                        }
                        variables.add(varMap);
                    }
                }
                deviceMap.put("variables", variables);

                // 可用的工作状态
                deviceMap.put("states", device.workingStates() != null ? device.workingStates() : Collections.emptyList());

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
                ruleInfo.put("id", rule.getId());
                if (rule.getConditions() != null && !rule.getConditions().isEmpty()) {
                    var cond = rule.getConditions().get(0);
                    ruleInfo.put("triggerDevice", cond.getDeviceName());
                    ruleInfo.put("triggerAttribute", cond.getAttribute());
                    ruleInfo.put("triggerValue", cond.getValue());
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
     * 构建现有规约的简要信息
     */
    private String buildExistingSpecsInfo(List<SpecificationDto> existingSpecs) {
        if (existingSpecs == null || existingSpecs.isEmpty()) {
            return "无现有规约";
        }

        try {
            List<Map<String, Object>> specsInfo = new ArrayList<>();
            for (SpecificationDto spec : existingSpecs) {
                Map<String, Object> specInfo = new LinkedHashMap<>();
                specInfo.put("id", spec.getId());
                specInfo.put("templateLabel", spec.getTemplateLabel());

                // 简化条件信息
                List<String> condSummary = new ArrayList<>();
                if (spec.getAConditions() != null) {
                    for (SpecConditionDto cond : spec.getAConditions()) {
                        condSummary.add("A:" + cond.getDeviceId() + "." + cond.getKey());
                    }
                }
                if (spec.getIfConditions() != null) {
                    for (SpecConditionDto cond : spec.getIfConditions()) {
                        condSummary.add("IF:" + cond.getDeviceId() + "." + cond.getKey());
                    }
                }
                specInfo.put("conditions", condSummary);
                specsInfo.add(specInfo);
            }
            return objectMapper.writeValueAsString(specsInfo);
        } catch (Exception e) {
            log.warn("Failed to build existing specs info", e);
            return "无现有规约";
        }
    }

    /**
     * 解析 AI 响应并验证设备属性
     */
    @SuppressWarnings("unchecked")
    private String parseAiResponse(String aiResponse, List<DeviceInfoHelper.DeviceInfo> devices, int maxRecommendations) {
        try {
            // 清理 AI 返回的内容，去除 Markdown 代码块标记
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

            // 构建设备能力映射，用于验证
            Map<String, DeviceInfoHelper.DeviceInfo> deviceMap = new HashMap<>();
            Map<String, DeviceInfoHelper.DeviceInfo> deviceLabelMap = new HashMap<>();
            for (DeviceInfoHelper.DeviceInfo device : devices) {
                deviceMap.put(device.nodeId(), device);
                deviceLabelMap.put(device.label(), device);
            }

            // 尝试解析 AI 返回的 JSON
            JsonNode root = objectMapper.readTree(cleanedResponse);

            JsonNode recommendationsNode = root.path("recommendations");
            if (recommendationsNode.isMissingNode() || !recommendationsNode.isArray()) {
                recommendationsNode = root;
            }

            List<Map<String, Object>> recommendations = new ArrayList<>();
            int count = 0;

            for (JsonNode rec : recommendationsNode) {
                if (count >= maxRecommendations) break;

                try {
                    Map<String, Object> recommendation = objectMapper.convertValue(rec, Map.class);

                    // 验证并过滤推荐
                    if (isValidRecommendation(recommendation, deviceMap, deviceLabelMap)) {
                        recommendations.add(recommendation);
                        count++;
                    } else {
                        log.info("Filtered out invalid recommendation: {}", recommendation.get("description"));
                    }
                } catch (Exception e) {
                    log.warn("Failed to parse recommendation: {}", rec);
                }
            }

            Map<String, Object> result = new LinkedHashMap<>();
            if (recommendations.isEmpty()) {
                result.put("message", "No valid specifications found for your board.");
            } else {
                result.put("message", String.format("Found %d validated specification recommendations based on your current devices.",
                        recommendations.size()));
            }
            result.put("count", recommendations.size());
            result.put("recommendations", recommendations);

            return objectMapper.writeValueAsString(result);

        } catch (Exception e) {
            log.error("Failed to parse AI response", e);
            try {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "Failed to parse AI recommendations. Please try again.",
                        "count", 0,
                        "recommendations", Collections.emptyList()
                ));
            } catch (Exception ex) {
                return "{\"message\":\"Failed to parse AI recommendations\",\"count\":0,\"recommendations\":[]}";
            }
        }
    }

    /**
     * 验证推荐是否使用设备实际存在的属性
     */
    @SuppressWarnings("unchecked")
    private boolean isValidRecommendation(Map<String, Object> recommendation,
            Map<String, DeviceInfoHelper.DeviceInfo> deviceMap,
            Map<String, DeviceInfoHelper.DeviceInfo> deviceLabelMap) {

        // 验证所有条件列表中的设备属性
        String[] conditionTypes = {"aConditions", "ifConditions", "thenConditions"};

        for (String conditionType : conditionTypes) {
            List<Map<String, Object>> conditions = (List<Map<String, Object>>) recommendation.get(conditionType);
            if (conditions == null || conditions.isEmpty()) {
                continue;
            }

            for (Map<String, Object> condition : conditions) {
                String deviceId = (String) condition.get("deviceId");
                String deviceLabel = (String) condition.get("deviceLabel");
                String targetType = (String) condition.get("targetType");
                String key = (String) condition.get("key");

                if (deviceId == null && deviceLabel == null || targetType == null || key == null) {
                    return false;
                }

                // 优先通过 deviceId（nodeId）查找，再通过 deviceLabel 查找
                DeviceInfoHelper.DeviceInfo device = deviceId != null ? deviceMap.get(deviceId) : null;
                if (device == null && deviceLabel != null) {
                    device = deviceLabelMap.get(deviceLabel);
                }
                if (device == null) {
                    log.info("Device {} (label: {}) not found in board. Available devices: {}", deviceId, deviceLabel, deviceMap.keySet());
                    return false;
                }

                // 特殊处理：如果 key 是 "currentState"，尝试映射到实际的状态变量
                String actualKey = key;
                if ("currentState".equalsIgnoreCase(key)) {
                    // currentState 不是一个有效的属性名，检查是否应该使用 thermostatMode 或类似的状态变量
                    // 先尝试查找是否有 thermostatMode 等常见状态变量
                    actualKey = mapCurrentStateToVariable(device);
                    if (actualKey == null) {
                        log.info("Attribute currentState (type: {}) not found in device {}. Variables: {}, WorkingStates: {}",
                                targetType, deviceId, device.variables(), device.workingStates());
                        return false;
                    }
                    log.info("Mapped currentState to actual variable: {} for device {}", actualKey, deviceId);
                }

                // 根据 targetType 验证属性是否存在
                boolean attrExists = false;
                String targetTypeLower = targetType.toLowerCase();
                // 安全地获取 value，支持数字和字符串类型
                Object valueObj = condition.get("value");
                String value = valueObj != null ? String.valueOf(valueObj) : null;

                if ("state".equals(targetTypeLower)) {
                    // 对于 state 类型，key 应该是 "currentState" 或类似的概念
                    // value 应该是有效的 workingState 值
                    // 允许 key 为 "currentState" 或空，只要 value 是有效的 workingState 即可
                    if ("currentState".equalsIgnoreCase(key) || key == null || key.isEmpty()) {
                        // 验证 value 是否是有效的 workingState
                        if (device.workingStates() != null && value != null) {
                            String valueStr = String.valueOf(value);
                            for (String state : device.workingStates()) {
                                if (state.equalsIgnoreCase(valueStr)) {
                                    attrExists = true;
                                    break;
                                }
                            }
                        }
                        // 如果没有 workingStates 但有 variables，也接受（可能是其他类型的设备）
                        if (!attrExists && device.variables() != null && !device.variables().isEmpty()) {
                            attrExists = true;
                        }
                    } else {
                        // 如果 key 不是 currentState，也检查 key 是否在 workingStates 中
                        if (device.workingStates() != null) {
                            for (String state : device.workingStates()) {
                                if (state.equalsIgnoreCase(key)) {
                                    attrExists = true;
                                    break;
                                }
                            }
                        }
                    }
                } else if ("variable".equals(targetTypeLower)) {
                    // 首先检查 variables
                    if (device.variables() != null && !device.variables().isEmpty()) {
                        for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                            if (var.name() != null && var.name().equalsIgnoreCase(actualKey)) {
                                attrExists = true;
                                break;
                            }
                        }
                    }

                    // 如果设备没有 variables（像 AC 这种），则检查 workingStates
                    // 当 AI 使用 variable 类型但设备实际用 workingStates 表示状态时
                    // 应该检查 value 是否是有效的 workingState
                    if (!attrExists && device.workingStates() != null && !device.workingStates().isEmpty()) {
                        String valueStr = String.valueOf(value);
                        for (String state : device.workingStates()) {
                            if (state.equalsIgnoreCase(valueStr)) {
                                attrExists = true;
                                break;
                            }
                        }
                    }
                } else if ("api".equals(targetTypeLower)) {
                    // API 暂时不验证
                    attrExists = true;
                } else if ("trust".equals(targetTypeLower) || "privacy".equals(targetTypeLower)) {
                    // trust/privacy 检查变量
                    if (device.variables() != null) {
                        for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                            if (var.name() != null && var.name().equalsIgnoreCase(actualKey)) {
                                attrExists = true;
                                break;
                            }
                        }
                    }
                }

                if (!attrExists) {
                    log.info("Attribute {} (type: {}) not found in device {}. Variables: {}, WorkingStates: {}",
                            key, targetType, deviceId, device.variables(), device.workingStates());
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * 尝试将 currentState 映射到设备实际的状态变量
     * 常见的空调状态变量有：thermostatMode, currentMode, mode, state 等
     */
    private String mapCurrentStateToVariable(DeviceInfoHelper.DeviceInfo device) {
        if (device.variables() == null) {
            return null;
        }

        // 常见的状态变量名列表，按优先级排序
        String[] commonStateVars = {"thermostatMode", "currentMode", "mode", "state", "currentState", "powerState"};

        for (String varName : commonStateVars) {
            for (DeviceInfoHelper.VariableInfo var : device.variables()) {
                if (var.name() != null && var.name().equalsIgnoreCase(varName)) {
                    return var.name();
                }
            }
        }

        // 如果没找到常见变量，返回第一个变量
        if (!device.variables().isEmpty()) {
            return device.variables().get(0).name();
        }

        return null;
    }
}
