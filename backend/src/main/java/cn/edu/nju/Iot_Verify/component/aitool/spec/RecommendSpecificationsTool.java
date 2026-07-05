package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
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
    private final PromptCompletionService promptCompletionService;

    private static final double TEMPERATURE = 0.7;
    private static final int MAX_TOKENS = 4000;
    private static final Set<String> ALLOWED_TEMPLATE_IDS = Set.of("1", "2", "3", "4", "5", "6", "7");
    private static final Set<String> ALLOWED_RELATIONS = Set.of("=", "!=", ">", ">=", "<", "<=", "in", "not_in", "not in");

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)规约推荐助手。你的任务是分析用户面板中现有的设备、规则和规约，
从系统可用规约模板中推荐最合适的规约来完善整个物联网系统的安全性和可靠性验证。

## 输入信息
- 用户画布中现有的设备列表（包含每个设备的变量和可用的工作状态）
- 用户画布中现有的自动化规则
- 用户画布中现有的规约列表

## 设备属性结构说明（非常重要！）
每个设备的信息结构如下：
- **label**: 设备显示名称，也是推荐结果中 deviceId 必须使用的设备引用值
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

2. **引用工作状态**：使用 targetType: "state"。key 固定使用 "state"，value 使用 states 列表中的状态值，如：
   - 如果要检查空调是否开启，应该用：
     targetType: "state", key: "state", relation: "!=", value: "off"
   - 如果设备模板暴露了更具体的状态变量，也可以用 targetType: "variable" 引用该变量

3. **禁止使用 currentState 作为 key**，因为它不是设备模板中定义的属性名

4. 确保 targetType 和 key/value 的组合在设备的 variables、APIs 或 states 中确实存在

## 输出要求
请分析现有设备和规则的功能，推荐可以验证系统正确性的规约，返回符合以下JSON格式的推荐：

```json
{
  "recommendations": [
    {
      "description": "用自然语言描述这条规约的作用",
      "priority": "high|medium|low",
      "confidence": 0.0-1.0,
      "templateId": "规约模板ID（必填，只能是 1|2|3|4|5|6|7）",
      "templateLabel": "规约模板标签（可选）",
      "aConditions": [
        {
          "deviceId": "设备 label（必须来自设备列表的 label 字段）",
          "deviceLabel": "设备 label",
          "targetType": "state|variable|api|trust|privacy",
          "key": "状态/变量/API名称（state 固定使用 state；variable 必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ],
      "ifConditions": [
        {
          "deviceId": "设备 label（必须来自设备列表的 label 字段）",
          "deviceLabel": "设备 label",
          "targetType": "state|variable|api|trust|privacy",
          "key": "状态/变量/API名称（state 固定使用 state；variable 必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ],
      "thenConditions": [
        {
          "deviceId": "设备 label（必须来自设备列表的 label 字段）",
          "deviceLabel": "设备 label",
          "targetType": "state|variable|api|trust|privacy",
          "key": "状态/变量/API名称（state 固定使用 state；variable 必须是设备variables中定义的变量名）",
          "relation": "=|>|<|>=|<=|!=",
          "value": "期望值"
        }
      ]
    }
  ]
}
```

注意：不要使用 "currentState" 作为 key。工作状态优先使用 targetType: "state" 且 key 固定为 "state"，value 必须来自设备 states 列表；内部变量使用 targetType: "variable"，key 必须来自设备 variables 列表。

## 规约模板类型
1. **always (AG)**: 总是满足 - "如果条件A满足，则状态B必须始终保持"
2. **eventually (EF)**: 最终满足 - "条件A满足后，最终状态B会达成"
3. **never (AG !)**: 永不发生 - "状态A永远不应该发生"
4. **immediate (A)**: 下一状态响应 - "当条件A满足时，下一状态必须满足B（AX，紧接其后）"
5. **response (A->)**: 响应 - "当条件A满足后，动作B最终会执行"
6. **persistence (GF)**: 持续满足 - "状态A最终会持续保持"
7. **safety (AG)**: 安全 - "危险状态永远不会发生"

## 推荐策略
1. **安全类**: 燃气泄漏、烟雾检测、门窗异常等安全相关规约
2. **响应类**: 设备联动的正确性验证
3. **一致性类**: 设备状态一致性验证
4. **隐私类**: 敏感数据隐私保护验证

## 重要约束
- aConditions、ifConditions、thenConditions 中的 targetType、key/value 必须引用该设备实际存在的 states、variables 或 APIs
- 禁止使用 "currentState" 作为 key，它不是有效的属性名
- 每条推荐必须包含合法 templateId，且 templateId 必须严格枚举为 "1" 到 "7"
- 确保每个推荐都有合理的置信度(confidence)
- 优先推荐置信度高、实用性强的规约
- 不要推荐与现有规约重复的规约
- 如果没有找到合适的推荐，返回空的recommendations数组
- 最多返回5个推荐
- 推荐中需要包含对设备 label 和变量的准确引用
""";

    public RecommendSpecificationsTool(DeviceInfoHelper deviceInfoHelper,
                                       BoardStorageService boardStorageService,
                                       PromptCompletionService promptCompletionService,
                                       ObjectMapper objectMapper) {
        super(objectMapper);
        this.deviceInfoHelper = deviceInfoHelper;
        this.boardStorageService = boardStorageService;
        this.promptCompletionService = promptCompletionService;
    }

    @Override
    public String getName() {
        return "recommend_specifications";
    }

    @Override
    public LlmToolSpec getDefinition() {
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

        return LlmToolSpec.of(getName(),
                "Analyze current board devices, rules, and existing specifications to recommend new formal specifications using AI. " +
                        "This tool uses AI to find suitable specifications that can verify system correctness, safety, and reliability.",
                schema);
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

            // 调用 LLM 生成智能推荐
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
     * 调用配置的 LLM 生成智能推荐
     */
    private String generateRecommendationsWithAI(
            List<DeviceInfoHelper.DeviceInfo> devices,
            String existingRulesInfo,
            String existingSpecsInfo,
            int maxRecommendations,
            String category) {

        String deviceInfoJson = buildDeviceInfoJson(devices);
        String userPrompt = buildUserPrompt(deviceInfoJson, existingRulesInfo, existingSpecsInfo, maxRecommendations, category);

        log.info("Calling LLM for specification recommendations...");
        String content = promptCompletionService.complete(SYSTEM_PROMPT, userPrompt, TEMPERATURE, MAX_TOKENS);

        if (content == null || content.isBlank()) {
            log.warn("AI returned empty content");
            return "{\"recommendations\": []}";
        }

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
            Map<String, DeviceInfoHelper.DeviceInfo> legacyNodeMap = new HashMap<>();
            for (DeviceInfoHelper.DeviceInfo device : devices) {
                deviceMap.put(device.label(), device);
                legacyNodeMap.put(device.nodeId(), device);
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
                    if (isValidRecommendation(recommendation, deviceMap, legacyNodeMap)) {
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
            Map<String, DeviceInfoHelper.DeviceInfo> legacyNodeMap) {

        String templateId = asTrimmedString(recommendation.get("templateId"));
        if (!ALLOWED_TEMPLATE_IDS.contains(templateId)) {
            log.info("Rejecting recommendation without legal templateId: {}", recommendation.get("description"));
            return false;
        }
        recommendation.put("templateId", templateId);

        // 验证所有条件列表中的设备属性
        String[] conditionTypes = {"aConditions", "ifConditions", "thenConditions"};

        for (String conditionType : conditionTypes) {
            List<Map<String, Object>> conditions = (List<Map<String, Object>>) recommendation.get(conditionType);
            if (conditions == null || conditions.isEmpty()) {
                continue;
            }

            for (Map<String, Object> condition : conditions) {
                String deviceId = asTrimmedString(condition.get("deviceId"));
                String deviceLabel = asTrimmedString(condition.get("deviceLabel"));
                String targetType = asTrimmedString(condition.get("targetType"));
                String key = asTrimmedString(condition.get("key"));
                String relation = asTrimmedString(condition.get("relation"));
                String value = asTrimmedString(condition.get("value"));

                if ((deviceId == null && deviceLabel == null) || targetType == null || key == null) {
                    return false;
                }
                if (value == null) {
                    return false;
                }
                if (relation != null && !isAllowedRelation(relation)) {
                    return false;
                }

                DeviceInfoHelper.DeviceInfo device = resolveDevice(deviceId, deviceLabel, deviceMap, legacyNodeMap);
                if (device == null) {
                    log.info("Device {} (label: {}) not found in board. Available devices: {}", deviceId, deviceLabel, deviceMap.keySet());
                    return false;
                }
                condition.put("deviceId", device.label());
                condition.put("deviceLabel", device.label());

                String actualKey = key;
                if ("currentState".equalsIgnoreCase(key)) {
                    log.info("Rejecting currentState key for device {}. Use targetType=state with key=state and a valid state value.", deviceId);
                    return false;
                }

                // 根据 targetType 验证属性是否存在
                boolean attrExists = false;
                String targetTypeLower = targetType.toLowerCase();
                condition.put("targetType", targetTypeLower);
                condition.put("key", actualKey);
                condition.put("relation", relation != null ? relation : "=");
                condition.put("value", value);

                if ("state".equals(targetTypeLower)) {
                    attrExists = stateValueExists(device, value);
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
                    if (device.apis() != null) {
                        for (DeviceInfoHelper.ApiInfo api : device.apis()) {
                            if (api.name() != null && api.name().equalsIgnoreCase(actualKey)) {
                                attrExists = true;
                                break;
                            }
                        }
                    }
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
     * 验证状态条件的 value 是否来自设备工作状态列表。
     */
    private DeviceInfoHelper.DeviceInfo resolveDevice(String deviceId,
            String deviceLabel,
            Map<String, DeviceInfoHelper.DeviceInfo> labelMap,
            Map<String, DeviceInfoHelper.DeviceInfo> legacyNodeMap) {
        DeviceInfoHelper.DeviceInfo device = deviceId != null ? labelMap.get(deviceId) : null;
        if (device == null && deviceLabel != null) {
            device = labelMap.get(deviceLabel);
        }
        if (device == null && deviceId != null) {
            device = legacyNodeMap.get(deviceId);
        }
        if (device == null && deviceLabel != null) {
            device = legacyNodeMap.get(deviceLabel);
        }
        return device;
    }

    private boolean stateValueExists(DeviceInfoHelper.DeviceInfo device, String value) {
        if (device.workingStates() == null || value == null) {
            return false;
        }
        boolean foundCandidate = false;
        for (String candidate : value.split("[,;]")) {
            String trimmed = candidate.trim();
            if (trimmed.isEmpty() || "_".equals(trimmed)) {
                continue;
            }
            foundCandidate = true;
            boolean exists = false;
            for (String state : device.workingStates()) {
                if (state != null && state.equalsIgnoreCase(trimmed)) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                return false;
            }
        }
        return foundCandidate;
    }

    private String asTrimmedString(Object value) {
        if (value == null) {
            return null;
        }
        String text = String.valueOf(value).trim();
        return text.isEmpty() ? null : text;
    }

    private boolean isAllowedRelation(String relation) {
        return relation != null && ALLOWED_RELATIONS.contains(relation.toLowerCase(Locale.ROOT));
    }
}
