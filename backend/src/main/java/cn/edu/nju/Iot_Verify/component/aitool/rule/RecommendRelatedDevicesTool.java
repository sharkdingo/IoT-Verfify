package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.RecommendationAdjustmentItem;
import cn.edu.nju.Iot_Verify.component.aitool.RecommendationCapabilityView;
import cn.edu.nju.Iot_Verify.component.aitool.RecommendationFilterItem;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.RecommendationLimits;
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
 * 智能设备推荐工具
 * 根据用户画布中现有的所有设备，从系统可用模板中推荐最合适的设备来完善整个物联网系统
 */
@Slf4j
@Component
public class RecommendRelatedDevicesTool extends AbstractAiTool {

    private final PromptCompletionService promptCompletionService;
    private final DeviceInfoHelper deviceInfoHelper;
    private final BoardStorageService boardStorageService;

    private static final double TEMPERATURE = 0.7;
    private static final int MAX_TOKENS = 4000;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)设备推荐助手。你的任务是分析用户画布中现有的设备，
从系统可用模板中推荐最合适的设备来完善整个物联网系统。

## 输入信息
- 用户画布中现有的设备列表和当前 Environment Pool
- 系统可用的设备模板列表，每个模板包含完整 capabilities

只能根据 capabilities 中声明的域、可伪造性、自然变化、动态、Transitions、API 状态/内容能力
和内容描述判断设备是否真正能补齐场景；不要凭模板名称臆测行为。

## 输出要求
请分析现有设备的功能和布局，推荐可以增强系统功能的设备，返回符合以下JSON格式的推荐：

```json
{
  "recommendations": [
    {
      "templateName": "设备模板名称（必须是系统中存在的模板）",
      "suggestedLabel": "建议设备实例名，例如 Bedroom_Motion_Sensor",
      "intendedUse": "建议用途，例如 bedroom occupancy trigger；仅作为推荐说明，不是持久化设备字段",
      "suggestedPlacement": "建议部署区域，例如 bedroom；仅作为推荐说明，不是持久化设备字段",
      "initialState": "可选，必须来自该模板 workingStates；不确定则省略",
      "currentStateTrust": "可选，仅在 initialState 存在时使用 trusted|untrusted；表示初始状态是否来自用户信任的事件",
      "currentStatePrivacy": "可选，仅在 initialState 存在时使用 public|private；表示初始状态的数据敏感度标签",
      "initialVariables": [
        {"name": "本地变量名", "value": "初始值", "trust": "trusted|untrusted"}
      ],
      "initialPrivacies": [
        {"name": "本地变量名", "privacy": "public|private"}
      ],
      "description": "设备描述",
      "reason": "推荐理由，用自然语言描述为什么推荐这个设备"
    }
  ]
}
```

## 重要约束
- 推荐模板必须是系统中已加载的真实模板名称
- 推荐的是设备实例，不只是模板；suggestedLabel 应体现建议部署区域/用途
- 可以推荐与现有设备同模板但不同建议部署区域/用途的实例，例如 Bedroom Motion Sensor 和 Hallway Motion Sensor
- 不要推荐与现有设备完全相同建议部署区域/用途的重复实例
- intendedUse 和 suggestedPlacement 只解释推荐上下文；应用时只保存模板、suggestedLabel 和有效初始运行值，不要暗示它们会成为设备字段或形式模型输入
- initialVariables/initialPrivacies 只能使用模板中 IsInside=true 的本地变量；共享环境变量不要放进设备实例
- currentStateTrust/currentStatePrivacy 和变量 trust/privacy 仅表示实例级高级覆盖；采用模板默认标签时必须省略。
- trust 是 MEDIC 控制来源标签：多条件规则只要至少一个实际触发来源可信，目标仍可信；只有全部来源不可信时目标才不可信。它不是认证或通用数据完整性。privacy 是数据敏感性标签，不代表现实访问控制或加密
- 基于现有设备的功能缺口进行推荐
- 如果没有找到合适的推荐，返回空的recommendations数组
- 最多返回10个推荐，具体数量遵循用户请求的 maxRecommendations
""";

    public RecommendRelatedDevicesTool(PromptCompletionService promptCompletionService,
                                       ObjectMapper objectMapper,
                                       DeviceInfoHelper deviceInfoHelper,
                                       BoardStorageService boardStorageService) {
        super(objectMapper);
        this.promptCompletionService = promptCompletionService;
        this.deviceInfoHelper = deviceInfoHelper;
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "recommend_related_devices";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("maxRecommendations", Map.of(
                "type", "integer",
                "description", "Maximum number of device recommendations to return (1-10). Default 5."
        ));

        props.put("language", Map.of(
                "type", "string",
                "enum", List.of("en", "zh-CN"),
                "description", "Natural-language output locale: en or zh-CN. Default en."
        ));

        props.put("userRequirement", Map.of(
                "type", "string",
                "maxLength", RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH,
                "description", "Optional user scenario or goal that should guide the device recommendations."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, List.of());

        return LlmToolSpec.of(getName(),
                "Analyze the current user's saved board and recommend new devices from available templates. " +
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

            requireOnlyFields(args, "$", Set.of(
                    "maxRecommendations", "language", "userRequirement"));

            int maxRecommendations = intArgInRange(args, "maxRecommendations", 5, 1, 10);
            String language = languageArg(args, "language");
            String userRequirement = optionalTextArg(
                    args, "userRequirement", "", RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH);

            List<DeviceInfoHelper.DeviceInfo> devices = deviceInfoHelper.getDevicesWithTemplateInfo(userId);
            List<DeviceTemplateDto> templates = boardStorageService.getDeviceTemplates(userId);

            if (log.isDebugEnabled()) {
                log.debug("Board device recommendation request: userId={}, devices={}, templates={}, max={}",
                        userId, devices.size(), templates.size(), maxRecommendations);
            }

            if (templates.isEmpty()) {
                Map<String, Object> emptyResult = new LinkedHashMap<>();
                emptyResult.put("message", recommendationMessage(language, "noTemplates", 0));
                emptyResult.put("count", 0);
                emptyResult.put("requestedCount", maxRecommendations);
                emptyResult.put("validatedCount", 0);
                emptyResult.put("filteredCount", 0);
                emptyResult.put("filteredItems", Collections.emptyList());
                emptyResult.put("adjustedCount", 0);
                emptyResult.put("adjustedItems", Collections.emptyList());
                emptyResult.put("rawCandidateCount", 0);
                emptyResult.put("inspectedCount", 0);
                emptyResult.put("truncatedCount", 0);
                emptyResult.put("recommendations", Collections.emptyList());
                return objectMapper.writeValueAsString(emptyResult);
            }

            // 构建当前画布设备信息
            String currentDevicesInfo = buildCurrentDevicesJson(
                    devices,
                    templates,
                    safeList(boardStorageService.getEnvironmentVariables(userId)));

            // 构建可用模板信息
            String availableTemplatesInfo = buildAvailableTemplatesJson(templates);

            // 调用 AI 生成推荐
            String aiResponse = generateBoardRecommendationsWithAI(
                    currentDevicesInfo,
                    availableTemplatesInfo,
                    maxRecommendations,
                    language,
                    userRequirement
            );

            log.debug("Board device recommendation AI response length: {} chars", aiResponse.length());

            // 解析 AI 响应
            String result = parseBoardRecommendationsResponse(
                    aiResponse,
                    templates,
                    devices,
                    maxRecommendations,
                    language);

            log.debug("Board device recommendation result length: {} chars", result.length());

            return result;

        } catch (ArgValidationException e) {
            return e.getErrorResponse();
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

    private String buildCurrentDevicesJson(List<DeviceInfoHelper.DeviceInfo> devices,
                                           List<DeviceTemplateDto> templates,
                                           List<BoardEnvironmentVariableDto> environmentVariables) {
        try {
            List<Map<String, Object>> devicesList = new ArrayList<>();
            Map<String, DeviceTemplateDto> templatesByName =
                    RecommendationCapabilityView.indexTemplates(templates);
            for (DeviceInfoHelper.DeviceInfo device : devices) {
                Map<String, Object> deviceMap = new LinkedHashMap<>();
                deviceMap.put("deviceId", device.nodeId());
                deviceMap.put("label", device.label());
                deviceMap.put("templateName", device.templateName());
                deviceMap.put("currentState", device.currentState());
                deviceMap.put("currentStateTrust", device.currentStateTrust());
                deviceMap.put("currentStatePrivacy", device.currentStatePrivacy());
                deviceMap.put("initialVariables", device.instanceVariables() != null ? device.instanceVariables() : Collections.emptyList());
                deviceMap.put("initialPrivacies", device.instancePrivacies() != null ? device.instancePrivacies() : Collections.emptyList());
                DeviceTemplateDto template = RecommendationCapabilityView.resolveTemplate(
                        templatesByName, device.templateName());
                deviceMap.put("capabilities", RecommendationCapabilityView.fromManifest(
                        template == null ? null : template.getManifest()));
                devicesList.add(deviceMap);
            }
            return objectMapper.writeValueAsString(Map.of(
                    "devices", devicesList,
                    "environmentVariables", environmentVariables == null
                            ? Collections.emptyList() : environmentVariables));
        } catch (Exception e) {
            log.error("Failed to build current devices JSON", e);
            throw new IllegalStateException("Could not serialize current devices for recommendation", e);
        }
    }

    private String buildAvailableTemplatesJson(List<DeviceTemplateDto> templates) {
        try {
            List<Map<String, Object>> templatesList = new ArrayList<>();
            for (DeviceTemplateDto template : templates) {
                DeviceTemplateDto.DeviceManifest manifest = template.getManifest();
                Map<String, Object> templateMap = new LinkedHashMap<>();
                templateMap.put("name", template.getName());
                templateMap.put("capabilities", RecommendationCapabilityView.fromManifest(manifest));

                templatesList.add(templateMap);
            }
            return objectMapper.writeValueAsString(templatesList);
        } catch (Exception e) {
            log.error("Failed to build available templates JSON", e);
            throw new IllegalStateException("Could not serialize available templates for recommendation", e);
        }
    }

    private String generateBoardRecommendationsWithAI(
            String currentDevicesInfo,
            String availableTemplatesInfo,
            int maxRecommendations,
            String language,
            String userRequirement) {
        String userPrompt = "## 现有设备\n" + currentDevicesInfo
                + "\n\n## 可用模板\n" + availableTemplatesInfo
                + "\n\n## 推荐要求"
                + "\n- 最多返回 " + maxRecommendations + " 条推荐"
                + "\n" + languageInstruction(language)
                + userRequirementInstruction(userRequirement)
                + "\n\n请直接返回JSON格式的推荐结果，不要包含其他文字。";

        log.info("Calling LLM for board device recommendations, maxRecommendations={}", maxRecommendations);
        String content = promptCompletionService.completeRecommendation(
                SYSTEM_PROMPT, userPrompt, TEMPERATURE, MAX_TOKENS);

        if (content == null || content.isBlank()) {
            return "";
        }
        return content;
    }

    private String parseBoardRecommendationsResponse(
            String aiResponse,
            List<DeviceTemplateDto> availableTemplates,
            List<DeviceInfoHelper.DeviceInfo> currentDevices,
            int maxRecommendations,
            String language) {
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

            // Canonical template names shown to the user and consumed by the frontend.
            Map<String, DeviceTemplateDto> availableTemplateByName = new HashMap<>();
            for (DeviceTemplateDto t : availableTemplates) {
                if (t.getName() != null) {
                    availableTemplateByName.put(t.getName().toLowerCase(Locale.ROOT), t);
                }
            }

            Set<String> existingInstanceKeys = new HashSet<>();
            for (DeviceInfoHelper.DeviceInfo device : currentDevices) {
                existingInstanceKeys.add(instanceKey(device.label()));
            }
            log.debug("Loaded {} existing device recommendation instance key(s)", existingInstanceKeys.size());

            // 解析 JSON
            JsonNode root = objectMapper.readTree(cleanedResponse);

            JsonNode recommendationsNode = root.path("recommendations");
            if (recommendationsNode.isMissingNode() && root.isArray()) {
                recommendationsNode = root;
            }
            if (!recommendationsNode.isArray()) {
                throw new IllegalArgumentException("AI response must contain a recommendations array");
            }

            List<Map<String, Object>> recommendations = new ArrayList<>();
            List<Map<String, Object>> filteredItems = new ArrayList<>();
            List<Map<String, Object>> adjustedItems = new ArrayList<>();
            Set<String> addedInstanceKeys = new HashSet<>();
            int rawCandidateCount = recommendationsNode.size();
            int count = 0;
            int inspected = 0;

            for (JsonNode rec : recommendationsNode) {
                if (count >= maxRecommendations) break;
                inspected++;

                try {
                    String templateName = rec.path("templateName").asText();
                    if (templateName == null || templateName.isBlank()) {
                        filteredItems.add(filteredItem(inspected, "missingTemplateName", language, text(rec.path("suggestedLabel"), "")));
                        continue;
                    }

                    // 检查模板是否存在于系统中
                    String templateKey = templateName.toLowerCase(Locale.ROOT);
                    DeviceTemplateDto template = availableTemplateByName.get(templateKey);
                    if (template == null) {
                        log.debug("Filtered device recommendation candidate {}: reasonCode=unknownTemplate",
                                inspected);
                        filteredItems.add(filteredItem(inspected, "unknownTemplate", language, templateName));
                        continue;
                    }
                    String canonicalTemplateName = template.getName();

                    JsonNode suggestedLabelNode = rec.path("suggestedLabel");
                    String rawSuggestedLabel = text(suggestedLabelNode, "");
                    String suggestedLabel = rawSuggestedLabel.isBlank()
                            ? suggestedLabelFallback(rec, canonicalTemplateName)
                            : rawSuggestedLabel;
                    String key = instanceKey(suggestedLabel);
                    if (existingInstanceKeys.contains(key) || addedInstanceKeys.contains(key)) {
                        log.debug("Filtered device recommendation candidate {}: reasonCode=duplicateDeviceInstance",
                                inspected);
                        filteredItems.add(filteredItem(inspected, "duplicateDeviceInstance", language, suggestedLabel));
                        continue;
                    }

                    Map<String, Object> recommendation = new LinkedHashMap<>();
                    Map<String, Object> appliedDefaults = new LinkedHashMap<>();
                    recommendation.put("templateName", canonicalTemplateName);
                    recommendation.put("suggestedLabel", suggestedLabel);
                    if (rawSuggestedLabel.isBlank()) {
                        appliedDefaults.put("suggestedLabel", suggestedLabel);
                    }
                    recommendation.put("intendedUse", rec.path("intendedUse").asText(""));
                    recommendation.put("suggestedPlacement", rec.path("suggestedPlacement").asText(""));
                    recommendation.put("description", rec.path("description").asText(""));
                    recommendation.put("reason", rec.path("reason").asText(""));
                    JsonNode initialStateNode = rec.path("initialState");
                    String rawInitialState = initialStateNode.asText("").trim();
                    String initialState = canonicalInitialState(template, rawInitialState);
                    if (isPresentNode(initialStateNode)
                            && (rawInitialState.isBlank() || initialState == null)) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    if (initialState != null && hasStateMachine(template)) {
                        recommendation.put("initialState", initialState);
                        if (!isPresentNode(initialStateNode)) {
                            appliedDefaults.put("state", initialState);
                        }
                        JsonNode trustNode = rec.path("currentStateTrust");
                        String trust = normalizeTrust(trustNode.asText(""));
                        if (isPresentNode(trustNode) && trust == null) {
                            filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                            continue;
                        }
                        if (trust != null) recommendation.put("currentStateTrust", trust);
                        JsonNode privacyNode = rec.path("currentStatePrivacy");
                        String privacy = normalizePrivacy(privacyNode.asText(""));
                        if (isPresentNode(privacyNode) && privacy == null) {
                            filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                            continue;
                        }
                        if (privacy != null) recommendation.put("currentStatePrivacy", privacy);
                    } else if (isPresentNode(rec.path("currentStateTrust"))
                            || isPresentNode(rec.path("currentStatePrivacy"))) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    JsonNode initialVariablesNode = rec.path("initialVariables");
                    if (isPresentNode(initialVariablesNode) && !initialVariablesNode.isArray()) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    List<Map<String, Object>> initialVariables = normalizeInitialVariables(
                            template, initialVariablesNode, appliedDefaults);
                    if (initialVariables == null) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    if (!initialVariables.isEmpty()) {
                        recommendation.put("initialVariables", initialVariables);
                    }
                    JsonNode initialPrivaciesNode = rec.path("initialPrivacies");
                    if (isPresentNode(initialPrivaciesNode) && !initialPrivaciesNode.isArray()) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    List<Map<String, Object>> initialPrivacies = normalizeInitialPrivacies(
                            template, initialPrivaciesNode, appliedDefaults);
                    if (initialPrivacies == null) {
                        filteredItems.add(filteredItem(inspected, "invalidInitialRuntime", language, suggestedLabel));
                        continue;
                    }
                    if (!initialPrivacies.isEmpty()) {
                        recommendation.put("initialPrivacies", initialPrivacies);
                    }

                    recommendations.add(recommendation);
                    if (!appliedDefaults.isEmpty()) {
                        adjustedItems.add(adjustedItem(inspected, language, suggestedLabel, appliedDefaults));
                    }
                    addedInstanceKeys.add(key);
                    count++;
                } catch (Exception e) {
                    log.warn("Failed to parse device recommendation candidate {}: exception={}",
                            inspected, e.getClass().getName());
                    filteredItems.add(filteredItem(inspected, "parseFailed", language, text(rec.path("templateName"), "")));
                }
            }

            Map<String, Object> result = new LinkedHashMap<>();
            if (recommendations.isEmpty()) {
                result.put("message", recommendationMessage(
                        language, rawCandidateCount == 0 ? "noCandidates" : "empty", 0));
            } else {
                result.put("message", recommendationMessage(language, "found", recommendations.size()));
            }
            result.put("count", recommendations.size());
            result.put("requestedCount", maxRecommendations);
            result.put("validatedCount", recommendations.size());
            result.put("filteredCount", filteredItems.size());
            result.put("filteredItems", filteredItems);
            result.put("adjustedCount", adjustedItems.size());
            result.put("adjustedItems", adjustedItems);
            result.put("rawCandidateCount", rawCandidateCount);
            result.put("inspectedCount", inspected);
            result.put("truncatedCount", Math.max(0, rawCandidateCount - inspected));
            result.put("recommendations", recommendations);

            return objectMapper.writeValueAsString(result);

        } catch (Exception e) {
            log.error("Failed to parse AI response: exception={}", e.getClass().getName());
            return errorJson(
                    recommendationMessage(language, "parseFailed", 0),
                    "AI_RESPONSE_INVALID",
                    502,
                    Map.of("phase", "response_parse"));
        }
    }

    private Map<String, Object> filteredItem(int index, String reasonCode, String language, String label) {
        return new RecommendationFilterItem(
                "device",
                index,
                reasonCode,
                validationReason(language, reasonCode),
                label
        ).toMap();
    }

    private Map<String, Object> adjustedItem(int index,
                                             String language,
                                             String label,
                                             Map<String, Object> appliedValues) {
        return new RecommendationAdjustmentItem(
                "device",
                index,
                "deviceDefaultsApplied",
                "zh-CN".equals(language)
                        ? "AI 省略了设备名称或初始运行字段；系统按建议部署区域和设备模板补全了实际应用值。"
                        : "The AI omitted the device name or initial runtime fields; effective values were derived from the suggested placement and device template.",
                label,
                appliedValues
        ).toMap();
    }

    private String validationReason(String language, String reasonCode) {
        boolean zh = "zh-CN".equals(language);
        return switch (reasonCode) {
            case "missingTemplateName" -> zh
                    ? "候选设备缺少模板名称，无法判断要创建哪类设备实例。"
                    : "The candidate is missing a template name, so the device type cannot be resolved.";
            case "unknownTemplate" -> zh
                    ? "候选设备引用了当前模板库中不存在的设备模板。"
                    : "The candidate references a device template that is not available.";
            case "duplicateDeviceInstance" -> zh
                    ? "候选设备与画布上已有实例或本次已保留推荐重复。"
                    : "The candidate duplicates an existing board instance or another kept recommendation.";
            case "invalidInitialRuntime" -> zh
                    ? "候选设备的初始状态、初始变量或隐私配置不符合该设备模板；后端不会静默丢弃这些配置后继续返回该建议。"
                    : "The candidate's initial state, variable, or privacy settings do not match the device template; the backend does not silently drop those settings and keep the suggestion.";
            case "parseFailed" -> zh
                    ? "该候选项不是可解析的设备推荐对象。"
                    : "The candidate is not a parseable device recommendation object.";
            default -> zh
                    ? "该候选设备未通过后端模板校验。"
                    : "The candidate did not pass backend template validation.";
        };
    }

    private String userRequirementInstruction(String userRequirement) {
        if (userRequirement == null || userRequirement.isBlank()) {
            return "";
        }
        return "\n- 用户需求场景: " + userRequirement
                + "\n- 优先推荐能补足该场景的设备；只能从可用模板中选择，不要编造模板。";
    }

    private String text(JsonNode node, String fallback) {
        if (node == null || node.isMissingNode() || node.isNull()) {
            return fallback;
        }
        String text = node.asText("").trim();
        return text.isEmpty() ? fallback : text;
    }

    private String suggestedLabelFallback(JsonNode rec, String templateName) {
        String suggestedPlacement = text(rec.path("suggestedPlacement"), "");
        if (!suggestedPlacement.isBlank()) {
            return suggestedPlacement + " " + templateName;
        }
        return templateName;
    }

    private String instanceKey(String label) {
        return String.valueOf(label).trim().toLowerCase(Locale.ROOT);
    }

    private String canonicalInitialState(DeviceTemplateDto template, String rawState) {
        if (template == null || template.getManifest() == null) {
            return null;
        }
        List<DeviceTemplateDto.DeviceManifest.WorkingState> states = template.getManifest().getWorkingStates();
        if (states == null || states.isEmpty()) {
            return null;
        }
        String candidate = rawState == null || rawState.isBlank()
                ? template.getManifest().getInitState()
                : rawState.trim();
        if (candidate == null || candidate.isBlank()) {
            return null;
        }
        for (DeviceTemplateDto.DeviceManifest.WorkingState state : states) {
            if (state.getName() != null && state.getName().equalsIgnoreCase(candidate)) {
                return state.getName();
            }
        }
        return null;
    }

    private List<Map<String, Object>> normalizeInitialVariables(
            DeviceTemplateDto template,
            JsonNode variablesNode,
            Map<String, Object> appliedDefaults) {
        if (template == null || template.getManifest() == null) return Collections.emptyList();
        if (isPresentNode(variablesNode) && !variablesNode.isArray()) return null;
        Map<String, DeviceTemplateDto.DeviceManifest.InternalVariable> localVariables = localVariableMap(template);
        List<Map<String, Object>> variables = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        if (variablesNode.isArray()) for (JsonNode row : variablesNode) {
            if (!row.isObject()) return null;
            String name = text(row.path("name"), "");
            if (name.isBlank() || !seen.add(name.toLowerCase(Locale.ROOT))) return null;
            DeviceTemplateDto.DeviceManifest.InternalVariable variable = localVariables.get(name.toLowerCase(Locale.ROOT));
            if (variable == null) return null;
            String value = canonicalVariableValue(variable, row.path("value").asText(""));
            if (value == null) return null;
            JsonNode trustNode = row.path("trust");
            String trust = normalizeTrust(trustNode.asText(""));
            if (isPresentNode(trustNode) && trust == null) return null;
            Map<String, Object> normalized = new LinkedHashMap<>();
            normalized.put("name", variable.getName());
            normalized.put("value", value);
            if (trust != null) normalized.put("trust", trust);
            variables.add(normalized);
        }
        for (DeviceTemplateDto.DeviceManifest.InternalVariable variable : localVariables.values()) {
            String key = variable.getName().toLowerCase(Locale.ROOT);
            if (seen.contains(key)) continue;
            String value = defaultVariableValue(variable);
            if (value == null) continue;
            Map<String, Object> normalized = new LinkedHashMap<>();
            normalized.put("name", variable.getName());
            normalized.put("value", value);
            variables.add(normalized);
            appliedDefaults.put("variables." + variable.getName() + ".value", value);
        }
        return variables;
    }

    private boolean hasStateMachine(DeviceTemplateDto template) {
        return template != null && template.getManifest() != null
                && template.getManifest().getModes() != null
                && !template.getManifest().getModes().isEmpty()
                && template.getManifest().getWorkingStates() != null
                && !template.getManifest().getWorkingStates().isEmpty();
    }

    private List<Map<String, Object>> normalizeInitialPrivacies(
            DeviceTemplateDto template,
            JsonNode privaciesNode,
            Map<String, Object> appliedDefaults) {
        if (template == null || template.getManifest() == null) return Collections.emptyList();
        if (isPresentNode(privaciesNode) && !privaciesNode.isArray()) return null;
        Map<String, DeviceTemplateDto.DeviceManifest.InternalVariable> localVariables = localVariableMap(template);
        List<Map<String, Object>> privacies = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        if (privaciesNode.isArray()) for (JsonNode row : privaciesNode) {
            if (!row.isObject()) return null;
            String name = text(row.path("name"), "");
            if (name.isBlank() || !seen.add(name.toLowerCase(Locale.ROOT))) return null;
            DeviceTemplateDto.DeviceManifest.InternalVariable variable = localVariables.get(name.toLowerCase(Locale.ROOT));
            if (variable == null) return null;
            JsonNode privacyNode = row.path("privacy");
            String normalizedPrivacy = normalizePrivacy(privacyNode.asText(""));
            if (isPresentNode(privacyNode) && normalizedPrivacy == null) return null;
            if (normalizedPrivacy != null) {
                Map<String, Object> normalized = new LinkedHashMap<>();
                normalized.put("name", variable.getName());
                normalized.put("privacy", normalizedPrivacy);
                privacies.add(normalized);
            }
        }
        return privacies;
    }

    private Map<String, DeviceTemplateDto.DeviceManifest.InternalVariable> localVariableMap(DeviceTemplateDto template) {
        Map<String, DeviceTemplateDto.DeviceManifest.InternalVariable> variables = new LinkedHashMap<>();
        if (template.getManifest() == null || template.getManifest().getInternalVariables() == null) {
            return variables;
        }
        for (DeviceTemplateDto.DeviceManifest.InternalVariable variable : template.getManifest().getInternalVariables()) {
            if (variable.getName() != null && Boolean.TRUE.equals(variable.getIsInside())) {
                variables.put(variable.getName().toLowerCase(Locale.ROOT), variable);
            }
        }
        return variables;
    }

    private String defaultVariableValue(DeviceTemplateDto.DeviceManifest.InternalVariable variable) {
        if (variable == null) return null;
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            String value = variable.getValues().get(0);
            return value == null || value.isBlank() ? null : value;
        }
        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            return String.valueOf(variable.getLowerBound());
        }
        return null;
    }

    private String canonicalVariableValue(DeviceTemplateDto.DeviceManifest.InternalVariable variable, String rawValue) {
        if (variable == null || rawValue == null) {
            return null;
        }
        String value = rawValue.trim();
        if (value.isBlank()) {
            return null;
        }
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            for (String allowed : variable.getValues()) {
                if (allowed != null && allowed.equalsIgnoreCase(value)) {
                    return allowed;
                }
            }
            return null;
        }
        if (variable.getLowerBound() != null || variable.getUpperBound() != null) {
            try {
                double number = Double.parseDouble(value);
                if (variable.getLowerBound() != null && number < variable.getLowerBound()) {
                    return null;
                }
                if (variable.getUpperBound() != null && number > variable.getUpperBound()) {
                    return null;
                }
                return value;
            } catch (NumberFormatException e) {
                return null;
            }
        }
        return value;
    }

    private boolean isProvided(JsonNode node) {
        return node != null && !node.isMissingNode() && !node.isNull() && !node.asText("").trim().isEmpty();
    }

    private boolean isPresentNode(JsonNode node) {
        return node != null && !node.isMissingNode() && !node.isNull();
    }

    private String normalizeTrust(String value) {
        if (value == null) {
            return null;
        }
        String normalized = value.trim().toLowerCase(Locale.ROOT);
        return "trusted".equals(normalized) || "untrusted".equals(normalized) ? normalized : null;
    }

    private String normalizePrivacy(String value) {
        if (value == null) {
            return null;
        }
        String normalized = value.trim().toLowerCase(Locale.ROOT);
        return "public".equals(normalized) || "private".equals(normalized) ? normalized : null;
    }

    private String languageInstruction(String language) {
        if ("zh-CN".equals(language)) {
            return "- 输出语言: 简体中文。description、reason、message 等自然语言字段必须使用简体中文。";
        }
        return "- Output language: English. Use English for every natural-language field such as description, reason, and message.";
    }

    private String recommendationMessage(String language, String key, int count) {
        boolean zh = "zh-CN".equals(language);
        return switch (key) {
            case "empty" -> zh
                    ? "暂无适合当前画布的设备推荐。"
                    : "No suitable devices found for your board.";
            case "noCandidates" -> zh
                    ? "AI 本次没有返回任何设备候选；后端没有过滤项目。请调整需求或重试。"
                    : "AI returned no device candidates in this run; the backend filtered nothing. Refine the request or retry.";
            case "found" -> zh
                    ? String.format("为当前画布找到 %d 个推荐设备。", count)
                    : String.format("Found %d recommended devices for your board.", count);
            case "parseFailed" -> zh
                    ? "解析设备推荐失败，请重试。"
                    : "Failed to parse recommendations.";
            case "noTemplates" -> zh
                    ? "暂无可用设备模板，无法生成设备推荐。"
                    : "No device templates are available for recommendations.";
            default -> zh ? "设备推荐已完成。" : "Device recommendation completed.";
        };
    }
}
