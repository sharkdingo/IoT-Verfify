package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyDouble;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.contains;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class RecommendRelatedDevicesToolTest {

    @Mock
    private PromptCompletionService promptCompletionService;
    @Mock
    private DeviceInfoHelper deviceInfoHelper;
    @Mock
    private BoardStorageService boardStorageService;

    private final ObjectMapper objectMapper = new ObjectMapper();
    private RecommendRelatedDevicesTool tool;

    @BeforeEach
    void setUp() {
        tool = new RecommendRelatedDevicesTool(promptCompletionService, objectMapper, deviceInfoHelper, boardStorageService);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void executeBoardRecommendations_rejectsUnknownRequestFieldBeforeReadingBoardOrCallingAi() throws Exception {
        JsonNode json = objectMapper.readTree(
                tool.executeBoardRecommendations("{\"userRequrement\":\"night safety\"}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals("$ contains unsupported field(s): userRequrement.", json.path("error").asText());
        verify(boardStorageService, never()).getDeviceTemplates(1L);
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void executeBoardRecommendations_withUnparseableAiResponse_returnsUpstreamError() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(template("Camera")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("not-json");

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations("{}"));

        assertEquals("AI_RESPONSE_INVALID", json.path("errorCode").asText());
        assertEquals(502, json.path("status").asInt());
        assertEquals("response_parse", json.path("phase").asText());
    }

    @Test
    void executeBoardRecommendations_whenAiReturnsNoCandidates_reportsNoFiltering() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(template("Camera")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("{\"recommendations\":[]}");

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations("{}"));

        assertEquals(0, json.path("rawCandidateCount").asInt());
        assertEquals(0, json.path("filteredCount").asInt());
        assertTrue(json.path("message").asText().contains("returned no device candidates"));
    }

    @Test
    void executeBoardRecommendations_honorsMaxRecommendations() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(
                template("Camera"), template("Alarm"), template("Plug")));
        when(promptCompletionService.completeRecommendation(
                anyString(),
                contains("最多返回 2 条推荐"),
                anyDouble(),
                anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"Camera","description":"Add camera","reason":"Visibility","confidence":0.9},
                            {"templateName":"Alarm","description":"Add alarm","reason":"Security","confidence":0.8},
                            {"templateName":"Plug","description":"Add plug","reason":"Automation","confidence":0.7}
                          ]
                        }
                        """);

        String result = tool.executeBoardRecommendations("""
                {
                  "maxRecommendations": 2
                }
                """);

        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(2, json.path("count").asInt());
        assertEquals(2, json.path("recommendations").size());
        assertEquals(3, json.path("rawCandidateCount").asInt());
        assertEquals(2, json.path("inspectedCount").asInt());
        assertEquals(1, json.path("truncatedCount").asInt());
        assertEquals("Camera", json.path("recommendations").get(0).path("templateName").asText());
        assertEquals("Alarm", json.path("recommendations").get(1).path("templateName").asText());
    }

    @Test
    void executeBoardRecommendations_withChineseLanguage_returnsLocalizedBackendMessage() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(
                new DeviceInfoHelper.DeviceInfo(
                        "door-1",
                        "Door",
                        "Door",
                        "closed",
                        "trusted",
                        null,
                        List.of(),
                        List.of(),
                        List.of(),
                        List.of(),
                        List.of(),
                        List.of(),
                        List.of("closed", "open"),
                        List.of())
        ));
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(template("Camera")));
        when(promptCompletionService.completeRecommendation(
                anyString(),
                contains("输出语言: 简体中文"),
                anyDouble(),
                anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"Camera","description":"补充摄像头","reason":"增强可视化监控","confidence":0.9}
                          ]
                        }
                        """);

        String result = tool.executeBoardRecommendations("""
                {
                  "language": "zh-CN",
                  "maxRecommendations": 3
                }
                """);

        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals("为当前画布找到 1 个推荐设备。", json.path("message").asText());
        assertEquals(1, json.path("count").asInt());
        assertEquals("Camera", json.path("recommendations").get(0).path("templateName").asText());
    }

    @Test
    void executeBoardRecommendations_canonicalizesTemplateNameFromAvailableTemplate() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(template("Window Shade")));
        when(promptCompletionService.completeRecommendation(
                anyString(),
                anyString(),
                anyDouble(),
                anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"window shade","description":"Add shade","reason":"Privacy","confidence":0.9}
                          ]
                        }
                        """);

        String result = tool.executeBoardRecommendations("{\"maxRecommendations\":3}");

        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertEquals("Window Shade", json.path("recommendations").get(0).path("templateName").asText());
    }

    @Test
    void executeBoardRecommendations_returnsFilteredItemsForUnknownTemplates() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(template("Camera")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"Imaginary Sensor","description":"Invalid","reason":"Not real","confidence":0.7},
                            {"templateName":"Camera","suggestedLabel":"Entry Camera","description":"Add camera","reason":"Visibility","confidence":0.9}
                          ]
                        }
                        """);

        String result = tool.executeBoardRecommendations("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("device", json.path("filteredItems").get(0).path("type").asText());
        assertEquals(1, json.path("filteredItems").get(0).path("index").asInt());
        assertEquals("unknownTemplate", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("Imaginary Sensor", json.path("filteredItems").get(0).path("label").asText());
    }

    @Test
    void executeBoardRecommendations_filtersCandidatesWithDroppedInitialRuntime() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(runtimeTemplate("Sensor")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"Sensor","suggestedLabel":"Bad State Sensor","initialState":"missing","description":"Bad state"},
                            {"templateName":"Sensor","suggestedLabel":"Bad Variable Sensor","initialVariables":[{"name":"missing","value":"high"}],"description":"Bad variable"},
                            {
                              "templateName":"Sensor",
                              "suggestedLabel":"Good Sensor",
                              "initialState":"active",
                              "currentStatePrivacy":"private",
                              "initialVariables":[{"name":"battery","value":"high","trust":"trusted"}],
                              "initialPrivacies":[{"name":"battery","privacy":"private"}],
                              "description":"Valid runtime"
                            }
                          ]
                        }
                        """);

        String result = tool.executeBoardRecommendations("{\"maxRecommendations\":5}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals("Good Sensor", json.path("recommendations").get(0).path("suggestedLabel").asText());
        assertEquals("active", json.path("recommendations").get(0).path("initialState").asText());
        assertEquals("private", json.path("recommendations").get(0).path("currentStatePrivacy").asText());
        assertEquals(1, json.path("recommendations").get(0).path("initialVariables").size());
        assertEquals(1, json.path("recommendations").get(0).path("initialPrivacies").size());
        assertEquals(2, json.path("filteredCount").asInt());
        assertEquals("invalidInitialRuntime", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("Bad State Sensor", json.path("filteredItems").get(0).path("label").asText());
        assertEquals("invalidInitialRuntime", json.path("filteredItems").get(1).path("reasonCode").asText());
        assertEquals("Bad Variable Sensor", json.path("filteredItems").get(1).path("label").asText());
    }

    @Test
    void executeBoardRecommendations_filtersDisplayNameDuplicatesAcrossDifferentTemplates() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(
                template("Camera"), template("Alarm")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {"templateName":"Camera","suggestedLabel":"Entry Monitor","description":"Camera"},
                            {"templateName":"Alarm","suggestedLabel":"entry monitor","description":"Alarm"}
                          ]
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations("{\"maxRecommendations\":5}"));

        assertEquals(1, json.path("count").asInt());
        assertEquals("Entry Monitor", json.path("recommendations").get(0).path("suggestedLabel").asText());
        assertEquals("duplicateDeviceInstance", json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    @Test
    void executeBoardRecommendations_materializesValuesButLeavesTemplateLabelsAsFallback() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(runtimeTemplate("Sensor")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [{
                            "templateName":"Sensor",
                            "suggestedPlacement":"Kitchen",
                            "intendedUse":"Kitchen monitoring",
                            "description":"Monitor the kitchen"
                          }]
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations("{\"maxRecommendations\":5}"));
        JsonNode recommendation = json.path("recommendations").get(0);

        assertEquals(1, json.path("count").asInt());
        assertEquals("Kitchen Sensor", recommendation.path("suggestedLabel").asText());
        assertEquals("Kitchen", recommendation.path("suggestedPlacement").asText());
        assertEquals("Kitchen monitoring", recommendation.path("intendedUse").asText());
        assertEquals("idle", recommendation.path("initialState").asText());
        assertFalse(recommendation.has("currentStateTrust"));
        assertFalse(recommendation.has("currentStatePrivacy"));
        assertEquals("battery", recommendation.path("initialVariables").get(0).path("name").asText());
        assertEquals("low", recommendation.path("initialVariables").get(0).path("value").asText());
        assertFalse(recommendation.path("initialVariables").get(0).has("trust"));
        assertFalse(recommendation.has("initialPrivacies"));
        assertEquals(1, json.path("adjustedCount").asInt());
        JsonNode defaults = json.path("adjustedItems").get(0).path("appliedValues");
        assertEquals("Kitchen Sensor", defaults.path("suggestedLabel").asText());
        assertEquals("idle", defaults.path("state").asText());
        assertEquals("low", defaults.path("variables.battery.value").asText());
        assertFalse(defaults.has("variables.battery.trust"));
        assertFalse(defaults.has("privacies.battery.privacy"));
    }

    @Test
    void executeBoardRecommendations_rejectsExplicitBlankRuntimeInsteadOfDefaultingIt() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(runtimeTemplate("Sensor")));
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [{
                            "templateName":"Sensor",
                            "suggestedLabel":"Kitchen Sensor",
                            "initialState":""
                          }]
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations("{}"));

        assertEquals(0, json.path("count").asInt());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("invalidInitialRuntime", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals(0, json.path("adjustedCount").asInt());
    }

    @Test
    void executeBoardRecommendations_rejectsOverlongRequirementInsteadOfTruncatingIt() throws Exception {
        String args = "{\"userRequirement\":\"" + "x".repeat(2001) + "\"}";

        JsonNode json = objectMapper.readTree(tool.executeBoardRecommendations(args));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals("userRequirement must be at most 2000 characters.", json.path("error").asText());
        verify(deviceInfoHelper, never()).getDevicesWithTemplateInfo(1L);
        verify(boardStorageService, never()).getDeviceTemplates(1L);
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    private DeviceTemplateDto template(String name) {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName(name);
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name(name)
                .description(name)
                .build());
        return dto;
    }

    private DeviceTemplateDto runtimeTemplate(String name) {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName(name);
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name(name)
                .description(name)
                .modes(List.of("SensorState"))
                .initState("idle")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("idle").build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("active").build()))
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("battery")
                        .isInside(true)
                        .values(List.of("low", "high"))
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .build());
        return dto;
    }
}
