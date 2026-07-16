package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyDouble;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.ArgumentMatchers.contains;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class RecommendRulesToolTest {

    @Mock
    private DeviceInfoHelper deviceInfoHelper;

    @Mock
    private BoardStorageService boardStorageService;

    @Mock
    private PromptCompletionService promptCompletionService;

    private final ObjectMapper objectMapper = new ObjectMapper();
    private RecommendRulesTool tool;

    @BeforeEach
    void setUp() {
        tool = new RecommendRulesTool(deviceInfoHelper, boardStorageService, promptCompletionService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_rejectsUnknownRequestFieldBeforeReadingBoardOrCallingAi() throws Exception {
        JsonNode json = objectMapper.readTree(tool.execute("{\"maxRecomendations\":3}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals("$ contains unsupported field(s): maxRecomendations.", json.path("error").asText());
        verify(deviceInfoHelper, never()).getDevicesWithTemplateInfo(anyLong());
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void execute_withUnparseableAiResponse_returnsUpstreamErrorNotEmptySuccess() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("not-json");

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals("AI_RESPONSE_INVALID", json.path("errorCode").asText());
        assertEquals(502, json.path("status").asInt());
        assertEquals("response_parse", json.path("phase").asText());
    }

    @Test
    void execute_whenAiReturnsNoCandidates_distinguishesThatFromBackendFiltering() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("{\"recommendations\":[]}");

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(0, json.path("rawCandidateCount").asInt());
        assertEquals(0, json.path("filteredCount").asInt());
        assertTrue(json.path("message").asText().contains("returned no rule candidates"));
    }

    @Test
    void execute_withChineseLanguage_returnsLocalizedBackendMessage() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(
                anyString(),
                contains("输出语言: 简体中文"),
                anyDouble(),
                anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "检测到动作时开灯",
                              "requiresUserInput": true,
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.9
                            }
                          ]
                        }
                        """);

        String result = tool.execute("""
                {
                  "language": "zh-CN",
                  "maxRecommendations": 3
                }
                """);

        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals("基于当前设备找到 1 条规则推荐。", json.path("message").asText());
        assertEquals(1, json.path("count").asInt());
        assertEquals("node-light", json.path("recommendations").get(0).path("command").path("deviceId").asText());
        assertEquals("Light", json.path("recommendations").get(0).path("command").path("deviceName").asText());
        assertTrue(json.path("recommendations").get(0).path("requiresUserInput").isMissingNode());
    }

    @Test
    void execute_acceptsModeAttributeRecommendation() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(homeModeDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Sleep mode turns off the light",
                              "conditions": [
                                {"deviceId":"node-home-mode","deviceName":"Home Mode","attribute":"Mode","targetType":"mode","relation":"=","value":"sleep"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.82
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertEquals("Mode", json.path("recommendations").get(0).path("conditions").get(0).path("attribute").asText());
        assertEquals("sleep", json.path("recommendations").get(0).path("conditions").get(0).path("value").asText());
    }

    @Test
    void execute_normalizesSetRelationRecommendation() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(homeModeDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Non-away modes turn on the light",
                              "conditions": [
                                {"deviceId":"node-home-mode","deviceName":"Home Mode","attribute":"Mode","targetType":"mode","relation":"NOT_IN","value":"away"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.82
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode condition = json.path("recommendations").get(0).path("conditions").get(0);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertEquals("not in", condition.path("relation").asText());
        assertEquals("away", condition.path("value").asText());
    }

    @Test
    void execute_acceptsFullStateTupleSetRecommendation() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(homeModeDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Occupied idle modes turn on the light",
                              "conditions": [
                                {"deviceId":"node-home-mode","deviceName":"Home Mode","attribute":"state","targetType":"state","relation":"IN","value":"home;idle,sleep;idle"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.84
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode condition = json.path("recommendations").get(0).path("conditions").get(0);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertEquals("state", condition.path("targetType").asText());
        assertEquals("state", condition.path("attribute").asText());
        assertEquals("in", condition.path("relation").asText());
        assertEquals("home;idle,sleep;idle", condition.path("value").asText());
    }

    @Test
    void execute_acceptsApiSignalRecommendationWithoutRelationOrValue() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(motionSensorDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Motion signal turns on the light",
                              "conditions": [
                                {"deviceId":"node-motion","deviceName":"Motion Sensor","attribute":"motionDetected","targetType":"api"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.86
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode condition = json.path("recommendations").get(0).path("conditions").get(0);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertEquals("api", condition.path("targetType").asText());
        assertEquals("motionDetected", condition.path("attribute").asText());
        assertTrue(condition.path("relation").isMissingNode());
        assertTrue(condition.path("value").isMissingNode());
        assertEquals(0, json.path("adjustedCount").asInt());
    }

    @Test
    void execute_reportsEquivalentApiEventSyntaxNormalization() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(motionSensorDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Motion signal turns on the light",
                              "conditions": [
                                {"deviceId":"node-motion","deviceName":"Motion Sensor","attribute":"motionDetected","targetType":"api","relation":"=","value":"TRUE"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.84
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode condition = json.path("recommendations").get(0).path("conditions").get(0);

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(1, json.path("count").asInt());
        assertTrue(condition.path("relation").isMissingNode());
        assertTrue(condition.path("value").isMissingNode());
        assertEquals(1, json.path("adjustedCount").asInt());
        assertEquals("apiEventSyntaxNormalized",
                json.path("adjustedItems").get(0).path("reasonCode").asText());
        assertEquals("motionDetected",
                json.path("adjustedItems").get(0).path("appliedValues").path("sourceApi").asText());
    }

    @Test
    void execute_filtersApiEventComparisonsThatChangeOrLeaveSemanticsAmbiguous() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(motionSensorDevice(), lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {"recommendations":[
                          {"name":"False is not an event occurrence",
                           "conditions":[{"deviceId":"node-motion","attribute":"motionDetected",
                             "targetType":"api","relation":"=","value":"FALSE"}],
                           "command":{"deviceId":"node-light","action":"turnOn"}},
                          {"name":"A partial comparison is ambiguous",
                           "conditions":[{"deviceId":"node-motion","attribute":"motionDetected",
                             "targetType":"api","relation":"="}],
                           "command":{"deviceId":"node-light","action":"turnOn"}}
                        ]}
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{\"maxRecommendations\":3}"));

        assertEquals(0, json.path("count").asInt());
        assertEquals(2, json.path("filteredCount").asInt());
        assertEquals("invalidApiEventSyntax",
                json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("invalidApiEventSyntax",
                json.path("filteredItems").get(1).path("reasonCode").asText());
        assertEquals(0, json.path("adjustedCount").asInt());
    }

    @Test
    void execute_canonicalizesAiFieldCaseBeforeReturningRecommendation() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Uppercase AI output should still apply",
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"MOTION","targetType":"variable","relation":"EQ","value":"YES"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"TURNON"},
                              "confidence": 0.84
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode recommendation = json.path("recommendations").get(0);
        JsonNode condition = recommendation.path("conditions").get(0);

        assertEquals(1, json.path("count").asInt());
        assertEquals("motion", condition.path("attribute").asText());
        assertEquals("=", condition.path("relation").asText());
        assertEquals("yes", condition.path("value").asText());
        assertEquals("turnOn", recommendation.path("command").path("action").asText());
    }

    @Test
    void execute_reportsTruncatedRawCandidatesAfterRequestedLimit() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Valid motion rule",
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.8
                            },
                            {
                              "name": "Second valid motion rule",
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.7
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":1}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals(2, json.path("rawCandidateCount").asInt());
        assertEquals(1, json.path("inspectedCount").asInt());
        assertEquals(1, json.path("truncatedCount").asInt());
    }

    @Test
    void execute_returnsFilteredItemsWithReasonsForInvalidCandidates() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Uses an unknown action",
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOff"},
                              "confidence": 0.5
                            },
                            {
                              "name": "Valid motion rule",
                              "conditions": [
                                {"deviceId":"node-light","deviceName":"Light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","deviceName":"Light","action":"turnOn"},
                              "confidence": 0.8
                            }
                          ]
                        }
                        """);

        String result = tool.execute("{\"maxRecommendations\":3}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("rule", json.path("filteredItems").get(0).path("type").asText());
        assertEquals(1, json.path("filteredItems").get(0).path("index").asInt());
        assertEquals("unknownActionApi", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("Uses an unknown action", json.path("filteredItems").get(0).path("label").asText());
    }

    @Test
    void execute_rejectsOutOfRangeCountBeforePrompting() throws Exception {
        String result = tool.execute("{\"maxRecommendations\":999,\"category\":\"nonsense\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("maxRecommendations must be between 1 and 10.", json.path("error").asText());
        verify(deviceInfoHelper, never()).getDevicesWithTemplateInfo(anyLong());
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void execute_rejectsUnsupportedCategoryInsteadOfSilentlyUsingAll() throws Exception {
        JsonNode json = objectMapper.readTree(tool.execute("{\"category\":\"nonsense\"}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertTrue(json.path("error").asText().startsWith("category must be one of: "));
        verify(deviceInfoHelper, never()).getDevicesWithTemplateInfo(anyLong());
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void execute_validatesContentLabelFlowAndExplainsIncompleteCandidate() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L))
                .thenReturn(List.of(lightDevice(), phoneDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "recommendations": [
                            {
                              "name": "Post the phone photo",
                              "conditions": [
                                {"deviceId":"node-light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","action":"turnOn","contentDevice":"node-phone","content":"PHOTO"}
                            },
                            {
                              "name": "Incomplete content flow",
                              "conditions": [
                                {"deviceId":"node-light","attribute":"motion","targetType":"variable","relation":"=","value":"yes"}
                              ],
                              "command": {"deviceId":"node-light","action":"turnOn","contentDevice":"node-phone"}
                            }
                          ]
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(1, json.path("count").asInt());
        JsonNode command = json.path("recommendations").get(0).path("command");
        assertEquals("photo", command.path("content").asText());
        assertEquals("private", command.path("contentPrivacy").asText());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("incompleteContentPayload",
                json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    @Test
    void execute_filtersContentFlowWhenTheTargetActionDoesNotAcceptContent() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L))
                .thenReturn(List.of(lightDevice(), motionSensorDevice(), phoneDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {"recommendations":[{
                          "name":"Attach a photo to an ordinary action",
                          "conditions":[{"deviceId":"node-light","attribute":"motion",
                            "targetType":"variable","relation":"=","value":"yes"}],
                          "command":{"deviceId":"node-motion","action":"motionDetected",
                            "contentDevice":"node-phone","content":"photo"}
                        }]}
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(0, json.path("count").asInt());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("actionDoesNotAcceptContent",
                json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    @Test
    void execute_filtersCandidateWithUnknownSemanticField() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {"recommendations":[{
                          "name":"Open a door as a hidden effect",
                          "conditions":[{"deviceId":"node-light","attribute":"motion",
                            "targetType":"variable","relation":"=","value":"yes"}],
                          "command":{"deviceId":"node-light","action":"turnOn"},
                          "unmodeledEffect":"open door"
                        }]}
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(0, json.path("count").asInt());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("unknownCandidateField",
                json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    @Test
    void execute_filtersCandidateWithoutPersistedRuleName() throws Exception {
        when(deviceInfoHelper.getDevicesWithTemplateInfo(1L)).thenReturn(List.of(lightDevice()));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {"recommendations":[{
                          "conditions":[{"deviceId":"node-light","attribute":"motion",
                            "targetType":"variable","relation":"=","value":"yes"}],
                          "command":{"deviceId":"node-light","action":"turnOn"}
                        }]}
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(0, json.path("count").asInt());
        assertEquals("missingRuleName",
                json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    private DeviceInfoHelper.DeviceInfo lightDevice() {
        return new DeviceInfoHelper.DeviceInfo(
                "node-light",
                "Light",
                "Light",
                "off",
                "trusted",
                null,
                List.of(),
                List.of(),
                List.of(new DeviceInfoHelper.VariableInfo("motion", "Motion detected", List.of("yes", "no"),
                        null, null, null, null)),
                List.of(new DeviceInfoHelper.ApiInfo("turnOn", "Turn on", false,
                        true, null, null)),
                List.of(),
                List.of(),
                List.of("off", "on"),
                List.of()
        );
    }

    private DeviceInfoHelper.DeviceInfo homeModeDevice() {
        return new DeviceInfoHelper.DeviceInfo(
                "node-home-mode",
                "Home Mode",
                "Home Mode",
                "sleep;idle",
                "trusted",
                null,
                List.of(),
                List.of(),
                List.of(),
                List.of(),
                List.of(),
                List.of(
                        new DeviceInfoHelper.ModeInfo("Mode", List.of("home", "away", "sleep")),
                        new DeviceInfoHelper.ModeInfo("State", List.of("idle", "sendingAlertMessage", "sendingPhoto"))),
                List.of("home;idle", "away;idle", "sleep;idle"),
                List.of()
        );
    }

    private DeviceInfoHelper.DeviceInfo motionSensorDevice() {
        return new DeviceInfoHelper.DeviceInfo(
                "node-motion",
                "Motion Sensor",
                "Motion Sensor",
                "idle",
                "trusted",
                null,
                List.of(),
                List.of(),
                List.of(),
                List.of(new DeviceInfoHelper.ApiInfo("motionDetected", "Motion detected", true,
                        false, null, null)),
                List.of(),
                List.of(),
                List.of("idle", "detected"),
                List.of()
        );
    }

    private DeviceInfoHelper.DeviceInfo phoneDevice() {
        return new DeviceInfoHelper.DeviceInfo(
                "node-phone",
                "Phone",
                "Mobile Phone",
                "on",
                "trusted",
                "private",
                List.of(),
                List.of(),
                List.of(),
                List.of(),
                List.of(),
                List.of(),
                List.of("on"),
                List.of(new DeviceInfoHelper.ContentInfo("photo", "private"))
        );
    }
}
