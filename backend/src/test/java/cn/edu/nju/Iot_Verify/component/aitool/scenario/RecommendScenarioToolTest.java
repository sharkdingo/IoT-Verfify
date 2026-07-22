package cn.edu.nju.Iot_Verify.component.aitool.scenario;

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
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.ArgumentMatchers.contains;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class RecommendScenarioToolTest {

    @Mock
    private PromptCompletionService promptCompletionService;

    @Mock
    private BoardStorageService boardStorageService;

    private final ObjectMapper objectMapper = new ObjectMapper();
    private AiScenarioDraftStore draftStore;
    private RecommendScenarioTool tool;

    @BeforeEach
    void setUp() {
        draftStore = new AiScenarioDraftStore();
        tool = new RecommendScenarioTool(
                promptCompletionService, boardStorageService, draftStore, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_rejectsUnknownRequestFieldBeforeReadingBoardOrCallingAi() throws Exception {
        JsonNode json = objectMapper.readTree(tool.execute("{\"maxSpecification\":3}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals("$ contains unsupported field(s): maxSpecification.", json.path("error").asText());
        verify(boardStorageService, never()).getDeviceTemplates(1L);
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void execute_withUnparseableAiResponse_returnsUpstreamErrorNotEmptyScene() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("not-json");

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals("AI_RESPONSE_INVALID", json.path("errorCode").asText());
        assertEquals(502, json.path("status").asInt());
        assertEquals("response_parse", json.path("phase").asText());
    }

    @Test
    void execute_whenAiReturnsNoSceneItems_reportsNoFiltering() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName":"Empty draft",
                          "rationale":"No items proposed",
                          "scene":{"devices":[],"environmentVariables":[],"rules":[],"specs":[]}
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(0, json.path("rawCandidateCount").asInt());
        assertEquals(0, json.path("filteredCount").asInt());
        assertFalse(json.path("verificationReady").asBoolean());
        assertEquals("NO_DEVICES", json.path("readinessIssues").get(0).path("code").asText());
        assertEquals("NO_SPECIFICATIONS", json.path("readinessIssues").get(1).path("code").asText());
        assertTrue(json.path("message").asText().contains("returned no scene-item candidates"));
        assertFalse(json.has("draftStored"));
        assertFalse(json.has("previousDraftRetained"));
    }

    @Test
    void execute_whenEmptyRecommendationRetainsPreviousDraft_reportsItExplicitly() throws Exception {
        UserContextHolder.setChatSessionId("session-1");
        draftStore.saveDraft(1L, "session-1", "Previous", objectMapper.readTree(
                "{\"devices\":[{\"id\":\"device_1\"}],\"rules\":[],\"specs\":[]}"));
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of());

        JsonNode json = objectMapper.readTree(tool.execute("{\"language\":\"en\"}"));

        assertFalse(json.path("draftStored").asBoolean());
        assertTrue(json.path("previousDraftRetained").asBoolean());
        assertTrue(json.path("message").asText().contains("previous valid draft"));
        assertEquals("Previous", draftStore.latestDraft(1L, "session-1").orElseThrow().scenarioName());
    }

    @Test
    void execute_generatesCoupledSceneAndKeepsPrefixLikeNamesLiteral() throws Exception {
        UserContextHolder.setChatSessionId("session-1");
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate(), lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(
                anyString(),
                contains("全量替换 scene 草案"),
                anyDouble(),
                anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Prefix-safe safety scene",
                          "rationale": "The rule and spec both reference the same sensor and light.",
                          "scene": {
                            "devices": [
                              {"id":"sensor_1","templateName":"Noise Sensor","label":"Noise Sensor"},
                              {"id":"light_1","templateName":"Light","label":"Light","state":"off"}
                            ],
                            "environmentVariables": [
                              {"name":"a_noise","value":"high","trust":"trusted","privacy":"public"},
                              {"name":"a_noise","value":"low","trust":"untrusted","privacy":"private"}
                            ],
                            "rules": [
                              {
                                "name":"High noise turns on light",
                                "sources":[{"fromId":"sensor_1","fromApi":"a_noise","itemType":"variable","relation":"=","value":"high"}],
                                "toId":"light_1",
                                "toApi":"turnOn"
                              }
                            ],
                            "specs": [
                              {
                                "id":"spec_1",
                                "templateId":"4",
                                "templateLabel":"Immediate response",
                                "ifConditions":[{"deviceId":"sensor_1","targetType":"variable","key":"a_noise","relation":"=","value":"high"}],
                                "thenConditions":[{"deviceId":"light_1","targetType":"state","key":"state","relation":"=","value":"on"}]
                              }
                            ]
                          }
                        }
                        """);

        String result = tool.execute("""
                {
                  "language": "en",
                  "userRequirement": "a_noise is a real environment variable name"
                }
                """);

        JsonNode json = objectMapper.readTree(result);
        JsonNode scene = json.path("scene");

        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertEquals(4, scene.path("version").asInt());
        assertEquals(2, scene.path("devices").size());
        assertFalse(scene.path("devices").get(0).has("state"));
        assertEquals(1, scene.path("rules").size());
        assertEquals(1, scene.path("specs").size());
        assertTrue(json.path("verificationReady").asBoolean());
        assertTrue(json.path("draftStored").asBoolean());
        assertFalse(json.path("previousDraftRetained").asBoolean());
        assertEquals(0, json.path("readinessIssues").size());
        assertEquals("FILTERED_CANDIDATES",
                json.path("semanticWarnings").get(0).path("code").asText());
        assertTrue(json.path("rationale").asText().contains("final canonical draft"));
        assertTrue(json.path("rationale").asText().contains("does not claim"));
        assertFalse(json.path("rationale").asText().contains("both reference the same sensor and light"));
        assertEquals("a_noise", scene.path("environmentVariables").get(0).path("name").asText());
        assertEquals("a_noise", scene.path("rules").get(0).path("sources").get(0).path("fromApi").asText());
        assertEquals("device_1", scene.path("specs").get(0).path("ifConditions").get(0).path("deviceId").asText());
        assertEquals("a_noise", scene.path("specs").get(0).path("ifConditions").get(0).path("key").asText());
        assertEquals("device_2", scene.path("specs").get(0).path("thenConditions").get(0).path("deviceId").asText());
        assertFalse(scene.path("templates").get(0).has("defaultTemplate"));
        assertFalse(scene.path("specs").get(0).has("id"));
        assertFalse(scene.path("specs").get(0).has("templateLabel"));
        assertFalse(scene.path("specs").get(0).has("devices"));
        assertFalse(scene.path("specs").get(0).path("ifConditions").get(0).has("id"));
        assertFalse(scene.path("specs").get(0).path("ifConditions").get(0).has("side"));
        assertFalse(scene.path("specs").get(0).path("ifConditions").get(0).has("deviceLabel"));
        assertTrue(json.path("filteredItems").findValuesAsText("reasonCode")
                .contains("duplicateEnvironmentVariable"));
        assertTrue(json.path("message").asText().contains("importable scene draft"));
        verify(promptCompletionService).completeRecommendation(
                argThat(system -> system.contains("不要声称它安全、完整、已验证或已应用")
                        && system.contains("itemType=api 时")
                        && system.contains("必须省略 relation 和 value")
                        && system.contains("不要把规约中 API 条件的 = TRUE 写法套到规则 API 事件源")
                        && system.contains("\"itemType\": \"api\"")),
                argThat(prompt -> prompt.contains("尚未形式化验证")
                        && prompt.contains("不会自动应用")),
                anyDouble(),
                anyInt());
        assertTrue(json.path("message").asText().contains("not been formally verified"));
        assertFalse(json.path("message").asText().contains("complete scenario"));
        AiScenarioDraftStore.DraftSnapshot stored = draftStore
                .latestDraft(1L, "session-1")
                .orElseThrow();
        assertEquals("Prefix-safe safety scene", stored.scenarioName());
        assertEquals(2, stored.scene().path("devices").size());
    }

    @Test
    void execute_normalizesEquivalentApiEventBooleanSyntaxButRejectsDifferentSemantics() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L))
                .thenReturn(List.of(eventSourceTemplate(), eventTargetTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scene": {
                            "devices": [
                              {"id":"source","templateName":"Event Source","label":"Event Source","state":"idle"},
                              {"id":"target","templateName":"Event Target","label":"Event Target","state":"off"}
                            ],
                            "rules": [
                              {
                                "name":"Equivalent API event syntax",
                                "sources":[{
                                  "fromId":"source","fromApi":"notify","itemType":"api",
                                  "relation":"=","value":"true"
                                }],
                                "toId":"target","toApi":"activate"
                              },
                              {
                                "name":"Different API boolean semantics",
                                "sources":[{
                                  "fromId":"source","fromApi":"notify","itemType":"api",
                                  "relation":"=","value":"FALSE"
                                }],
                                "toId":"target","toApi":"activate"
                              }
                            ],
                            "specs": []
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));
        JsonNode rules = json.path("scene").path("rules");

        assertEquals(1, rules.size());
        assertEquals("Equivalent API event syntax", rules.get(0).path("name").asText());
        JsonNode source = rules.get(0).path("sources").get(0);
        assertEquals("api", source.path("itemType").asText());
        assertFalse(source.has("relation"));
        assertFalse(source.has("value"));
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("invalidRuleSources",
                json.path("filteredItems").get(0).path("reasonCode").asText());
        assertTrue(json.path("adjustedItems").findValuesAsText("reasonCode")
                .contains("apiEventSyntaxNormalized"));
        JsonNode adjustment = json.path("adjustedItems").findParents("reasonCode").stream()
                .filter(item -> "apiEventSyntaxNormalized".equals(item.path("reasonCode").asText()))
                .findFirst()
                .orElseThrow();
        assertEquals("notify", adjustment.path("appliedValues").path("sourceApi").asText());
        assertEquals("=", adjustment.path("appliedValues").path("removedRelation").asText());
        assertEquals("TRUE", adjustment.path("appliedValues").path("removedValue").asText());
    }

    @Test
    void execute_returnsFilteredItemsForInvalidSceneCandidates() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate(), lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Partially invalid scene",
                          "scene": {
                            "devices": [
                              {"id":"sensor_1","templateName":"Noise Sensor","label":"Noise Sensor"},
                              {"id":"ghost_1","templateName":"Ghost Device","label":"Ghost Device","state":"on"},
                              {"id":"light_1","templateName":"Light","label":"Light","state":"off"}
                            ],
                            "rules": [
                              {
                                "name":"Ghost triggers light",
                                "sources":[{"fromId":"ghost_1","fromApi":"motion","itemType":"variable","relation":"=","value":"yes"}],
                                "toId":"light_1",
                                "toApi":"turnOn"
                              },
                              {
                                "name":"Noise turns on light",
                                "sources":[{"fromId":"sensor_1","fromApi":"a_noise","itemType":"variable","relation":"=","value":"high"}],
                                "toId":"light_1",
                                "toApi":"turnOn"
                              }
                            ],
                            "specs": [
                              {"id":"spec_bad","templateId":"99","templateLabel":"Unknown spec"}
                            ]
                          }
                        }
                        """);

        String result = tool.execute("{\"maxDevices\":5,\"maxRules\":5,\"maxSpecs\":5}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(4, json.path("count").asInt(),
                "Final scene count includes the required shared environment item");
        assertEquals(3, json.path("validatedCount").asInt());
        assertEquals(3, json.path("filteredCount").asInt());
        assertEquals(6, json.path("rawCandidateCount").asInt());
        assertEquals(6, json.path("inspectedCount").asInt());
        assertEquals(0, json.path("truncatedCount").asInt());
        assertEquals("device", json.path("filteredItems").get(0).path("type").asText());
        assertEquals("unknownTemplate", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("rule", json.path("filteredItems").get(1).path("type").asText());
        assertEquals("invalidRuleSources", json.path("filteredItems").get(1).path("reasonCode").asText());
        assertEquals("specification", json.path("filteredItems").get(2).path("type").asText());
        assertEquals("invalidSpecTemplateId", json.path("filteredItems").get(2).path("reasonCode").asText());
    }

    @Test
    void execute_filtersWholeRuleOrSpecWhenAnyNestedCandidateWouldBeDropped() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate(), lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Partially dropped nested candidates",
                          "scene": {
                            "devices": [
                              {"id":"sensor_1","templateName":"Noise Sensor","label":"Noise Sensor"},
                              {"id":"light_1","templateName":"Light","label":"Light","state":"off"}
                            ],
                            "rules": [
                              {
                                "name":"Noise or missing variable turns on light",
                                "sources":[
                                  {"fromId":"sensor_1","fromApi":"a_noise","itemType":"variable","relation":"=","value":"high"},
                                  {"fromId":"sensor_1","fromApi":"missing_variable","itemType":"variable","relation":"=","value":"high"}
                                ],
                                "toId":"light_1",
                                "toApi":"turnOn"
                              }
                            ],
                            "specs": [
                              {
                                "id":"spec_partial",
                                "templateId":"1",
                                "templateLabel":"Always",
                                "aConditions":[
                                  {"deviceId":"sensor_1","targetType":"variable","key":"a_noise","relation":"=","value":"high"},
                                  {"deviceId":"sensor_1","targetType":"variable","key":"missing_variable","relation":"=","value":"high"}
                                ]
                              }
                            ]
                          }
                        }
                        """);

        String result = tool.execute("{\"maxDevices\":5,\"maxRules\":5,\"maxSpecs\":5}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode scene = json.path("scene");

        assertEquals(3, json.path("count").asInt(),
                "Final scene count includes the required shared environment item");
        assertEquals(2, scene.path("devices").size());
        assertTrue(scene.path("rules").isEmpty());
        assertTrue(scene.path("specs").isEmpty());
        assertEquals(2, json.path("filteredCount").asInt());
        assertEquals("rule", json.path("filteredItems").get(0).path("type").asText());
        assertEquals("invalidRuleSources", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("specification", json.path("filteredItems").get(1).path("type").asText());
        assertEquals("invalidSpecConditions", json.path("filteredItems").get(1).path("reasonCode").asText());
    }

    @Test
    void execute_filtersUnknownEnvironmentVariablesInsteadOfReturningDriftingScene() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(sensorTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Unknown environment variable",
                          "scene": {
                            "devices": [
                              {"id":"sensor_1","templateName":"Noise Sensor","label":"Noise Sensor"}
                            ],
                            "environmentVariables": [
                              {"name":"weather","value":"rainy","trust":"trusted","privacy":"public"}
                            ],
                            "rules": [],
                            "specs": []
                          }
                        }
                        """);

        String result = tool.execute("{\"maxDevices\":5,\"maxRules\":5,\"maxSpecs\":5}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode scene = json.path("scene");

        assertEquals(2, json.path("count").asInt(),
                "Final scene count includes the required shared environment item");
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("environment", json.path("filteredItems").get(0).path("type").asText());
        assertEquals("unknownEnvironmentVariable", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("weather", json.path("filteredItems").get(0).path("label").asText());
        assertEquals(1, scene.path("environmentVariables").size());
        assertEquals("a_noise", scene.path("environmentVariables").get(0).path("name").asText());
    }

    @Test
    void execute_filtersDeviceWithInvalidInitialRuntimeInsteadOfDefaultingIt() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Invalid device runtime",
                          "scene": {
                            "devices": [
                              {"id":"light_bad","templateName":"Light","label":"Bad Light","state":"dimmed","currentStateTrust":"trusted"},
                              {"id":"light_trust_bad","templateName":"Light","label":"Bad Trust Light","state":"off","currentStateTrust":"maybe"},
                              {"id":"light_ok","templateName":"Light","label":"Ok Light","state":"on","currentStateTrust":"trusted"}
                            ],
                            "rules": [],
                            "specs": []
                          }
                        }
                        """);

        String result = tool.execute("{\"maxDevices\":5,\"maxRules\":5,\"maxSpecs\":5}");
        JsonNode json = objectMapper.readTree(result);
        JsonNode scene = json.path("scene");

        assertEquals(1, scene.path("devices").size());
        assertEquals("device_1", scene.path("devices").get(0).path("id").asText());
        assertEquals("on", scene.path("devices").get(0).path("state").asText());
        assertEquals(2, json.path("filteredCount").asInt());
        assertEquals("invalidDeviceRuntime", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("invalidDeviceRuntime", json.path("filteredItems").get(1).path("reasonCode").asText());
    }

    @Test
    void execute_rejectsIncompleteRuleContentFlowInsteadOfSilentlyDroppingIt() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L))
                .thenReturn(List.of(lightTemplate(), contentTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Incomplete content flow",
                          "scene": {
                            "devices": [
                              {"id":"light_1","templateName":"Light","label":"Light","state":"off"},
                              {"id":"phone_1","templateName":"Phone","label":"Phone"}
                            ],
                            "rules": [
                              {
                                "name":"Missing content item",
                                "sources":[{"fromId":"light_1","fromApi":"brightness","itemType":"variable","relation":">","value":"50"}],
                                "toId":"light_1",
                                "toApi":"turnOn",
                                "contentDevice":"phone_1"
                              }
                            ],
                            "specs": []
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(2, json.path("scene").path("devices").size());
        assertTrue(json.path("scene").path("rules").isEmpty());
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("invalidRuleContent",
                json.path("filteredItems").get(0).path("reasonCode").asText());
    }

    @Test
    void execute_preservesValidatedLocalRuntimeLabelsAndRejectsEnvironmentOverridesOnDevices() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate(), sensorTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Runtime labels",
                          "scene": {
                            "devices": [
                              {
                                "id":"light_1",
                                "templateName":"Light",
                                "label":"Desk Light",
                                "state":"on",
                                "currentStateTrust":"TRUSTED",
                                "currentStatePrivacy":"PRIVATE",
                                "variables":[{"name":"brightness","value":"80","trust":"UNTRUSTED"}],
                                "privacies":[{"name":"brightness","privacy":"PRIVATE"}]
                              },
                              {
                                "id":"sensor_bad",
                                "templateName":"Noise Sensor",
                                "label":"Bad Sensor",
                                "state":"Working"
                              }
                            ],
                            "rules": [],
                            "specs": [{
                              "templateId":"1",
                              "templateLabel":"Current state sensitivity",
                              "aConditions":[{
                                "deviceId":"light_1",
                                "targetType":"privacy",
                                "propertyScope":"state",
                                "key":"SwitchState",
                                "relation":"=",
                                "value":"PRIVATE"
                              }],
                              "ifConditions":[],
                              "thenConditions":[]
                            }]
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));
        JsonNode devices = json.path("scene").path("devices");

        assertEquals(1, devices.size());
        assertEquals("trusted", devices.get(0).path("currentStateTrust").asText());
        assertEquals("private", devices.get(0).path("currentStatePrivacy").asText());
        assertEquals("brightness", devices.get(0).path("variables").get(0).path("name").asText());
        assertEquals("80", devices.get(0).path("variables").get(0).path("value").asText());
        assertEquals("untrusted", devices.get(0).path("variables").get(0).path("trust").asText());
        assertEquals("private", devices.get(0).path("privacies").get(0).path("privacy").asText());
        JsonNode propertyCondition = json.path("scene").path("specs").get(0).path("aConditions").get(0);
        assertEquals("state", propertyCondition.path("propertyScope").asText());
        assertEquals("SwitchState", propertyCondition.path("key").asText());
        assertEquals("private", propertyCondition.path("value").asText());
        assertFalse(propertyCondition.toString().contains("SwitchState_"));
        assertEquals(1, json.path("filteredCount").asInt());
        assertEquals("invalidDeviceRuntime", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("Bad Sensor", json.path("filteredItems").get(0).path("label").asText());
    }

    @Test
    void execute_filtersDuplicateIdsAndInvalidProvidedLayoutInsteadOfSilentlyRewriting() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Invalid identities and layout",
                          "scene": {
                            "devices": [
                              {"id":"light_1","templateName":"Light","label":"First","state":"off"},
                              {"id":"light_1","templateName":"Light","label":"Duplicate","state":"on"},
                              {"id":"light_small","templateName":"Light","label":"Too small","state":"off","width":10},
                              {"id":"light_bad_pos","templateName":"Light","label":"Bad position","state":"off","position":{"x":"left","y":20}},
                              {"id":"light_far","templateName":"Light","label":"Outside portable canvas","state":"off","position":{"x":1000001,"y":20}}
                            ],
                            "rules": [],
                            "specs": []
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(1, json.path("scene").path("devices").size());
        assertEquals("device_1", json.path("scene").path("devices").get(0).path("id").asText());
        assertEquals(4, json.path("filteredCount").asInt());
        assertEquals("duplicateDeviceId", json.path("filteredItems").get(0).path("reasonCode").asText());
        assertEquals("invalidDeviceLayout", json.path("filteredItems").get(1).path("reasonCode").asText());
        assertEquals("invalidDeviceLayout", json.path("filteredItems").get(2).path("reasonCode").asText());
        assertEquals("invalidDeviceLayout", json.path("filteredItems").get(3).path("reasonCode").asText());
    }

    @Test
    void execute_rewritesAiAliasAcrossDependenciesAndReportsEveryAppliedDefault() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scenarioName": "Literal identity",
                          "scene": {
                            "devices": [{
                              "id":"Hall Light #1",
                              "templateName":"Light",
                              "label":"Hall Light",
                              "variables":[{"name":"brightness","value":"80"}]
                            }],
                            "rules": [{
                              "name":"Bright hall light stays on",
                              "sources":[{"fromId":"Hall Light #1","fromApi":"brightness","itemType":"variable","relation":">","value":"50"}],
                              "toId":"Hall Light #1",
                              "toApi":"turnOn"
                            }],
                            "specs": [{
                              "templateId":"1",
                              "aConditions":[{"deviceId":"Hall Light #1","targetType":"state","key":"state","relation":"=","value":"on"}],
                              "ifConditions":[],
                              "thenConditions":[]
                            }]
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));
        JsonNode scene = json.path("scene");

        assertEquals("device_1", scene.path("devices").get(0).path("id").asText());
        assertEquals("device_1", scene.path("rules").get(0).path("sources").get(0).path("fromId").asText());
        assertEquals("device_1", scene.path("rules").get(0).path("toId").asText());
        assertEquals("device_1", scene.path("specs").get(0).path("aConditions").get(0).path("deviceId").asText());
        assertEquals(3, json.path("validatedCount").asInt());
        assertEquals(1, json.path("adjustedCount").asInt());
        JsonNode defaults = json.path("adjustedItems").get(0).path("appliedValues");
        assertEquals("off", defaults.path("state").asText());
        assertEquals(176, defaults.path("width").asInt());
        assertEquals(128, defaults.path("height").asInt());
        assertFalse(defaults.has("currentStateTrust"));
        assertFalse(defaults.has("currentStatePrivacy"));
        assertFalse(defaults.has("variables.brightness.trust"));
        assertFalse(defaults.has("privacies.brightness.privacy"));
        assertFalse(scene.path("devices").get(0).has("currentStateTrust"));
        assertFalse(scene.path("devices").get(0).has("currentStatePrivacy"));
        assertFalse(scene.path("devices").get(0).has("privacies"));
    }

    @Test
    void execute_keepsRuleWhenOptionalDisplayNameIsMissing() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scene": {
                            "devices": [{"id":"light_1","templateName":"Light","label":"Light","state":"off"}],
                            "rules": [{
                              "sources":[{"fromId":"light_1","fromApi":"brightness","itemType":"variable","relation":">","value":"50"}],
                              "toId":"light_1",
                              "toApi":"turnOn"
                            }],
                            "specs": []
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        JsonNode rule = json.path("scene").path("rules").get(0);
        assertFalse(rule.has("name"));
        assertEquals("device_1", rule.path("toId").asText());
        assertEquals(0, json.path("filteredCount").asInt());
    }

    @Test
    void execute_rewritesAiAliasesSoModelNormalizationCannotMergeDevices() throws Exception {
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scene": {
                            "devices": [
                              {"id":"Hall Light","templateName":"Light","label":"Hall Light A","state":"off"},
                              {"id":"hall-light","templateName":"Light","label":"Hall Light B","state":"on"}
                            ],
                            "rules": [],
                            "specs": []
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(2, json.path("scene").path("devices").size());
        assertEquals("device_1", json.path("scene").path("devices").get(0).path("id").asText());
        assertEquals("device_2", json.path("scene").path("devices").get(1).path("id").asText());
        assertEquals(0, json.path("filteredCount").asInt());
    }

    @Test
    void execute_revalidatesTemplate7ApiConditionByStableDeviceReference() throws Exception {
        DeviceTemplateDto notifier = new DeviceTemplateDto();
        notifier.setName("Notifier");
        notifier.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Notifier")
                .modes(List.of("Status"))
                .initState("idle")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("idle").build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("notified").build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("notify").signal(true).endState("notified").build()))
                .build());
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(notifier));
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of());
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(promptCompletionService.completeRecommendation(anyString(), anyString(), anyDouble(), anyInt()))
                .thenReturn("""
                        {
                          "scene": {
                            "devices": [{
                              "id":"Notifier response alias",
                              "templateName":"Notifier",
                              "label":"Entry notifier",
                              "state":"idle"
                            }],
                            "rules": [],
                            "specs": [{
                              "templateId":"7",
                              "aConditions":[{
                                "deviceId":"Notifier response alias",
                                "targetType":"api",
                                "key":"notify"
                              }],
                              "ifConditions":[],
                              "thenConditions":[]
                            }]
                          }
                        }
                        """);

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals(1, json.path("scene").path("specs").size());
        assertEquals("device_1", json.path("scene").path("specs").get(0)
                .path("aConditions").get(0).path("deviceId").asText());
        assertEquals("=", json.path("scene").path("specs").get(0)
                .path("aConditions").get(0).path("relation").asText());
        assertEquals("TRUE", json.path("scene").path("specs").get(0)
                .path("aConditions").get(0).path("value").asText());
        assertEquals(0, json.path("filteredCount").asInt());
    }

    @Test
    void execute_rejectsDecimalMaxDevicesBeforeLoadingBoard() throws Exception {
        String result = tool.execute("{\"maxDevices\":2.5}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("maxDevices must be an integer between 1 and 10.", json.path("error").asText());
        verify(boardStorageService, never()).getDeviceTemplates(1L);
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    @Test
    void execute_rejectsNonStringRequirementInsteadOfCoercingIt() throws Exception {
        JsonNode json = objectMapper.readTree(tool.execute("{\"userRequirement\":123}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals("userRequirement must be a string.", json.path("error").asText());
        verify(boardStorageService, never()).getDeviceTemplates(1L);
        verify(promptCompletionService, never()).complete(anyString(), anyString(), anyDouble(), anyInt());
    }

    private DeviceTemplateDto sensorTemplate() {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Noise Sensor");
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Noise Sensor")
                .description("Noise sensor")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("a_noise")
                        .description("Noise level")
                        .isInside(false)
                        .values(List.of("high", "low"))
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .initState("Working")
                .workingStates(List.of(DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                        .name("Working")
                        .build()))
                .build());
        return dto;
    }

    private DeviceTemplateDto lightTemplate() {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Light");
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Light")
                .description("Light")
                .modes(List.of("SwitchState"))
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("brightness")
                        .description("Brightness")
                        .isInside(true)
                        .lowerBound(0)
                        .upperBound(100)
                        .naturalChangeRate("[-1, 1]")
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .initState("off")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("off").build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("on").build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("turnOn")
                        .description("Turn on")
                        .signal(false)
                        .acceptsContent(true)
                        .startState("off")
                        .endState("on")
                        .build()))
                .build());
        return dto;
    }

    private DeviceTemplateDto contentTemplate() {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Phone");
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Phone")
                .description("Phone")
                .initState("on")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("on").build()))
                .contents(List.of(DeviceTemplateDto.DeviceManifest.Content.builder()
                        .name("photo")
                        .privacy("private")
                        .build()))
                .build());
        return dto;
    }

    private DeviceTemplateDto eventSourceTemplate() {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Event Source");
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Event Source")
                .modes(List.of("Status"))
                .initState("idle")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("idle").build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("notified").build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("notify").signal(true).endState("notified").build()))
                .build());
        return dto;
    }

    private DeviceTemplateDto eventTargetTemplate() {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Event Target");
        dto.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name("Event Target")
                .modes(List.of("Status"))
                .initState("off")
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("off").build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder().name("on").build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("activate").signal(true).endState("on").build()))
                .build());
        return dto;
    }
}
