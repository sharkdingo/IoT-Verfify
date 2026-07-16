package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.dto.board.CollectionMutationResultDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.core.JsonProcessingException;
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
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ManageRuleToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ManageRuleTool tool;
    private AiDestructiveActionGuard destructiveActionGuard;

    @BeforeEach
    void setUp() {
        ObjectMapper objectMapper = new ObjectMapper();
        destructiveActionGuard = new AiDestructiveActionGuard(objectMapper);
        tool = new ManageRuleTool(boardStorageService, objectMapper, destructiveActionGuard);
        UserContextHolder.setUserId(1L);
        UserContextHolder.setChatSessionId("rule-test-session");
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void add_withUnsupportedRelation_shouldReject() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"state",
                      "targetType":"state",
                      "relation":"approx",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported relation"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void add_withUnsupportedTargetType_shouldReject() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"LightMode",
                      "targetType":"unknown",
                      "relation":"=",
                      "value":"on"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported targetType"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void add_withModeTargetType_shouldPersistSemanticHint() throws Exception {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        stubSuccessfulRuleAdd();
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"LightMode",
                      "targetType":"mode",
                      "relation":"=",
                      "value":"on"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        JsonNode response = new ObjectMapper().readTree(result);
        assertEquals("NOT_VERIFIED", response.path("verificationStatus").asText());
        assertEquals(1, response.path("executionOrder").asInt());
        assertEquals("Light_1", response.path("rule").path("conditions").get(0).path("deviceId").asText());
        assertEquals("Light", response.path("rule").path("conditions").get(0).path("deviceLabel").asText());
        assertTrue(response.path("rule").path("conditions").get(0).path("deviceName").isMissingNode());
        assertTrue(response.path("message").asText().contains("not been formally verified"));
        verify(boardStorageService).addRule(anyLong(), argThat(rule ->
                rule.getConditions() != null
                        && !rule.getConditions().isEmpty()
                        && "mode".equals(rule.getConditions().get(0).getTargetType())
                        && rule.getRuleString() != null
                        && rule.getRuleString().contains("IF Light.LightMode = on THEN Light.turnOn")));
    }

    @Test
    void add_withLabel_shouldPersistProvidedUserText() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        stubSuccessfulRuleAdd();
        String argsJson = """
                {
                  "action":"add",
                  "label":"When motion is detected, turn the light on.",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"motionDetected",
                      "targetType":"api"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("not been formally verified"));
        verify(boardStorageService).addRule(anyLong(), argThat(rule ->
                "When motion is detected, turn the light on.".equals(rule.getRuleString())));
    }

    @Test
    void add_withOrderedModeRelation_shouldRejectBeforeStorage() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"LightMode",
                      "targetType":"mode",
                      "relation":">",
                      "value":"on"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("targetType 'mode' only supports =, !=, in, not in"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void add_withApiTargetTypeWithoutRelationValue_shouldPersistEventSignalShape() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        stubSuccessfulRuleAdd();
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"on",
                      "targetType":"api"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"off"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("not been formally verified"));
        verify(boardStorageService).addRule(anyLong(), argThat(rule ->
                rule.getConditions() != null
                        && !rule.getConditions().isEmpty()
                        && "api".equals(rule.getConditions().get(0).getTargetType())
                        && rule.getConditions().get(0).getRelation() == null
                        && rule.getConditions().get(0).getValue() == null));
    }

    @Test
    void add_withApiTargetTypeAndRelationValue_shouldReject() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"on",
                      "targetType":"api",
                      "relation":"=",
                      "value":"TRUE"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"off"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("must not include relation or value"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void add_withUnknownCommandApi_shouldRejectBeforeStorage() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"state",
                      "targetType":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"launch"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("unknown API"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void add_withIllegalVariableValue_shouldRejectBeforeStorage() {
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        when(boardStorageService.getDeviceTemplates(1L)).thenReturn(List.of(lightTemplate()));
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"motion",
                      "targetType":"variable",
                      "relation":"=",
                      "value":"maybe"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Condition 1"));
        assertFalse(result.contains("Condition index"));
        assertTrue(result.contains("illegal enum value"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    @Test
    void execute_whenJsonSerializationFails_shouldReturnStableErrorJson() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.writeValueAsString(any())).thenThrow(new JsonProcessingException("boom") {
        });

        ManageRuleTool fallbackTool = new ManageRuleTool(boardStorageService, failingMapper, destructiveActionGuard);
        UserContextHolder.clear();

        String result = fallbackTool.execute("{}");

        JsonNode json = new ObjectMapper().readTree(result);
        assertEquals("User not logged in", json.path("error").asText());
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void add_whenResponseSerializationFails_shouldReturnResultUnavailable() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node("Light_1", "Light")));
        stubSuccessfulRuleAdd();

        ManageRuleTool fallbackTool = new ManageRuleTool(boardStorageService, failingMapper, destructiveActionGuard);

        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceId":"Light_1",
                      "attribute":"state",
                      "targetType":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceId":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = fallbackTool.execute(argsJson);
        JsonNode json = new ObjectMapper().readTree(result);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertEquals(false, json.path("resultAvailable").asBoolean());
        assertTrue(json.path("warning").asText().contains("serialization failed"));
    }

    @Test
    void delete_requiresPreviewAndExplicitLaterConfirmation() throws Exception {
        RuleDto target = RuleDto.builder().id(9L).ruleString("When smoke is detected, sound alarm").build();
        when(boardStorageService.getRules(1L)).thenReturn(List.of(target));
        when(boardStorageService.removeRuleIfUnchanged(1L, 9L, target))
                .thenReturn(CollectionMutationResultDto.of("deleted", target, List.of()));

        String preview = tool.execute("{\"action\":\"delete\",\"ruleId\":9,\"confirmed\":true}");
        JsonNode previewJson = new ObjectMapper().readTree(preview);
        assertTrue(previewJson.path("requiresUserConfirmation").asBoolean());
        verify(boardStorageService, never()).removeRuleIfUnchanged(anyLong(), anyLong(), any());

        UserContextHolder.setDestructiveActionConfirmed(true);
        String result = tool.execute("{\"action\":\"delete\",\"ruleId\":9,\"confirmed\":true,\"impactToken\":\""
                + previewJson.path("impactToken").asText() + "\"}");
        JsonNode resultJson = new ObjectMapper().readTree(result);
        assertEquals("deleted", resultJson.path("operation").asText());
        verify(boardStorageService).removeRuleIfUnchanged(1L, 9L, target);
    }

    @Test
    void add_rejectsWrongScalarTypesAndActionIrrelevantFieldsBeforeStorage() throws Exception {
        JsonNode numericValue = new ObjectMapper().readTree(tool.execute("""
                {
                  "action":"add",
                  "conditions":[{
                    "deviceId":"Light_1",
                    "attribute":"state",
                    "targetType":"state",
                    "relation":"=",
                    "value":1
                  }],
                  "command":{"deviceId":"Light_1","action":"turnOn"}
                }
                """));
        JsonNode irrelevantDeleteField = new ObjectMapper().readTree(tool.execute("""
                {
                  "action":"add",
                  "ruleId":9,
                  "conditions":[],
                  "command":{}
                }
                """));

        assertEquals("VALIDATION_ERROR", numericValue.path("errorCode").asText());
        assertTrue(numericValue.path("error").asText().contains("conditions[0].value"));
        assertEquals("VALIDATION_ERROR", irrelevantDeleteField.path("errorCode").asText());
        assertTrue(irrelevantDeleteField.path("error").asText().contains("ruleId"));
        verify(boardStorageService, never()).addRule(anyLong(), any());
    }

    private void stubSuccessfulRuleAdd() {
        when(boardStorageService.addRule(anyLong(), any())).thenAnswer(invocation -> {
            RuleDto rule = invocation.getArgument(1);
            return CollectionMutationResultDto.of("created", rule, List.of(rule));
        });
    }

    private DeviceNodeDto node(String id, String label) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setLabel(label);
        node.setTemplateName("Light");
        return node;
    }

    private DeviceTemplateDto lightTemplate() {
        DeviceTemplateDto template = new DeviceTemplateDto();
        template.setName("Light");
        DeviceTemplateDto.DeviceManifest manifest = new DeviceTemplateDto.DeviceManifest();
        manifest.setName("Light");
        manifest.setModes(List.of("Switch"));
        manifest.setInitState("Off");
        manifest.setWorkingStates(List.of(
                workingState("Off"),
                workingState("On")
        ));
        manifest.setInternalVariables(List.of(
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("motion")
                        .isInside(false)
                        .values(List.of("yes", "no"))
                        .build()
        ));
        manifest.setApis(List.of(
                api("turnOn", false),
                api("turnOff", false),
                api("motionDetected", true)
        ));
        template.setManifest(manifest);
        return template;
    }

    private DeviceTemplateDto.DeviceManifest.WorkingState workingState(String name) {
        DeviceTemplateDto.DeviceManifest.WorkingState state = new DeviceTemplateDto.DeviceManifest.WorkingState();
        state.setName(name);
        state.setTrust("trusted");
        state.setDescription("");
        state.setDynamics(List.of());
        return state;
    }

    private DeviceTemplateDto.DeviceManifest.API api(String name, boolean signal) {
        DeviceTemplateDto.DeviceManifest.API api = new DeviceTemplateDto.DeviceManifest.API();
        api.setName(name);
        api.setSignal(signal);
        return api;
    }
}
