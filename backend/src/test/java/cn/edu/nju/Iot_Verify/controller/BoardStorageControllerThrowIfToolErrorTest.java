package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckDuplicateRuleTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckRuleSimilarityTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRelatedDevicesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRulesTool;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.RecommendScenarioTool;
import cn.edu.nju.Iot_Verify.component.aitool.spec.RecommendSpecificationsTool;
import cn.edu.nju.Iot_Verify.component.board.BoardBatchRequestParser;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BadGatewayException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.dto.recommendation.DeviceRecommendationRequestDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioRecommendationResponseDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioRecommendationRequestDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.InteractiveAiExecutionService;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.concurrent.Callable;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.lenient;

@ExtendWith(MockitoExtension.class)
class BoardStorageControllerThrowIfToolErrorTest {

    @Mock private BoardStorageService boardService;
    @Mock private RecommendRulesTool recommendRulesTool;
    @Mock private RecommendRelatedDevicesTool recommendRelatedDevicesTool;
    @Mock private CheckDuplicateRuleTool checkDuplicateRuleTool;
    @Mock private CheckRuleSimilarityTool checkRuleSimilarityTool;
    @Mock private RecommendSpecificationsTool recommendSpecificationsTool;
    @Mock private RecommendScenarioTool recommendScenarioTool;
    @Mock private DeviceTemplateSchemaValidator deviceTemplateSchemaValidator;
    @Mock private BoardBatchRequestParser boardBatchRequestParser;
    @Mock private InteractiveAiExecutionService interactiveAiExecutionService;

    private BoardStorageController controller;
    private RuleDto dummyRule;
    private ObjectMapper objectMapper;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper()
                .configure(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES, true)
                .configure(DeserializationFeature.ACCEPT_FLOAT_AS_INT, false);
        controller = new BoardStorageController(
                boardService, recommendRulesTool, recommendRelatedDevicesTool,
                checkDuplicateRuleTool, checkRuleSimilarityTool,
                recommendSpecificationsTool, recommendScenarioTool, objectMapper,
                deviceTemplateSchemaValidator, boardBatchRequestParser, interactiveAiExecutionService);
        lenient().when(interactiveAiExecutionService.execute(
                        anyLong(), anyString(), org.mockito.ArgumentMatchers.<Callable<Object>>any()))
                .thenAnswer(invocation -> invocation.<Callable<Object>>getArgument(2).call());
        dummyRule = new RuleDto();
        dummyRule.setConditions(List.of());
        dummyRule.setCommand(new RuleDto.Command("dev", "on", null, null));
    }

    private void stubToolError(int status, String errorCode) throws Exception {
        String json = String.format(
                "{\"error\":\"test msg\",\"errorCode\":\"%s\",\"status\":%d}",
                errorCode, status);
        when(checkDuplicateRuleTool.execute(anyString())).thenReturn(json);
    }

    @Test
    void throwIfToolError_400_throwsBadRequest() throws Exception {
        stubToolError(400, "VALIDATION_ERROR");
        assertThrows(BadRequestException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_401_throwsUnauthorized() throws Exception {
        stubToolError(401, "UNAUTHORIZED");
        assertThrows(UnauthorizedException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_404_throwsNotFound() throws Exception {
        stubToolError(404, "NOT_FOUND");
        assertThrows(ResourceNotFoundException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_503_throwsServiceUnavailable() throws Exception {
        stubToolError(503, "SERVICE_UNAVAILABLE");
        assertThrows(ServiceUnavailableException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_500_throwsInternalServer() throws Exception {
        stubToolError(500, "INTERNAL_ERROR");
        assertThrows(InternalServerException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_502_throwsBadGateway() throws Exception {
        stubToolError(502, "AI_RESPONSE_INVALID");
        assertThrows(BadGatewayException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_403_throwsForbidden() throws Exception {
        stubToolError(403, "FORBIDDEN");
        assertThrows(ForbiddenException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_409_throwsConflict() throws Exception {
        stubToolError(409, "CONFLICT");
        assertThrows(ConflictException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void throwIfToolError_422_throwsValidation() throws Exception {
        stubToolError(422, "VALIDATION_ERROR");
        assertThrows(ValidationException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void completeDuplicateCheckResult_returnsSuccess() throws Exception {
        when(checkDuplicateRuleTool.execute(anyString()))
                .thenReturn("""
                        {"isDuplicate":false,"requiresReview":false,"matchedRule":null,
                         "similarity":0.0,"matchType":"none","reasonCode":"NO_MATCHING_SIGNATURE",
                         "reason":"no matching signature",
                         "message":"No obvious duplicate rule found; this is not a conflict-free proof."}
                        """);
        assertDoesNotThrow(() -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void incompleteDuplicateCheckResult_throwsInternalServer() throws Exception {
        when(checkDuplicateRuleTool.execute(anyString()))
                .thenReturn("{\"isDuplicate\":false}");

        assertThrows(InternalServerException.class,
                () -> controller.checkDuplicateRule(1L, dummyRule));
    }

    @Test
    void inconsistentSimilarityResult_throwsBadGateway() throws Exception {
        when(checkRuleSimilarityTool.execute(anyString())).thenReturn("""
                {"isSimilar":false,"isDuplicate":true,"requiresReview":true,
                 "matchedRule":"Existing rule","similarity":1.0,"reasonCode":"AI_DUPLICATE",
                 "reason":"same semantics","message":"duplicate"}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.checkRuleSimilarity(1L, dummyRule));
    }

    @Test
    void completeRuleRecommendationResult_mapsToTypedDto() throws Exception {
        when(recommendRulesTool.execute(anyString())).thenReturn("""
                {"message":"One rule found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":1,"adjustedItems":[{"type":"rule","index":1,
                 "reasonCode":"apiEventSyntaxNormalized","reason":"Equivalent event syntax normalized",
                 "label":"Alert on motion","appliedValues":{"sourceApi":"motion"}}],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"category":"security","name":"Alert on motion",
                 "conditions":[{"deviceId":"device_1",
                 "deviceLabel":"Hall sensor","deviceName":"Hall sensor","attribute":"motion",
                 "targetType":"api"}],"command":{"deviceId":"device_2",
                 "deviceLabel":"Alarm","deviceName":"Alarm","action":"turn_on"}}]}
                """);

        var response = controller.recommendRules(1L, 5, "all", "en", "", "request-123").getData();

        assertEquals(1, response.getAdjustedCount());
        assertEquals("apiEventSyntaxNormalized", response.getAdjustedItems().get(0).getReasonCode());
    }

    @Test
    void incompleteRecommendationAccounting_throwsBadGateway() throws Exception {
        when(recommendRulesTool.execute(anyString())).thenReturn("""
                {"message":"One rule found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":0,"adjustedItems":[],
                 "rawCandidateCount":2,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"category":"security","name":"Alert on motion",
                 "conditions":[],"command":{}}]}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendRules(1L, 5, "all", "en", "", "request-123"));
    }

    @Test
    void keptRuleRecommendationWithoutPersistedName_throwsBadGateway() throws Exception {
        when(recommendRulesTool.execute(anyString())).thenReturn("""
                {"message":"One rule found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":0,"adjustedItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"conditions":[{"deviceId":"device_1",
                 "deviceName":"Hall sensor","attribute":"motion","targetType":"api"}],
                 "command":{"deviceId":"device_2","deviceName":"Alarm","action":"turn_on"}}]}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendRules(1L, 5, "all", "en", "", "request-123"));
    }

    @Test
    void unknownKeptRecommendationField_throwsBadGateway() throws Exception {
        when(recommendRulesTool.execute(anyString())).thenReturn("""
                {"message":"One rule found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":0,"adjustedItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"category":"security","name":"Alert on motion",
                 "conditions":[],"command":{},"unmodeledEffect":"open door"}]}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendRules(1L, 5, "all", "en", "", "request-123"));
    }

    @Test
    void deviceRecommendationRequestAndAdjustments_mapToTypedDto() throws Exception {
        when(recommendRelatedDevicesTool.executeBoardRecommendations(anyString())).thenReturn("""
                {"message":"One device found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":1,"adjustedItems":[{"type":"device","index":1,
                 "reasonCode":"deviceDefaultsApplied","reason":"Defaults applied",
                 "label":"Hall sensor","appliedValues":{"initialState":"idle"}}],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"templateName":"Motion Detector",
                 "suggestedLabel":"Hall sensor","intendedUse":"trigger",
                 "suggestedPlacement":"hall",
                 "description":"Detect motion","reason":"Supports automation",
                 "initialState":"idle","currentStateTrust":"trusted",
                 "currentStatePrivacy":"public"}]}
                """);

        assertDoesNotThrow(() -> controller.recommendDevices(
                1L, "request-123", new DeviceRecommendationRequestDto()));
    }

    @Test
    void specificationRecommendation_mapsToTypedDto() throws Exception {
        when(recommendSpecificationsTool.execute(anyString())).thenReturn("""
                {"message":"One specification found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"rationale":"Motion must trigger alarm",
                 "templateId":"5","aConditions":[],
                 "ifConditions":[{"deviceId":"device_1","deviceLabel":"Hall sensor",
                 "targetType":"api","key":"motion","relation":"=","value":"TRUE"}],
                 "thenConditions":[{"deviceId":"device_2",
                 "deviceLabel":"Alarm","targetType":"state","key":"state",
                 "relation":"=","value":"on"}]}]}
                """);

        assertDoesNotThrow(() -> controller.recommendSpecs(
                1L, 5, "all", "en", "", "request-123"));
    }

    @Test
    void keptSpecificationRecommendationWithoutRationale_throwsBadGateway() throws Exception {
        when(recommendSpecificationsTool.execute(anyString())).thenReturn("""
                {"message":"One specification found.","count":1,"requestedCount":5,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "recommendations":[{"templateId":"3","aConditions":[],
                 "ifConditions":[],"thenConditions":[]}]}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendSpecs(1L, 5, "all", "en", "", "request-123"));
    }

    @Test
    void scenarioFinalCountMayIncludeSynthesizedEnvironmentItem() throws Exception {
        when(recommendScenarioTool.execute(anyString())).thenReturn("""
                {"message":"Scenario generated.","count":3,"requestedCount":16,
                 "validatedCount":2,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":1,"adjustedItems":[{"type":"environment",
                 "reasonCode":"missingEnvironmentAdded","reason":"Required value added",
                 "label":"temperature","appliedValues":{"value":"20"}}],
                 "rawCandidateCount":2,"inspectedCount":2,"truncatedCount":0,
                 "scenarioName":"Home","rationale":"Exercise a shared reading",
                 "objectiveStatus":"PARTIAL","objectiveIssues":[
                   {"code":"NO_AUTOMATION_RULES","message":"No automation rule."}],
                 "verificationReady":true,"readinessIssues":[],
                 "semanticWarnings":[{"code":"NO_AUTOMATION_RULES",
                 "message":"The final draft contains no retained automation rules."}],
                 "scene":{"schema":"iot-verify.board-scene","version":4,
                 "templates":[{"name":"Sensor","manifest":{"Name":"Sensor"}}],
                 "devices":[{"id":"device_1","templateName":"Sensor","label":"Hall sensor",
                 "position":{"x":0,"y":0},"width":176,"height":128}],
                 "environmentVariables":[{"name":"temperature","value":"20",
                 "trust":"trusted","privacy":"public"}],"rules":[],
                 "specs":[{"templateId":"3","aConditions":[{"deviceId":"device_1",
                 "targetType":"variable","key":"temperature","relation":">","value":"30"}],
                 "ifConditions":[],"thenConditions":[]}]}}
                """);

        ScenarioRecommendationResponseDto response = controller.recommendScenario(
                1L, "request-123", new ScenarioRecommendationRequestDto()).getData();
        JsonNode scene = objectMapper.valueToTree(response.getScene());

        assertEquals(List.of("manifest", "name"),
                iterableFieldNames(scene.path("templates").get(0)));
        JsonNode device = scene.path("devices").get(0);
        assertFalse(device.has("state"));
        assertFalse(device.has("currentStateTrust"));
        assertFalse(device.has("currentStatePrivacy"));
        assertEquals("device_1", device.path("id").asText());
        JsonNode condition = scene.path("specs").get(0).path("aConditions").get(0);
        assertEquals(List.of("deviceId", "key", "relation", "targetType", "value"),
                iterableFieldNames(condition));
        assertEquals("PARTIAL", response.getObjectiveStatus());
        assertEquals("NO_AUTOMATION_RULES", response.getObjectiveIssues().get(0).getCode());
        assertTrue(response.getVerificationReady());
        assertTrue(response.getReadinessIssues().isEmpty());
        assertEquals("NO_AUTOMATION_RULES", response.getSemanticWarnings().get(0).getCode());
    }

    @Test
    void scenarioReadinessMustMatchScene() {
        when(recommendScenarioTool.execute(anyString())).thenReturn("""
                {"message":"Scenario generated.","count":1,"requestedCount":3,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":0,"adjustedItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "scenarioName":"Home","rationale":"Missing a specification",
                 "objectiveStatus":"PARTIAL","objectiveIssues":[
                   {"code":"NO_AUTOMATION_RULES","message":"No automation rule."},
                   {"code":"NO_SPECIFICATIONS","message":"No formal specification."}],
                 "verificationReady":true,"readinessIssues":[],
                 "semanticWarnings":[
                   {"code":"NO_AUTOMATION_RULES","message":"No retained rules."},
                   {"code":"UNREFERENCED_DEVICES","message":"One device is unreferenced."}
                 ],
                 "scene":{"schema":"iot-verify.board-scene","version":4,
                 "templates":[],"devices":[{"id":"device_1","templateName":"Sensor",
                 "label":"Hall sensor","position":{"x":0,"y":0},"width":176,"height":128}],
                 "environmentVariables":[],"rules":[],"specs":[]}}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendScenario(
                        1L, "request-123", new ScenarioRecommendationRequestDto()));
    }

    @Test
    void scenarioObjectiveStatusMustMatchScene() {
        when(recommendScenarioTool.execute(anyString())).thenReturn("""
                {"message":"Scenario generated.","count":1,"requestedCount":3,
                 "validatedCount":1,"filteredCount":0,"filteredItems":[],
                 "adjustedCount":0,"adjustedItems":[],
                 "rawCandidateCount":1,"inspectedCount":1,"truncatedCount":0,
                 "scenarioName":"Home","rationale":"Missing core content",
                 "objectiveStatus":"COMPLETE","objectiveIssues":[],
                 "verificationReady":false,"readinessIssues":[
                   {"code":"NO_SPECIFICATIONS","message":"Add a specification."}],
                 "semanticWarnings":[
                   {"code":"NO_AUTOMATION_RULES","message":"No retained rules."},
                   {"code":"UNREFERENCED_DEVICES","message":"One device is unreferenced."}
                 ],
                 "scene":{"schema":"iot-verify.board-scene","version":4,
                 "templates":[],"devices":[{"id":"device_1","templateName":"Sensor",
                 "label":"Hall sensor","position":{"x":0,"y":0},"width":176,"height":128}],
                 "environmentVariables":[],"rules":[],"specs":[]}}
                """);

        assertThrows(BadGatewayException.class,
                () -> controller.recommendScenario(
                        1L, "request-123", new ScenarioRecommendationRequestDto()));
    }

    private static List<String> iterableFieldNames(JsonNode node) {
        java.util.ArrayList<String> names = new java.util.ArrayList<>();
        node.fieldNames().forEachRemaining(names::add);
        names.sort(String::compareTo);
        return names;
    }
}
