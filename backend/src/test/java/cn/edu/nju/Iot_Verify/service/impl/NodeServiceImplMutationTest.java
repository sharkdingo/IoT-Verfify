package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceCreationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeConfigDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.DeviceLabelConflictException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.lenient;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class NodeServiceImplMutationTest {

    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private DeviceTemplateService deviceTemplateService;

    private NodeServiceImpl nodeService;
    private List<DeviceNodeDto> savedNodes;

    @BeforeEach
    void setUp() {
        nodeService = new NodeServiceImpl(boardStorageService, deviceTemplateService, new ObjectMapper());
        savedNodes = List.of();
        lenient().when(deviceTemplateService.findTemplateByName(anyLong(), anyString()))
                .thenAnswer(invocation -> {
                    String name = invocation.getArgument(1);
                    return Optional.of(DeviceTemplatePo.builder()
                            .id(100L)
                            .userId(invocation.getArgument(0))
                            .name(name)
                            .manifestJson("{\"Name\":\"" + name + "\",\"Modes\":[]}")
                            .build());
                });
    }

    @Test
    void addNode_whenTemplateDoesNotExist_shouldThrowBadRequest() {
        when(deviceTemplateService.checkTemplateExists(1L, "unknown")).thenReturn(false);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                nodeService.addNode(1L, "unknown", null, null, null, null, null, null));

        assertEquals(400, ex.getCode());
        assertEquals("Create device failed: template 'unknown' does not exist.", ex.getMessage());
        verifyNoInteractions(boardStorageService);
    }

    @Test
    void addNode_shouldUseBoardStorageAuthorityAndPreserveAvailableLabel() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        applyNodeCreateWithExisting();

        nodeService.addNode(1L, "Light", "shared-node", 10.0, 20.0, runtime("On"), 100, 80);

        verify(boardStorageService).createNode(eq(1L), any());
        DeviceNodeDto saved = savedNode();
        assertTrue(saved.getId().startsWith("device_"));
        assertEquals("shared-node", saved.getLabel());
        assertEquals("Light", saved.getTemplateName());
        assertEquals("On", saved.getState());
        assertEquals(10.0, saved.getPosition().getX());
        assertEquals(20.0, saved.getPosition().getY());
        assertEquals(100, saved.getWidth());
        assertEquals(80, saved.getHeight());
    }

    @Test
    void addNode_keepsDistinctDisplayNamesEvenWhenTheirOldModelAliasesWouldCollide() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        applyNodeCreateWithExisting(existingNode("AC 1"));

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Light", "ac_1", null, null, runtime("On"), null, null);

        DeviceNodeDto saved = savedNode();
        assertNotEquals("ac_1", saved.getId());
        assertTrue(saved.getId().startsWith("device_"));
        assertEquals("ac_1", saved.getLabel());
        assertEquals(saved.getId(), result.getDevice().getId());
        assertTrue(result.getWarnings().isEmpty());
        assertEquals(List.of("position.x", "position.y", "width", "height"), result.getDefaultsApplied());
    }

    @Test
    void addNode_rejectsAnExplicitDuplicateLabelWithoutWriting() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        DeviceNodeDto existing = existingNode("existing-id");
        existing.setLabel("Hall Light");
        applyNodeCreateWithExisting(existing);

        DeviceLabelConflictException exception = assertThrows(DeviceLabelConflictException.class, () ->
                nodeService.addNode(
                        1L, "Light", "hall light", null, null, runtime("On"), null, null));

        assertEquals("hall light", exception.getRequestedLabel());
        assertEquals("hall light_1", exception.getSuggestedLabel());
        assertTrue(savedNodes.isEmpty());
    }

    @Test
    void addNode_whenNameWasOmitted_generatesAnAvailableDefaultName() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        DeviceNodeDto existing = existingNode("existing-id");
        existing.setLabel("LIGHT");
        applyNodeCreateWithExisting(existing);

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Light", null, null, null, runtime("On"), null, null);

        assertEquals("Light_1", savedNode().getLabel());
        assertTrue(result.getDefaultsApplied().contains("label"));
    }

    @Test
    void addNode_returnsEnvironmentPoolChangesFromTheSameAtomicCreate() {
        when(deviceTemplateService.checkTemplateExists(1L, "Sensor")).thenReturn(true);
        BoardEnvironmentVariableDto temperature =
                new BoardEnvironmentVariableDto("temperature", "20", "trusted", "public");
        EnvironmentVariableChangeDto added = EnvironmentVariableChangeDto.builder()
                .changeType(EnvironmentVariableChangeDto.ChangeType.ADDED)
                .name("temperature")
                .currentValue(temperature)
                .build();
        applyNodeCreateWithEnvironment(List.of(temperature), List.of(added));

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Sensor", "hall sensor", null, null, runtime("Working"), null, null);

        assertEquals(List.of(temperature), result.getEnvironmentVariables());
        assertEquals(List.of(added), result.getEnvironmentChanges());
    }

    @Test
    void addNode_whenSizeOmitted_shouldUseBoardDefaultNodeSize() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        applyNodeCreateWithExisting();

        nodeService.addNode(1L, "Light", "light_default_size", null, null, runtime("On"), null, null);

        assertEquals(176, savedNode().getWidth());
        assertEquals(128, savedNode().getHeight());
    }

    @Test
    void addNode_whenTemplateIsStateless_shouldUsePlaceholderWithoutWarning() {
        // Simulates Weather/Clock/Temperature Sensor templates with no state machine.
        String weatherJson = "{\"Name\":\"Weather\",\"Modes\":[],\"InitState\":\"\",\"WorkingStates\":[]}";
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L).userId(1L).name("Weather").manifestJson(weatherJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Weather")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Weather")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Weather", "weather_1", null, null, null, null, null);

        assertEquals("Working", savedNode().getState());
        assertEquals("statelessPlaceholder", result.getInitialStateSource());
        assertTrue(result.getDefaultsApplied().contains("state"));
        assertTrue(result.getWarnings().isEmpty());
    }

    @Test
    void addNode_whenTemplateHasNonEmptyInitState_shouldUseTemplateState() {
        String lightJson = "{\"Name\":\"Light\",\"Modes\":[\"SwitchState\"],\"InitState\":\"on\",\"WorkingStates\":[{\"Name\":\"on\"},{\"Name\":\"off\"}]}";
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(2L).userId(1L).name("Light").manifestJson(lightJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Light")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Light", "light_1", null, null, null, null, null);

        assertEquals("on", savedNode().getState());
        assertEquals("templateDefault", result.getInitialStateSource());
    }

    @Test
    void addNode_whenTemplateHasInternalVariables_shouldPersistOnlyDeviceInstance() {
        String lightJson = """
                {"Name":"Light","Modes":["SwitchState"],"InitState":"on",
                 "InternalVariables":[{"Name":"power"},{"Name":"temperature"}],
                 "WorkingStates":[{"Name":"on"},{"Name":"off"}]}
                """;
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(2L).userId(1L).name("Light").manifestJson(lightJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Light")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        nodeService.addNode(1L, "Light", "kitchen_light", 10.0, 20.0, null, null, null);

        assertTrue(savedNode().getId().startsWith("device_"));
        assertEquals("kitchen_light", savedNode().getLabel());
        assertEquals("on", savedNode().getState());
        assertEquals(1, savedNodes.size());
    }

    @Test
    void addNode_whenTemplateManifestMissingInitState_shouldUseFallbackState() {
        // Template JSON with no InitState key at all
        String noInitJson = "{\"Name\":\"Custom\",\"Modes\":[]}";
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(3L).userId(1L).name("Custom").manifestJson(noInitJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Custom")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Custom")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Custom", "custom_1", null, null, null, null, null);

        assertEquals("Working", savedNode().getState());
        assertEquals("statelessPlaceholder", result.getInitialStateSource());
        assertTrue(result.getWarnings().isEmpty());
    }

    @Test
    void addNode_whenStatefulTemplateHasBlankInitState_shouldWarnAboutFallback() {
        String invalidJson = "{\"Name\":\"Custom\",\"Modes\":[\"Mode\"],\"InitState\":\"\","
                + "\"WorkingStates\":[{\"Name\":\"Working\"}]}";
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(3L).userId(1L).name("Custom").manifestJson(invalidJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Custom")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Custom")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Custom", "custom_1", null, null, null, null, null);

        assertEquals("systemFallback", result.getInitialStateSource());
        assertTrue(result.getWarnings().get(0).contains("no usable initial state"));
    }

    @Test
    void addNode_whenLegacyTemplateHasOnlyPartialStateDefinition_shouldWarnAboutFallback() {
        String invalidJson = "{\"Name\":\"Custom\",\"Modes\":[],\"InitState\":\"on\","
                + "\"WorkingStates\":[]}";
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(3L).userId(1L).name("Custom").manifestJson(invalidJson).build();

        when(deviceTemplateService.checkTemplateExists(1L, "Custom")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Custom")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Custom", "custom_1", null, null, null, null, null);

        assertEquals("systemFallback", result.getInitialStateSource());
        assertFalse(result.getWarnings().isEmpty());
    }

    @Test
    void addNode_preservesExplicitUserDomainRuntimeConfiguration() {
        String sensorJson = """
                {"Name":"Sensor","Modes":["Mode"],"InitState":"idle",
                 "InternalVariables":[{"Name":"battery","IsInside":true,"Values":["low","high"],"Trust":"trusted","Privacy":"public"}],
                 "WorkingStates":[{"Name":"idle","Trust":"trusted","Privacy":"public"},{"Name":"active","Trust":"trusted","Privacy":"public"}]}
                """;
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(4L).userId(1L).name("Sensor").manifestJson(sensorJson).build();
        when(deviceTemplateService.checkTemplateExists(1L, "Sensor")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Sensor")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceRuntimeConfigDto runtime = runtime("active");
        runtime.setCurrentStateTrust("untrusted");
        runtime.setCurrentStatePrivacy("private");
        runtime.setVariables(List.of(new VariableStateDto("battery", "high", "untrusted")));
        runtime.setPrivacies(List.of(new PrivacyStateDto("battery", "private")));

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Sensor", "entry_sensor", null, null, runtime, null, null);

        DeviceNodeDto saved = savedNode();
        assertEquals("active", saved.getState());
        assertEquals("untrusted", saved.getCurrentStateTrust());
        assertEquals("private", saved.getCurrentStatePrivacy());
        assertEquals(List.of(new VariableStateDto("battery", "high", "untrusted")), saved.getVariables());
        assertEquals(List.of(new PrivacyStateDto("battery", "private")), saved.getPrivacies());
        assertTrue(result.getDefaultsApplied().contains("position.x"));
    }

    @Test
    void addNode_materializesOnlyValuesAndLeavesTemplateLabelsAsFallback() {
        String sensorJson = """
                {"Name":"Sensor","Modes":["Mode"],"InitState":"idle",
                 "InternalVariables":[
                   {"Name":"battery","IsInside":true,"Values":["low","high"],"Trust":"trusted","Privacy":"public"},
                   {"Name":"signal","IsInside":true,"LowerBound":0,"UpperBound":10,"Trust":"untrusted","Privacy":"private"}
                 ],
                 "WorkingStates":[{"Name":"idle","Trust":"trusted","Privacy":"public"}]}
                """;
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(5L).userId(1L).name("Sensor").manifestJson(sensorJson).build();
        when(deviceTemplateService.checkTemplateExists(1L, "Sensor")).thenReturn(true);
        when(deviceTemplateService.findTemplateByName(1L, "Sensor")).thenReturn(Optional.of(templatePo));
        applyNodeCreateWithExisting();

        DeviceRuntimeConfigDto runtime = runtime("idle");
        runtime.setVariables(List.of(new VariableStateDto("battery", "high", null)));
        runtime.setPrivacies(List.of());

        DeviceCreationResultDto result = nodeService.addNode(
                1L, "Sensor", "kitchen_sensor", null, null, runtime, null, null);

        DeviceNodeDto saved = savedNode();
        assertEquals(List.of(
                new VariableStateDto("battery", "high", null),
                new VariableStateDto("signal", "0", null)
        ), saved.getVariables());
        assertEquals(List.of(), saved.getPrivacies());
        assertNull(saved.getCurrentStateTrust());
        assertNull(saved.getCurrentStatePrivacy());
        assertFalse(result.getDefaultsApplied().contains("variables.battery.trust"));
        assertTrue(result.getDefaultsApplied().contains("variables.signal"));
        assertFalse(result.getDefaultsApplied().stream().anyMatch(value -> value.startsWith("privacies")));
    }

    @Test
    void addNode_whenBoardStorageRejectsRuntimeState_shouldPropagateValidation() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        when(boardStorageService.createNode(eq(1L), any()))
                .thenThrow(new ValidationException(Map.of("nodes[0].state", "Illegal state value")));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                nodeService.addNode(1L, "Light", "light_bad", null, null, runtime("broken"), null, null));

        assertEquals("Illegal state value", ex.getErrors().get("nodes[0].state"));
    }

    @SuppressWarnings("unchecked")
    private void applyNodeCreateWithExisting(DeviceNodeDto... existingNodes) {
        applyNodeCreateWithEnvironment(List.of(), List.of(), existingNodes);
    }

    @SuppressWarnings("unchecked")
    private void applyNodeCreateWithEnvironment(
            List<BoardEnvironmentVariableDto> environmentVariables,
            List<EnvironmentVariableChangeDto> environmentChanges,
            DeviceNodeDto... existingNodes) {
        when(boardStorageService.createNode(eq(1L), any())).thenAnswer(invocation -> {
            Function<List<DeviceNodeDto>, DeviceNodeDto> factory = invocation.getArgument(1, Function.class);
            List<DeviceNodeDto> current = new ArrayList<>(List.of(existingNodes));
            DeviceNodeDto created = factory.apply(List.copyOf(current));
            current.add(created);
            savedNodes = List.copyOf(current);
            return DeviceMutationResultDto.builder()
                    .operation("created")
                    .affectedDevices(List.of(created))
                    .currentNodes(savedNodes)
                    .environmentVariables(environmentVariables)
                    .environmentChanges(environmentChanges)
                    .currentCount(savedNodes.size())
                    .build();
        });
    }

    private DeviceNodeDto existingNode(String id) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setLabel(id);
        node.setTemplateName("Existing");
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(0.0);
        position.setY(0.0);
        node.setPosition(position);
        node.setState("Working");
        node.setWidth(176);
        node.setHeight(128);
        return node;
    }

    private DeviceNodeDto savedNode() {
        if (savedNodes == null || savedNodes.isEmpty()) {
            throw new AssertionError("createNode should save at least one node");
        }
        return savedNodes.get(savedNodes.size() - 1);
    }

    private DeviceRuntimeConfigDto runtime(String state) {
        DeviceRuntimeConfigDto runtime = new DeviceRuntimeConfigDto();
        runtime.setState(state);
        return runtime;
    }
}
