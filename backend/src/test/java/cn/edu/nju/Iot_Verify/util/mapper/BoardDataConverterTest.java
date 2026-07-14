package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardSemanticSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoMoreInteractions;
import static org.mockito.Mockito.when;

class BoardDataConverterTest {

    @Test
    void getDevicesForVerification_omitsStateForModeLessTemplates() {
        BoardStorageService storage = mock(BoardStorageService.class);
        when(storage.getSemanticSnapshot(1L)).thenReturn(snapshot(
                List.of(
                        node("kitchen_smoke", "Smoke Sensor", "Working"),
                        node("range_hood", "Range Hood", "off")),
                List.of(
                        template("Smoke Sensor", List.of(), List.of()),
                        template("Range Hood", List.of("MachineState"), List.of("off", "on")))));

        BoardDataConverter converter = new BoardDataConverter(storage);
        List<DeviceVerificationDto> devices = converter.getModelInputSnapshot(1L).devices();

        DeviceVerificationDto smoke = devices.stream()
                .filter(device -> "kitchen_smoke".equals(device.getVarName()))
                .findFirst()
                .orElseThrow();
        assertEquals("kitchen_smoke", smoke.getDeviceLabel());
        assertNull(smoke.getState());
        assertNull(smoke.getCurrentStateTrust());
        assertNull(smoke.getCurrentStatePrivacy());

        DeviceVerificationDto hood = devices.stream()
                .filter(device -> "range_hood".equals(device.getVarName()))
                .findFirst()
                .orElseThrow();
        assertEquals("off", hood.getState());
        assertEquals("trusted", hood.getCurrentStateTrust());
        assertEquals("private", hood.getCurrentStatePrivacy());
        verify(storage).getSemanticSnapshot(1L);
        verifyNoMoreInteractions(storage);
    }

    @Test
    void getDevicesForVerification_omitsStateWhenTemplateHasModesButNoWorkingStates() {
        BoardStorageService storage = mock(BoardStorageService.class);
        when(storage.getSemanticSnapshot(1L)).thenReturn(snapshot(
                List.of(node("draft_device", "Draft Template", "on")),
                List.of(template("Draft Template", List.of("MachineState"), List.of()))));

        BoardDataConverter converter = new BoardDataConverter(storage);
        DeviceVerificationDto device = converter.getModelInputSnapshot(1L).devices().get(0);

        assertEquals("draft_device", device.getVarName());
        assertNull(device.getState());
        assertNull(device.getCurrentStateTrust());
        assertNull(device.getCurrentStatePrivacy());
    }

    @Test
    void getDevicesForVerification_matchesTemplateByDtoNameOrManifestName() {
        BoardStorageService storage = mock(BoardStorageService.class);
        DeviceTemplateDto template = template("Window Shade Display", List.of("OpenableState"), List.of("closed", "open"));
        template.getManifest().setName("Window Shade");
        when(storage.getSemanticSnapshot(1L)).thenReturn(snapshot(
                List.of(node("shade_1", "Window Shade Display", "closed")),
                List.of(template)));

        BoardDataConverter converter = new BoardDataConverter(storage);
        BoardDataConverter.ModelInputSnapshot modelSnapshot = converter.getModelInputSnapshot(1L);
        DeviceVerificationDto device = modelSnapshot.devices().get(0);

        assertEquals("closed", device.getState());
        assertEquals("trusted", device.getCurrentStateTrust());
        assertEquals("private", device.getCurrentStatePrivacy());
        assertEquals(template.getManifest(), modelSnapshot.templateManifests().get("Window Shade Display"));
    }

    private DeviceNodeDto node(String id, String templateName, String state) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setTemplateName(templateName);
        node.setLabel(id);
        node.setState(state);
        node.setCurrentStateTrust("trusted");
        node.setCurrentStatePrivacy("private");
        return node;
    }

    private DeviceTemplateDto template(String name, List<String> modes, List<String> workingStates) {
        DeviceTemplateDto template = new DeviceTemplateDto();
        template.setName(name);
        template.setManifest(DeviceTemplateDto.DeviceManifest.builder()
                .name(name)
                .modes(modes)
                .workingStates(workingStates.stream()
                        .map(state -> DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                                .name(state)
                                .build())
                        .toList())
                .build());
        return template;
    }

    private BoardSemanticSnapshotDto snapshot(
            List<DeviceNodeDto> nodes,
            List<DeviceTemplateDto> templates) {
        return new BoardSemanticSnapshotDto(
                nodes, List.of(), List.of(), List.of(), templates);
    }
}
