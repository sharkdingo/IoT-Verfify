package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class NodeServiceImplSearchNodesTest {

    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private DeviceTemplateService deviceTemplateService;

    private NodeServiceImpl nodeService;

    @BeforeEach
    void setUp() {
        nodeService = new NodeServiceImpl(boardStorageService, deviceTemplateService, new ObjectMapper());
    }

    @Test
    void searchNodes_withKeyword_shouldUseScopedSearchQuery() {
        DeviceNodeDto light = node("n1", "Living Light", "Light");
        DeviceNodeDto door = node("n2", "Front Door", "Door");
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(light, door));

        List<DeviceNodeDto> result = nodeService.searchNodes(1L, "light");

        verify(boardStorageService).getNodes(1L);
        assertEquals(List.of(light), result);
    }

    @Test
    void searchNodes_withoutKeyword_shouldReturnAllUserNodes() {
        DeviceNodeDto light = node("n1", "Living Light", "Light");
        when(boardStorageService.getNodes(2L)).thenReturn(List.of(light));

        List<DeviceNodeDto> result = nodeService.searchNodes(2L, " ");

        verify(boardStorageService).getNodes(2L);
        assertEquals(List.of(light), result);
    }

    private DeviceNodeDto node(String id, String label, String templateName) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setLabel(label);
        node.setTemplateName(templateName);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(1.0);
        position.setY(2.0);
        node.setPosition(position);
        node.setState("On");
        node.setWidth(176);
        node.setHeight(128);
        return node;
    }
}
