package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.ArgumentMatchers.any;

@ExtendWith(MockitoExtension.class)
class NodeServiceImplMutationTest {

    @Mock
    private DeviceNodeRepository nodeRepo;
    @Mock
    private DeviceTemplateService deviceTemplateService;

    private NodeServiceImpl nodeService;

    @BeforeEach
    void setUp() {
        nodeService = new NodeServiceImpl(nodeRepo, deviceTemplateService, new ObjectMapper());
    }

    @Test
    void addNode_whenNoMatchedAndNoFallbackTemplate_shouldThrowBadRequest() {
        when(deviceTemplateService.checkTemplateExists(1L, "unknown")).thenReturn(false);
        when(deviceTemplateService.getAllTemplateNames(1L)).thenReturn(List.of());

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                nodeService.addNode(1L, "unknown", null, null, null, null, null, null));

        assertEquals(400, ex.getCode());
        verify(nodeRepo, never()).save(org.mockito.ArgumentMatchers.any());
    }

    @Test
    void deleteNode_whenNodeMissing_shouldThrowNotFound() {
        when(nodeRepo.findByUserIdAndLabel(1L, "ghost")).thenReturn(Optional.empty());

        ResourceNotFoundException ex = assertThrows(ResourceNotFoundException.class, () ->
                nodeService.deleteNode(1L, "ghost"));

        assertEquals(404, ex.getCode());
    }

    @Test
    void addNode_shouldUseUserScopedIdUniquenessCheck() {
        when(deviceTemplateService.checkTemplateExists(1L, "Light")).thenReturn(true);
        when(nodeRepo.existsByUserIdAndId(1L, "shared-node")).thenReturn(false);

        nodeService.addNode(1L, "Light", "shared-node", 10.0, 20.0, "On", 100, 80);

        verify(nodeRepo).existsByUserIdAndId(1L, "shared-node");
        verify(nodeRepo).save(any(DeviceNodePo.class));
    }
}
