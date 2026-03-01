package cn.edu.nju.Iot_Verify.service.impl;

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

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class NodeServiceImplSearchNodesTest {

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
    void searchNodes_withKeyword_shouldUseScopedSearchQuery() {
        DeviceNodePo node = DeviceNodePo.builder()
                .id("n1")
                .userId(1L)
                .templateName("Light")
                .label("Living Light")
                .posX(1.0)
                .posY(2.0)
                .state("On")
                .width(110)
                .height(90)
                .build();
        when(nodeRepo.searchByUserIdAndTemplateOrLabel(1L, "light"))
                .thenReturn(List.of(node));

        String result = nodeService.searchNodes(1L, "light");

        verify(nodeRepo).searchByUserIdAndTemplateOrLabel(1L, "light");
        verify(nodeRepo, never()).findByUserId(1L);
        assertTrue(result.contains("\"userId\":1"));
        assertTrue(result.contains("\"label\":\"Living Light\""));
    }

    @Test
    void searchNodes_withoutKeyword_shouldReturnAllUserNodes() {
        when(nodeRepo.findByUserId(2L)).thenReturn(List.of());

        String result = nodeService.searchNodes(2L, " ");

        verify(nodeRepo).findByUserId(2L);
        verify(nodeRepo, never()).searchByUserIdAndTemplateOrLabel(2L, " ");
        assertTrue(!result.isBlank());
    }
}
