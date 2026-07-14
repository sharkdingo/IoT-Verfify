package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

/** Public response-contract tests for search_devices. */
class SearchNodeToolNormalizeResultTest {

    private final ObjectMapper objectMapper = new ObjectMapper();
    private final NodeService nodeService = mock(NodeService.class);
    private final SearchNodeTool tool = new SearchNodeTool(nodeService, objectMapper);

    @AfterEach
    void clearUser() {
        UserContextHolder.clear();
    }

    @Test
    void emptyResult_explainsThatNoDeviceMatched() throws Exception {
        UserContextHolder.setUserId(1L);
        when(nodeService.searchNodes(1L, "light")).thenReturn(List.of());

        JsonNode result = objectMapper.readTree(tool.execute("{\"keyword\":\" light \"}"));

        assertEquals(0, result.path("count").asInt());
        assertTrue(result.path("devices").isArray());
        assertTrue(result.path("devices").isEmpty());
        assertTrue(result.path("message").asText().contains("matched"));
    }

    @Test
    void nonEmptyResult_returnsStructuredDeviceSnapshots() throws Exception {
        UserContextHolder.setUserId(1L);
        DeviceNodeDto device = new DeviceNodeDto();
        device.setId("light_1");
        device.setLabel("Kitchen Light");
        device.setTemplateName("Light");
        when(nodeService.searchNodes(1L, "")).thenReturn(List.of(device));

        JsonNode result = objectMapper.readTree(tool.execute("{}"));

        assertEquals(1, result.path("count").asInt());
        assertEquals("light_1", result.path("devices").get(0).path("id").asText());
        assertEquals("Kitchen Light", result.path("devices").get(0).path("label").asText());
    }

    @Test
    void wrongTypeOrUnknownSearchOption_isRejectedBeforeSearch() throws Exception {
        UserContextHolder.setUserId(1L);

        JsonNode wrongType = objectMapper.readTree(tool.execute("{\"keyword\":42}"));
        JsonNode unknown = objectMapper.readTree(tool.execute("{\"query\":\"light\"}"));

        assertEquals("VALIDATION_ERROR", wrongType.path("errorCode").asText());
        assertEquals("VALIDATION_ERROR", unknown.path("errorCode").asText());
        verify(nodeService, never()).searchNodes(1L, "42");
        verify(nodeService, never()).searchNodes(1L, "");
    }
}
