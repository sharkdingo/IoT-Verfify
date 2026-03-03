package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.NodeService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Regression tests for AddNodeTool numeric parameter parsing.
 * Ensures null JSON values, non-numeric strings, and absent fields
 * all result in null being passed to NodeService (triggering default values).
 */
@ExtendWith(MockitoExtension.class)
class AddNodeToolNullParamsTest {

    @Mock
    private NodeService nodeService;

    private ObjectMapper objectMapper;
    private AddNodeTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new AddNodeTool(nodeService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_withNullJsonValues_passesNullToService() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull()))
                .thenReturn("Created device successfully: ac_1.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\",\"x\":null,\"y\":null,\"w\":null,\"h\":null}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull());
        assertTrue(result.contains("ac_1"));
    }

    @Test
    void execute_withNonNumericStrings_passesNullToService() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull()))
                .thenReturn("Created device successfully: ac_2.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\",\"x\":\"abc\",\"y\":\"def\",\"w\":\"xyz\",\"h\":\"!\"}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull());
        assertTrue(result.contains("ac_2"));
    }

    @Test
    void execute_withAbsentFields_passesNullToService() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull()))
                .thenReturn("Created device successfully: ac_3.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\"}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull());
        assertTrue(result.contains("ac_3"));
    }

    @Test
    void execute_withValidNumbers_passesValuesToService() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                eq(100.5), eq(200.0), isNull(), eq(120), eq(80)))
                .thenReturn("Created device successfully: ac_4.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\",\"x\":100.5,\"y\":200,\"w\":120,\"h\":80}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                eq(100.5), eq(200.0), isNull(), eq(120), eq(80));
        assertTrue(result.contains("ac_4"));
    }

    @Test
    void execute_withEmptyStringValues_passesNullToService() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull()))
                .thenReturn("Created device successfully: ac_5.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\",\"x\":\"\",\"y\":\"\"}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                isNull(), isNull(), isNull(), isNull(), isNull());
        assertTrue(result.contains("ac_5"));
    }

    @Test
    void execute_withNumericStrings_parsesCorrectly() throws Exception {
        when(nodeService.addNode(eq(1L), eq("Air Conditioner"), isNull(),
                eq(150.0), eq(250.0), isNull(), eq(110), eq(90)))
                .thenReturn("Created device successfully: ac_6.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\",\"x\":\"150\",\"y\":\"250\",\"w\":\"110\",\"h\":\"90\"}");

        verify(nodeService).addNode(eq(1L), eq("Air Conditioner"), isNull(),
                eq(150.0), eq(250.0), isNull(), eq(110), eq(90));
        assertTrue(result.contains("ac_6"));
    }
}
