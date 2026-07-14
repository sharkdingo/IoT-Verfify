package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
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
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ManageEnvironmentToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ObjectMapper objectMapper;
    private ManageEnvironmentTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new ManageEnvironmentTool(boardStorageService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void listExplainsThatValuesAndLabelsAreModelInputs() throws Exception {
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of(
                new BoardEnvironmentVariableDto("temperature", "22", "trusted", "private")));

        JsonNode result = objectMapper.readTree(tool.execute("{\"action\":\"list\"}"));

        assertEquals("listed", result.path("operation").asText());
        assertFalse(result.path("changesApplied").asBoolean());
        assertEquals("temperature", result.path("environmentVariables").get(0).path("name").asText());
        assertTrue(result.path("modelMeaning").path("value").asText().contains("not a live sensor"));
        assertTrue(result.path("modelMeaning").path("privacy").asText().contains("does not enforce"));
    }

    @Test
    @SuppressWarnings("unchecked")
    void setPreservesUnspecifiedFieldsAndReturnsBeforeAfter() throws Exception {
        List<BoardEnvironmentVariableDto> initial = List.of(
                new BoardEnvironmentVariableDto("temperature", "22", "trusted", "private"));
        when(boardStorageService.updateEnvironmentVariables(eq(1L), any())).thenAnswer(invocation -> {
            UnaryOperator<List<BoardEnvironmentVariableDto>> mutator = invocation.getArgument(1);
            return mutator.apply(initial);
        });

        JsonNode result = objectMapper.readTree(tool.execute(
                "{\"action\":\"set\",\"name\":\"temperature\",\"value\":\"27\"}"));

        assertEquals("updated", result.path("operation").asText());
        assertTrue(result.path("changesApplied").asBoolean());
        assertEquals("22", result.path("previousVariable").path("value").asText());
        assertEquals("27", result.path("currentVariable").path("value").asText());
        assertEquals("trusted", result.path("currentVariable").path("trust").asText());
        assertEquals("private", result.path("currentVariable").path("privacy").asText());
        assertTrue(result.path("unspecifiedFieldsPreserved").toString().contains("trust"));
    }

    @Test
    @SuppressWarnings("unchecked")
    void resetReportsActualTemplateDefaultsReturnedByService() throws Exception {
        List<BoardEnvironmentVariableDto> initial = List.of(
                new BoardEnvironmentVariableDto("temperature", "27", "untrusted", "private"));
        when(boardStorageService.updateEnvironmentVariables(eq(1L), any())).thenAnswer(invocation -> {
            UnaryOperator<List<BoardEnvironmentVariableDto>> mutator = invocation.getArgument(1);
            List<BoardEnvironmentVariableDto> submitted = mutator.apply(initial);
            assertEquals(null, submitted.get(0).getValue());
            return List.of(new BoardEnvironmentVariableDto(
                    "temperature", "0", "trusted", "public"));
        });

        JsonNode result = objectMapper.readTree(tool.execute(
                "{\"action\":\"reset\",\"name\":\"temperature\"}"));

        assertEquals("defaults_restored", result.path("operation").asText());
        assertTrue(result.path("changesApplied").asBoolean());
        assertTrue(result.path("defaultsRestored").asBoolean());
        assertEquals("27", result.path("previousVariable").path("value").asText());
        assertEquals("0", result.path("currentVariable").path("value").asText());
        assertEquals("trusted", result.path("currentVariable").path("trust").asText());
    }

    @Test
    void setRejectsAmbiguousNullInsteadOfTreatingItAsReset() throws Exception {
        JsonNode result = objectMapper.readTree(tool.execute(
                "{\"action\":\"set\",\"name\":\"temperature\",\"value\":null}"));

        assertEquals("VALIDATION_ERROR", result.path("errorCode").asText());
        assertTrue(result.path("error").asText().contains("use reset"));
    }

    @Test
    void actionSpecificFieldsAreRejectedInsteadOfIgnored() throws Exception {
        JsonNode listWithName = objectMapper.readTree(tool.execute(
                "{\"action\":\"list\",\"name\":\"temperature\"}"));
        JsonNode resetWithValue = objectMapper.readTree(tool.execute(
                "{\"action\":\"reset\",\"name\":\"temperature\",\"value\":\"27\"}"));

        assertEquals("VALIDATION_ERROR", listWithName.path("errorCode").asText());
        assertTrue(listWithName.path("error").asText().contains("name"));
        assertEquals("VALIDATION_ERROR", resetWithValue.path("errorCode").asText());
        assertTrue(resetWithValue.path("error").asText().contains("value"));
        verifyNoInteractions(boardStorageService);
    }
}
