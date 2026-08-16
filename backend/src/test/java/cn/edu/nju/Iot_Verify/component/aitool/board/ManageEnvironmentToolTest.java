package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.dto.board.EnvironmentMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableUpdateRequestDto;
import cn.edu.nju.Iot_Verify.exception.EnvironmentVariableConflictException;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.verify;
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
        List<BoardEnvironmentVariableDto> saved = List.of(
                new BoardEnvironmentVariableDto("temperature", "27", "trusted", "private"));
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(initial);
        when(boardStorageService.saveEnvironmentVariables(eq(1L), any()))
                .thenReturn(EnvironmentMutationResultDto.builder().environmentVariables(saved).build());

        JsonNode result = objectMapper.readTree(tool.execute(
                "{\"action\":\"set\",\"name\":\"temperature\",\"value\":\"27\"}"));

        assertEquals("updated", result.path("operation").asText());
        assertTrue(result.path("changesApplied").asBoolean());
        assertEquals("22", result.path("previousVariable").path("value").asText());
        assertEquals("27", result.path("currentVariable").path("value").asText());
        assertEquals("trusted", result.path("currentVariable").path("trust").asText());
        assertEquals("private", result.path("currentVariable").path("privacy").asText());
        assertTrue(result.path("unspecifiedFieldsPreserved").toString().contains("trust"));

        /*
         * The precondition is the point of this path, so assert the request carried it. `expected` must be
         * the COMPLETE row as read - not just the field being written - or a concurrent edit to `trust`
         * would be overwritten by the value this call remembered.
         */
        ArgumentCaptor<List<EnvironmentVariableUpdateRequestDto>> captor =
                ArgumentCaptor.forClass(List.class);
        verify(boardStorageService).saveEnvironmentVariables(eq(1L), captor.capture());
        EnvironmentVariableUpdateRequestDto sent = captor.getValue().get(0);
        assertEquals("temperature", sent.getName());
        assertEquals("22", sent.getExpected().getValue());
        assertEquals("trusted", sent.getExpected().getTrust());
        assertEquals("private", sent.getExpected().getPrivacy());
        // Only the supplied field is desired; the service carries the rest over from `expected`.
        assertEquals("27", sent.getDesired().getValue());
        assertNull(sent.getDesired().getTrust());
        assertNull(sent.getDesired().getPrivacy());
    }

    /**
     * A stale baseline is reported as a recoverable conflict, not as a server fault or a flat business error.
     *
     * <p>Before compare-and-set this tool was last-writer-wins on a row the UI guards with a 409: the user
     * edits a variable's value while the assistant holds a snapshot from an earlier turn, the assistant
     * writes {@code trust}, and the user's value is silently reverted because the unspecified fields come
     * from what the assistant remembered.
     *
     * <p>The generic {@code BaseException} branch would already produce a 409, so what this pins is the part
     * the model needs to recover: the reason code, the variable's current row, and the instruction not to
     * repeat the same write. Without those a conflict is indistinguishable from any other business error.
     */
    @Test
    void setRejectsAStaleBaselineWithTheCurrentRowAndRecoveryGuidance() throws Exception {
        BoardEnvironmentVariableDto asRead =
                new BoardEnvironmentVariableDto("temperature", "22", "trusted", "private");
        BoardEnvironmentVariableDto asItNowIs =
                new BoardEnvironmentVariableDto("temperature", "30", "trusted", "private");
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of(asRead));
        when(boardStorageService.saveEnvironmentVariables(eq(1L), any()))
                .thenThrow(new EnvironmentVariableConflictException("temperature", asItNowIs));

        JsonNode result = objectMapper.readTree(tool.execute(
                "{\"action\":\"set\",\"name\":\"temperature\",\"trust\":\"untrusted\"}"));

        assertEquals("ENVIRONMENT_VARIABLE_STALE", result.path("errorCode").asText());
        assertEquals(409, result.path("status").asInt());
        // The current row, so the model can decide whether its intent still applies to 30 rather than 22.
        assertEquals("30", result.path("currentVariable").path("value").asText());
        assertTrue(result.path("guidance").asText().contains("action=list"));
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
