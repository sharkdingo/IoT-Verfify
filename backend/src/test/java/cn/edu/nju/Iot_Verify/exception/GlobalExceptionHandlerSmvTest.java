package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonMappingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;
import org.springframework.core.MethodParameter;
import org.springframework.http.HttpMethod;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.http.converter.HttpMessageNotReadableException;
import org.springframework.mock.http.MockHttpInputMessage;
import org.springframework.web.method.annotation.MethodArgumentTypeMismatchException;
import org.springframework.web.servlet.resource.NoResourceFoundException;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class GlobalExceptionHandlerSmvTest {

    private final GlobalExceptionHandler handler = new GlobalExceptionHandler();

    @Test
    void handleSmvGenerationException_shouldExposeErrorCategoryInData() {
        SmvGenerationException ex = SmvGenerationException.ambiguousDeviceReference(
                "Sensor", java.util.List.of("sensor_1", "sensor_2"));

        ResponseEntity<Result<Map<String, Object>>> response = handler.handleSmvGenerationException(ex);

        assertEquals(HttpStatus.INTERNAL_SERVER_ERROR, response.getStatusCode());
        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals(500, body.getCode());
        assertTrue(body.getMessage().contains("AMBIGUOUS_DEVICE_REFERENCE"));
        assertNotNull(body.getData());
        assertEquals("AMBIGUOUS_DEVICE_REFERENCE", body.getData().get("errorCategory"));
    }

    @Test
    void handleMethodArgumentTypeMismatch_shouldReturn400() throws Exception {
        // Use reflection to get a MethodParameter for the test
        MethodParameter param = new MethodParameter(
                GlobalExceptionHandlerSmvTest.class.getDeclaredMethod("dummyMethod", Long.class), 0);
        MethodArgumentTypeMismatchException ex = new MethodArgumentTypeMismatchException(
                "abc", Long.class, "id", param, new NumberFormatException("For input string: \"abc\""));

        ResponseEntity<Result<Void>> response = handler.handleMethodArgumentTypeMismatch(ex);

        assertEquals(HttpStatus.BAD_REQUEST, response.getStatusCode());
        Result<Void> body = response.getBody();
        assertNotNull(body);
        assertEquals(400, body.getCode());
        assertTrue(body.getMessage().contains("id"));
    }

    @Test
    void handleValidationException_shouldExposeEveryFieldReason() {
        ValidationException ex = new ValidationException(Map.of(
                "nodes[0].id", "Conflicts with a generated model marker",
                "rules[1].conditions", "Rule trigger is invalid"));

        ResponseEntity<Result<Map<String, Object>>> response = handler.handleValidationException(ex);

        assertEquals(HttpStatus.UNPROCESSABLE_ENTITY, response.getStatusCode());
        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals(422, body.getCode());
        assertNotNull(body.getData());
        @SuppressWarnings("unchecked")
        Map<String, String> errors = (Map<String, String>) body.getData().get("errors");
        assertEquals(2, errors.size());
        assertEquals("Rule trigger is invalid", errors.get("rules[1].conditions"));
    }

    @Test
    void handleBoardReplacementStale_shouldExposeReasonAndFreshPreview() {
        BoardReplacementPreviewDto preview = BoardReplacementPreviewDto.builder()
                .impactToken("fresh-token")
                .deviceCount(2)
                .environmentVariableCount(1)
                .ruleCount(3)
                .specificationCount(4)
                .build();

        ResponseEntity<Result<Map<String, Object>>> response =
                handler.handleBoardReplacementStaleException(
                        new BoardReplacementStaleException(preview));

        assertEquals(HttpStatus.CONFLICT, response.getStatusCode());
        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals(409, body.getCode());
        assertEquals("BOARD_REPLACEMENT_STALE", body.getData().get("reasonCode"));
        assertEquals(preview, body.getData().get("currentPreview"));
    }

    @Test
    void handleHttpMessageNotReadable_shouldReturn400() {
        HttpMessageNotReadableException ex = new HttpMessageNotReadableException("bad json");

        ResponseEntity<Result<Map<String, Object>>> response = handler.handleHttpMessageNotReadableException(ex);

        assertEquals(HttpStatus.BAD_REQUEST, response.getStatusCode());
        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals(400, body.getCode());
        assertEquals("Malformed request body", body.getMessage());
        assertEquals(Map.of("request", "Malformed JSON syntax"), body.getData().get("errors"));
    }

    @Test
    void handleHttpMessageNotReadable_shouldIdentifyUnknownFieldWithoutEchoingItsValue() throws Exception {
        ObjectMapper mapper = new ObjectMapper().enable(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES);
        JsonMappingException cause = assertThrows(JsonMappingException.class,
                () -> mapper.readValue("{\"known\":\"ok\",\"unexpected\":\"secret\"}", StrictInput.class));
        HttpMessageNotReadableException ex = new HttpMessageNotReadableException(
                "bad json", cause, new MockHttpInputMessage(new byte[0]));

        ResponseEntity<Result<Map<String, Object>>> response = handler.handleHttpMessageNotReadableException(ex);

        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals("Unknown field 'unexpected'", body.getMessage());
        assertEquals(Map.of("unexpected", "Unknown field"), body.getData().get("errors"));
        assertTrue(!body.getMessage().contains("secret"));
    }

    @Test
    void handleHttpMessageNotReadable_shouldIdentifyNestedTypeMismatchPath() throws Exception {
        ObjectMapper mapper = new ObjectMapper();
        JsonMappingException cause = assertThrows(JsonMappingException.class,
                () -> mapper.readValue("{\"items\":[{\"count\":{}}]}", NestedInput.class));
        HttpMessageNotReadableException ex = new HttpMessageNotReadableException(
                "bad json", cause, new MockHttpInputMessage(new byte[0]));

        ResponseEntity<Result<Map<String, Object>>> response = handler.handleHttpMessageNotReadableException(ex);

        Result<Map<String, Object>> body = response.getBody();
        assertNotNull(body);
        assertEquals(
                "Invalid JSON value at 'items[0].count': Value does not match the declared field type",
                body.getMessage());
        assertEquals(
                Map.of("items[0].count", "Value does not match the declared field type"),
                body.getData().get("errors"));
    }

    @Test
    void handleNoResourceFound_shouldReturn404() {
        NoResourceFoundException ex = new NoResourceFoundException(HttpMethod.GET, "api/board/active");

        ResponseEntity<Result<Void>> response = handler.handleNoResourceFoundException(ex);

        assertEquals(HttpStatus.NOT_FOUND, response.getStatusCode());
        Result<Void> body = response.getBody();
        assertNotNull(body);
        assertEquals(404, body.getCode());
        assertTrue(body.getMessage().contains("api/board/active"));
    }

    @SuppressWarnings("unused")
    private void dummyMethod(Long id) { }

    private record StrictInput(String known) {}
    private record NestedInput(java.util.List<NestedItem> items) {}
    private record NestedItem(Integer count) {}
}
