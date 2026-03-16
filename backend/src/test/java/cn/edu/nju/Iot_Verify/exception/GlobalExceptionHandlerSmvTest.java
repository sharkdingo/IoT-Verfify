package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.Result;
import org.junit.jupiter.api.Test;
import org.springframework.core.MethodParameter;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.method.annotation.MethodArgumentTypeMismatchException;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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

    @SuppressWarnings("unused")
    private void dummyMethod(Long id) { }
}
