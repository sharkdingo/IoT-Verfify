package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.Result;
import org.junit.jupiter.api.Test;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class GlobalExceptionHandlerSmvTest {

    @Test
    void handleSmvGenerationException_shouldExposeErrorCategoryInData() {
        GlobalExceptionHandler handler = new GlobalExceptionHandler();
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
}
