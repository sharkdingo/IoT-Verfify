package cn.edu.nju.Iot_Verify.component.fuzz;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class FuzzInputEventTest {

    @Test
    void legacyConstructorAndNullCanonicalSourceDefaultToModelChoice() {
        FuzzInputEvent legacy = new FuzzInputEvent(
                1, FuzzInputEventKind.DEVICE_VARIABLE, "device-1", "temperature", "21");
        FuzzInputEvent canonicalWithNullSource = new FuzzInputEvent(
                2, FuzzInputEventKind.ENVIRONMENT_VALUE, "environment", "humidity", "40", null);

        assertEquals(FuzzInputEventSource.MODEL_CHOICE, legacy.source());
        assertEquals(FuzzInputEventSource.MODEL_CHOICE, canonicalWithNullSource.source());
    }
}
