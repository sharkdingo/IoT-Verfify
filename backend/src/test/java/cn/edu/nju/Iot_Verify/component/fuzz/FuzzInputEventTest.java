package cn.edu.nju.Iot_Verify.component.fuzz;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;

class FuzzInputEventTest {

    @Test
    void canonicalConstructorRejectsMissingSource() {
        assertThrows(NullPointerException.class, () -> new FuzzInputEvent(
                2, FuzzInputEventKind.ENVIRONMENT_VALUE, "environment", "humidity", "40", null));
    }
}
