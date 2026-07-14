package cn.edu.nju.Iot_Verify.dto.fix;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PreferredRangeSelectionTest {

    @Test
    void targetIdFor_includesTraceScopeAndStaysOpaque() {
        String firstTraceTarget = PreferredRangeSelection.targetIdFor(10L, 0, 1);
        String secondTraceTarget = PreferredRangeSelection.targetIdFor(11L, 0, 1);

        assertTrue(PreferredRangeSelection.isValidTargetId(firstTraceTarget));
        assertTrue(PreferredRangeSelection.isValidTargetId(secondTraceTarget));
        assertFalse(firstTraceTarget.contains("r0"));
        assertFalse(firstTraceTarget.contains("c1"));
        assertNotEquals(firstTraceTarget, secondTraceTarget);
    }
}
