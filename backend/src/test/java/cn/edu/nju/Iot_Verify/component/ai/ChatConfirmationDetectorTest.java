package cn.edu.nju.Iot_Verify.component.ai;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ChatConfirmationDetectorTest {

    private final ChatConfirmationDetector detector = new ChatConfirmationDetector();

    @Test
    void explicitConfirmation_acceptsDirectConfirmation() {
        assertTrue(detector.isExplicitConfirmation("Yes, delete it."));
        assertTrue(detector.isExplicitConfirmation("I confirm deletion of the living-room light"));
        assertTrue(detector.isExplicitConfirmation("\u786e\u8ba4\u5220\u9664\u5ba2\u5385\u706f"));
    }

    @Test
    void explicitConfirmation_rejectsQuestionsNegationAndOrdinaryRequests() {
        assertFalse(detector.isExplicitConfirmation("Do not delete it"));
        assertFalse(detector.isExplicitConfirmation("Why do I need to confirm?"));
        assertFalse(detector.isExplicitConfirmation("\u4e0d\u8981\u5220\u9664"));
        assertFalse(detector.isExplicitConfirmation("\u6709\u51e0\u4e2a\u8bbe\u5907\u3001\u89c4\u5219\u548c\u89c4\u7ea6\uff1f"));
        assertFalse(detector.isExplicitConfirmation("\u6839\u636e\u5f53\u524d\u573a\u666f\u8865\u5168\u591c\u95f4\u5b89\u5168\u573a\u666f"));
    }
}
