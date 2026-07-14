package cn.edu.nju.Iot_Verify.component.ai;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ChatIntentRouterTest {

    private final ChatIntentRouter router = new ChatIntentRouter();

    @Test
    void route_shouldUseToolLoopForActionablePlatformRequests() {
        assertToolLoop("please list rules");
        assertToolLoop("run formal verification on the current model");
        assertToolLoop("please call fix_violation for trace 42");
        assertToolLoop("please create a rule that turns on the purifier when PM2.5 is high");
        assertToolLoop("请查看当前画布概览");
        assertToolLoop("帮我推荐几条当前设备的安全规约");
        assertToolLoop("如果我打开空调，当前系统会触发哪些规则吗");
    }

    @Test
    void route_shouldKeepConceptualAndContentGenerationRequestsConversational() {
        assertConversation("explain what a rule is");
        assertConversation("what is model checking?");
        assertConversation("list best practices for Java streams");
        assertConversation("请解释规则和规约的区别");
        assertConversation("请写一段 Python 脚本模拟温度传感器数据上报逻辑");
    }

    @Test
    void explicitConfirmation_shouldReenterToolLoopButRejectQuestionsAndNegation() {
        assertTrue(router.isExplicitConfirmation("Yes, delete it."));
        assertTrue(router.isExplicitConfirmation("I confirm deletion of the living-room light"));
        assertTrue(router.isExplicitConfirmation("\u786e\u8ba4\u5220\u9664\u5ba2\u5385\u706f"));
        assertToolLoop("yes");
        assertToolLoop("\u786e\u8ba4\u5220\u9664");

        assertFalse(router.isExplicitConfirmation("Do not delete it"));
        assertFalse(router.isExplicitConfirmation("Why do I need to confirm?"));
        assertFalse(router.isExplicitConfirmation("\u4e0d\u8981\u5220\u9664"));
        assertFalse(router.isExplicitConfirmation("\u4e3a\u4ec0\u4e48\u9700\u8981\u786e\u8ba4\uff1f"));
    }

    private void assertToolLoop(String content) {
        assertTrue(router.route(content).requiresToolLoop(), content);
    }

    private void assertConversation(String content) {
        assertFalse(router.route(content).requiresToolLoop(), content);
    }
}
