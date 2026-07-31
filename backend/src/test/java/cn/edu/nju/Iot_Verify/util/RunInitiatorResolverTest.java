package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class RunInitiatorResolverTest {

    @AfterEach
    void clearContext() {
        UserContextHolder.clear();
    }

    @Test
    void currentWithoutChatExecutionIsUserInitiated() {
        assertEquals(RunInitiator.USER, RunInitiatorResolver.current());
    }

    @Test
    void currentWithChatExecutionIsAssistantInitiated() {
        UserContextHolder.setChatExecutionId("execution-1");

        assertEquals(RunInitiator.AI_ASSISTANT, RunInitiatorResolver.current());
    }
}
