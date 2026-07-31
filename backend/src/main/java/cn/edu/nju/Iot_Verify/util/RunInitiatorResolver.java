package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;

/** Resolves run ownership while the initiating request still owns its chat execution context. */
public final class RunInitiatorResolver {

    private RunInitiatorResolver() {
    }

    public static RunInitiator current() {
        String chatExecutionId = UserContextHolder.getChatExecutionId();
        return chatExecutionId == null || chatExecutionId.isBlank()
                ? RunInitiator.USER
                : RunInitiator.AI_ASSISTANT;
    }
}
