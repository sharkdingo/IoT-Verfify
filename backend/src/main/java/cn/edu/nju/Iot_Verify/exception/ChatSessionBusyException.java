package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class ChatSessionBusyException extends ConflictException {
    private final String reasonCode = "CHAT_SESSION_BUSY";
    private final String sessionId;

    public ChatSessionBusyException(String sessionId) {
        super("The assistant is still processing this conversation. Stop it and wait for completion before switching or deleting it.");
        this.sessionId = sessionId;
    }
}
