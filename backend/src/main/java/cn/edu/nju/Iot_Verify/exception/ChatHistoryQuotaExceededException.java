package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class ChatHistoryQuotaExceededException extends BaseException {

    private final long messageCount;
    private final int maxMessagesPerSession;
    private final long requiredTurnCapacity;

    public ChatHistoryQuotaExceededException(
            long messageCount,
            int maxMessagesPerSession,
            long requiredTurnCapacity) {
        super(429, "This conversation is too close to its stored-message limit for another complete AI turn. "
                + "Start a new conversation or delete this conversation when it is no longer needed.");
        this.messageCount = messageCount;
        this.maxMessagesPerSession = maxMessagesPerSession;
        this.requiredTurnCapacity = requiredTurnCapacity;
    }
}
