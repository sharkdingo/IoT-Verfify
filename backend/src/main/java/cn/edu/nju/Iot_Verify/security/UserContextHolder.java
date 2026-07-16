package cn.edu.nju.Iot_Verify.security;

public final class UserContextHolder {

    private static final ThreadLocal<Long> currentUserId = new ThreadLocal<>();
    private static final ThreadLocal<String> currentChatSessionId = new ThreadLocal<>();
    private static final ThreadLocal<Boolean> destructiveActionConfirmed =
            ThreadLocal.withInitial(() -> false);

    private UserContextHolder() {
    }

    public static void setUserId(Long userId) {
        currentUserId.set(userId);
    }

    public static Long getUserId() {
        return currentUserId.get();
    }

    public static void setChatSessionId(String sessionId) {
        currentChatSessionId.set(sessionId);
    }

    public static String getChatSessionId() {
        return currentChatSessionId.get();
    }

    public static void setDestructiveActionConfirmed(boolean confirmed) {
        destructiveActionConfirmed.set(confirmed);
    }

    public static boolean isDestructiveActionConfirmed() {
        return Boolean.TRUE.equals(destructiveActionConfirmed.get());
    }

    public static void clear() {
        currentUserId.remove();
        currentChatSessionId.remove();
        destructiveActionConfirmed.remove();
    }
}
