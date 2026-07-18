package cn.edu.nju.Iot_Verify.security;

public final class UserContextHolder {

    private static final ThreadLocal<Long> currentUserId = new ThreadLocal<>();
    private static final ThreadLocal<String> currentChatSessionId = new ThreadLocal<>();
    private static final ThreadLocal<String> confirmedProtectedActionKind = new ThreadLocal<>();

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
        setConfirmedProtectedActionKind(confirmed ? "DESTRUCTIVE" : null);
    }

    public static boolean isDestructiveActionConfirmed() {
        return isProtectedActionConfirmed("DESTRUCTIVE");
    }

    public static void setSceneReplacementConfirmed(boolean confirmed) {
        setConfirmedProtectedActionKind(confirmed ? "SCENE_REPLACEMENT" : null);
    }

    public static boolean isSceneReplacementConfirmed() {
        return isProtectedActionConfirmed("SCENE_REPLACEMENT");
    }

    public static void setDefaultTemplateResetConfirmed(boolean confirmed) {
        setConfirmedProtectedActionKind(confirmed ? "DEFAULT_TEMPLATE_RESET" : null);
    }

    public static boolean isDefaultTemplateResetConfirmed() {
        return isProtectedActionConfirmed("DEFAULT_TEMPLATE_RESET");
    }

    public static void setConfirmedProtectedActionKind(String kind) {
        if (kind == null || kind.isBlank()) {
            confirmedProtectedActionKind.remove();
            return;
        }
        confirmedProtectedActionKind.set(kind.trim());
    }

    public static boolean isProtectedActionConfirmed(String kind) {
        return kind != null && kind.equals(confirmedProtectedActionKind.get());
    }

    public static void clear() {
        currentUserId.remove();
        currentChatSessionId.remove();
        confirmedProtectedActionKind.remove();
    }
}
