package cn.edu.nju.Iot_Verify.security;

public final class UserContextHolder {

    private static final ThreadLocal<Long> currentUserId = new ThreadLocal<>();

    private UserContextHolder() {
    }

    public static void setUserId(Long userId) {
        currentUserId.set(userId);
    }

    public static Long getUserId() {
        return currentUserId.get();
    }

    public static void clear() {
        currentUserId.remove();
    }
}
