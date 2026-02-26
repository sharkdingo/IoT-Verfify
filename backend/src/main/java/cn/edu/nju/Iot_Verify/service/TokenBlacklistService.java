package cn.edu.nju.Iot_Verify.service;

/**
 * Token黑名单服务接口
 *
 * 用于登出后使Token失效，当前由 Redis 实现（RedisTokenBlacklistService）
 */
public interface TokenBlacklistService {

    /**
     * 将Token加入黑名单
     *
     * @param token JWT token
     * @param expirationSeconds 剩余过期时间（秒），用于设置合理的过期时间
     */
    void blacklist(String token, long expirationSeconds);

    /**
     * 检查Token是否在黑名单中
     *
     * @param token JWT token
     * @return true 表示Token已失效
     */
    boolean isBlacklisted(String token);
}
