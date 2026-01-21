package cn.edu.nju.Iot_Verify.service;

/**
 * Token黑名单服务接口
 * 
 * 用于登出后使Token失效，支持内存和Redis两种实现
 * 
 * 未来添加Redis后，实现类改为:
 * {@code @Service public class RedisTokenBlacklistService implements TokenBlacklistService}
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
