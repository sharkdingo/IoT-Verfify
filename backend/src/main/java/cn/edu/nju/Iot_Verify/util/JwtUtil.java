package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.configure.JwtConfig;
import cn.edu.nju.Iot_Verify.configure.ProductionSafetyCheck;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import io.jsonwebtoken.Claims;
import io.jsonwebtoken.ExpiredJwtException;
import io.jsonwebtoken.JwtException;
import io.jsonwebtoken.Jwts;
import io.jsonwebtoken.SignatureAlgorithm;
import io.jsonwebtoken.security.Keys;
import jakarta.annotation.PostConstruct;
import org.springframework.core.env.Environment;
import org.springframework.stereotype.Component;

import lombok.extern.slf4j.Slf4j;

import javax.crypto.SecretKey;
import java.nio.charset.StandardCharsets;
import java.util.Date;

@Slf4j
@Component
public class JwtUtil {

    private static final String INSECURE_DEFAULT_PREFIX = "iot-verify-secret-key";

    private final JwtConfig config;
    private final Environment environment;

    private SecretKey signingKey;

    public JwtUtil(JwtConfig config, Environment environment) {
        this.config = config;
        this.environment = environment;
    }

    @PostConstruct
    public void init() {
        byte[] keyBytes = config.getSecret().getBytes(StandardCharsets.UTF_8);
        this.signingKey = Keys.hmacShaKeyFor(keyBytes);

        if (config.getSecret().startsWith(INSECURE_DEFAULT_PREFIX) && ProductionSafetyCheck.isProductionProfile(environment)) {
            log.warn("JWT secret is still using the insecure default value — "
                    + "configure jwt.secret (or JWT_SECRET env) for production!");
        }
    }

    /* The production-profile decision has one owner; see ProductionSafetyCheck.isProductionProfile. This class
       duplicated the profile set, the case fold and the loop, and the fold was the part that had drifted. */

    private SecretKey getSigningKey() {
        return signingKey;
    }

    public String generateToken(Long userId, String phone) {
        Date now = new Date();
        Date expiryDate = new Date(now.getTime() + config.getExpiration());

        return Jwts.builder()
                .setSubject(String.valueOf(userId))
                .claim("phone", phone)
                .setIssuedAt(now)
                .setExpiration(expiryDate)
                .signWith(getSigningKey(), SignatureAlgorithm.HS256)
                .compact();
    }

    public Long getUserIdFromToken(String token) {
        Claims claims = parseClaims(token);
        try {
            return Long.parseLong(claims.getSubject());
        } catch (NumberFormatException e) {
            throw new UnauthorizedException("Invalid token: malformed user ID");
        }
    }
    /**
     * 获取Token剩余过期时间（秒）
     * 用于黑名单设置合理的TTL
     */
    public long getExpirationSeconds(String token) {
        Claims claims = parseClaims(token);
        long expMillis = claims.getExpiration().getTime();
        long nowMillis = System.currentTimeMillis();
        return Math.max(60, (expMillis - nowMillis) / 1000);
    }

    public boolean validateToken(String token) {
        try {
            Claims claims = parseClaims(token);
            return !claims.getExpiration().before(new Date());
        } catch (ExpiredJwtException e) {
            return false;
        } catch (JwtException e) {
            return false;
        } catch (Exception e) {
            return false;
        }
    }

    /* No throwing `validateTokenOrThrow` variant: only the boolean `validateToken` above has callers. */
    private Claims parseClaims(String token) {
        return Jwts.parserBuilder()
                .setSigningKey(getSigningKey())
                .build()
                .parseClaimsJws(token)
                .getBody();
    }
}
