package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.configure.JwtConfig;
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
import java.util.Set;

@Slf4j
@Component
public class JwtUtil {

    private static final String INSECURE_DEFAULT_PREFIX = "iot-verify-secret-key";
    private static final Set<String> PRODUCTION_PROFILES = Set.of("prod", "production");

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

        if (config.getSecret().startsWith(INSECURE_DEFAULT_PREFIX) && isProductionProfile()) {
            log.warn("JWT secret is still using the insecure default value — "
                    + "configure jwt.secret (or JWT_SECRET env) for production!");
        }
    }

    private boolean isProductionProfile() {
        for (String profile : environment.getActiveProfiles()) {
            if (PRODUCTION_PROFILES.contains(profile.toLowerCase())) {
                return true;
            }
        }
        return false;
    }

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

    public String getPhoneFromToken(String token) {
        Claims claims = parseClaims(token);
        return claims.get("phone", String.class);
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

    public void validateTokenOrThrow(String token) {
        try {
            Claims claims = parseClaims(token);
            if (claims.getExpiration().before(new Date())) {
                throw UnauthorizedException.expiredToken();
            }
        } catch (ExpiredJwtException e) {
            throw UnauthorizedException.expiredToken();
        } catch (JwtException e) {
            throw UnauthorizedException.invalidToken();
        } catch (UnauthorizedException e) {
            throw e;
        } catch (Exception e) {
            throw UnauthorizedException.invalidToken();
        }
    }

    private Claims parseClaims(String token) {
        return Jwts.parserBuilder()
                .setSigningKey(getSigningKey())
                .build()
                .parseClaimsJws(token)
                .getBody();
    }
}
