package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import io.jsonwebtoken.Claims;
import io.jsonwebtoken.ExpiredJwtException;
import io.jsonwebtoken.JwtException;
import io.jsonwebtoken.Jwts;
import io.jsonwebtoken.SignatureAlgorithm;
import io.jsonwebtoken.security.Keys;
import jakarta.annotation.PostConstruct;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Component;

import javax.crypto.SecretKey;
import java.nio.charset.StandardCharsets;
import java.util.Date;

@Component
public class JwtUtil {

    @Value("${jwt.secret:iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256-algorithm}")
    private String secret;

    @Value("${jwt.expiration:86400000}")
    private Long expiration;

    private SecretKey signingKey;

    @PostConstruct
    public void init() {
        byte[] keyBytes = secret.getBytes(StandardCharsets.UTF_8);
        this.signingKey = Keys.hmacShaKeyFor(keyBytes);
    }

    private SecretKey getSigningKey() {
        return signingKey;
    }

    public String generateToken(Long userId, String phone) {
        Date now = new Date();
        Date expiryDate = new Date(now.getTime() + expiration);

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
        return Long.parseLong(claims.getSubject());
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
