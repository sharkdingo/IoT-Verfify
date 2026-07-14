package cn.edu.nju.Iot_Verify.security;

import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import cn.edu.nju.Iot_Verify.util.JwtUtil;
import jakarta.servlet.FilterChain;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.security.authentication.UsernamePasswordAuthenticationToken;
import org.springframework.security.core.context.SecurityContextHolder;
import org.springframework.lang.NonNull;
import org.springframework.stereotype.Component;
import org.springframework.util.StringUtils;
import org.springframework.web.filter.OncePerRequestFilter;

import java.io.IOException;
import java.util.Collections;

@Slf4j
@Component
@RequiredArgsConstructor
public class JwtAuthenticationFilter extends OncePerRequestFilter {

    private final JwtUtil jwtUtil;
    private final TokenBlacklistService tokenBlacklistService;
    private final UserRepository userRepository;

    @Override
    protected void doFilterInternal(@NonNull HttpServletRequest request, @NonNull HttpServletResponse response, @NonNull FilterChain filterChain)
            throws ServletException, IOException {

        String token = extractToken(request);

        // Only a valid, non-blacklisted token establishes authentication. A blacklisted
        // token proceeds unauthenticated (falls through, no context set).
        if (StringUtils.hasText(token) && jwtUtil.validateToken(token)
                && !tokenBlacklistService.isBlacklisted(token)) {
            try {
                Long userId = jwtUtil.getUserIdFromToken(token);
                if (userRepository.existsById(userId)) {
                    UsernamePasswordAuthenticationToken authentication =
                            new UsernamePasswordAuthenticationToken(userId, null, Collections.emptyList());
                    SecurityContextHolder.getContext().setAuthentication(authentication);
                    // Also set UserContextHolder for AI tools
                    UserContextHolder.setUserId(userId);
                } else {
                    log.debug("JWT references deleted or unknown user {}, ignoring authentication", userId);
                }
            } catch (Exception e) {
                // Token validation failed, continue without authentication
            }
        }

        try {
            filterChain.doFilter(request, response);
        } finally {
            // UserContextHolder is a ThreadLocal on a reused Tomcat worker thread. If we
            // never cleared it, a later request arriving WITHOUT a valid token (so the
            // block above neither sets nor clears it) would still observe the previous
            // request's userId — a cross-user leak on the AI-tool path that reads
            // UserContextHolder. SecurityContextHolder is cleared by Spring Security's own
            // filter; this ThreadLocal is ours to clean up.
            UserContextHolder.clear();
        }
    }

    @Override
    protected boolean shouldNotFilterAsyncDispatch() {
        return false;
    }

    private String extractToken(HttpServletRequest request) {
        String bearerToken = request.getHeader("Authorization");
        if (StringUtils.hasText(bearerToken) && bearerToken.startsWith("Bearer ")) {
            return bearerToken.substring(7);
        }
        return null;
    }
}
