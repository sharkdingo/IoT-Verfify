package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import com.fasterxml.jackson.databind.node.ObjectNode;
import org.springframework.stereotype.Component;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/**
 * Session-scoped, single-use authorization for destructive AI tool calls.
 *
 * <p>The model only receives an opaque token. The server binds that token to the authenticated
 * user, chat session, tool, target, and a canonical digest of the exact preview. A successful
 * consume removes the pending action atomically, so one user confirmation cannot authorize a
 * second protected mutation in the same tool-planning turn.
 */
@Component
public class AiDestructiveActionGuard {

    private static final Duration TOKEN_TTL = Duration.ofMinutes(15);
    private static final int TOKEN_BYTES = 32;

    private final ObjectMapper objectMapper;
    private final SecureRandom secureRandom = new SecureRandom();
    private final ConcurrentMap<SessionScope, PendingAction> pendingBySession =
            new ConcurrentHashMap<>();

    public AiDestructiveActionGuard(ObjectMapper objectMapper) {
        this.objectMapper = objectMapper;
    }

    public String issue(Long userId,
                        String toolName,
                        String targetKey,
                        Object previewSnapshot,
                        String domainImpactToken) {
        SessionScope scope = currentScope(userId);
        byte[] tokenBytes = new byte[TOKEN_BYTES];
        secureRandom.nextBytes(tokenBytes);
        String token = Base64.getUrlEncoder().withoutPadding().encodeToString(tokenBytes);
        PendingAction pending = new PendingAction(
                token,
                requireText(toolName, "toolName"),
                requireText(targetKey, "targetKey"),
                digest(previewSnapshot),
                domainImpactToken,
                Instant.now().plus(TOKEN_TTL));
        pendingBySession.put(scope, pending);
        removeExpiredEntries();
        return token;
    }

    public ConsumeResult consume(Long userId,
                                 String toolName,
                                 String targetKey,
                                 String suppliedToken,
                                 Object currentPreviewSnapshot) {
        boolean actionConfirmed = "reset_default_templates".equals(toolName)
                ? UserContextHolder.isDefaultTemplateResetConfirmed()
                : UserContextHolder.isDestructiveActionConfirmed();
        if (!actionConfirmed) {
            return ConsumeResult.rejected(
                    "CONFIRMATION_REQUIRED",
                    "No changes were made. Confirm the exact preview in a later message before retrying.");
        }

        SessionScope scope;
        try {
            scope = currentScope(userId);
        } catch (IllegalStateException e) {
            return ConsumeResult.rejected(
                    "CONFIRMATION_CONTEXT_REQUIRED",
                    "No changes were made because the protected-action confirmation is not associated with an active chat session.");
        }

        PendingAction pending = pendingBySession.get(scope);
        if (pending == null) {
            return ConsumeResult.rejected(
                    "CONFIRMATION_MISSING",
                    "No changes were made. The preview is missing, expired, or already used; request a fresh preview.");
        }
        if (pending.expiresAt().isBefore(Instant.now())) {
            pendingBySession.remove(scope, pending);
            return ConsumeResult.rejected(
                    "CONFIRMATION_EXPIRED",
                    "No changes were made. The protected-action preview expired; request and confirm a fresh preview.");
        }

        String expectedTool = requireText(toolName, "toolName");
        String expectedTarget = requireText(targetKey, "targetKey");
        if (!pending.toolName().equals(expectedTool)
                || !pending.targetKey().equals(expectedTarget)
                || !secureEquals(pending.token(), suppliedToken)) {
            return ConsumeResult.rejected(
                    "CONFIRMATION_MISMATCH",
                    "No changes were made. The confirmation token does not match this tool and target; review a fresh preview.");
        }

        byte[] currentDigest = digest(currentPreviewSnapshot);
        if (!MessageDigest.isEqual(pending.previewDigest(), currentDigest)) {
            pendingBySession.remove(scope, pending);
            return ConsumeResult.rejected(
                    "CONFIRMATION_STALE",
                    "No changes were made because the protected-action impact changed after the preview; review and confirm the current preview.");
        }

        if (!pendingBySession.remove(scope, pending)) {
            return ConsumeResult.rejected(
                    "CONFIRMATION_CONSUMED",
                    "No changes were made. This protected-action confirmation was already used; request a fresh preview.");
        }
        return ConsumeResult.approved(pending.domainImpactToken());
    }

    public void clearSession(Long userId, String sessionId) {
        if (userId == null || sessionId == null || sessionId.isBlank()) return;
        pendingBySession.remove(new SessionScope(userId, sessionId));
    }

    public void clearUser(Long userId) {
        if (userId == null) return;
        pendingBySession.keySet().removeIf(scope -> Objects.equals(scope.userId(), userId));
    }

    /** Returns compact confirmation context without depending on persisted tool-result history. */
    public Optional<PendingActionContext> pendingContext(Long userId, String sessionId) {
        if (userId == null || sessionId == null || sessionId.isBlank()) return Optional.empty();
        SessionScope scope = new SessionScope(userId, sessionId);
        PendingAction pending = pendingBySession.get(scope);
        if (pending == null) return Optional.empty();
        if (!pending.expiresAt().isAfter(Instant.now())) {
            pendingBySession.remove(scope, pending);
            return Optional.empty();
        }
        return Optional.of(new PendingActionContext(
                pending.toolName(), pending.targetKey(), pending.token()));
    }

    private SessionScope currentScope(Long userId) {
        if (userId == null) {
            throw new IllegalStateException("A destructive AI action requires an authenticated user.");
        }
        String sessionId = UserContextHolder.getChatSessionId();
        if (sessionId == null || sessionId.isBlank()) {
            throw new IllegalStateException("A destructive AI action requires an active chat session.");
        }
        return new SessionScope(userId, sessionId);
    }

    private byte[] digest(Object value) {
        try {
            JsonNode tree = objectMapper.valueToTree(value);
            JsonNode canonical = canonicalize(tree);
            return MessageDigest.getInstance("SHA-256")
                    .digest(objectMapper.writeValueAsBytes(canonical));
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 is unavailable", e);
        } catch (Exception e) {
            throw new IllegalStateException("Could not bind the protected-action preview", e);
        }
    }

    private JsonNode canonicalize(JsonNode node) {
        if (node == null || node.isNull()) return JsonNodeFactory.instance.nullNode();
        if (node.isObject()) {
            ObjectNode sorted = JsonNodeFactory.instance.objectNode();
            List<String> fieldNames = new ArrayList<>();
            node.fieldNames().forEachRemaining(fieldNames::add);
            fieldNames.sort(Comparator.naturalOrder());
            for (String fieldName : fieldNames) {
                sorted.set(fieldName, canonicalize(node.get(fieldName)));
            }
            return sorted;
        }
        if (node.isArray()) {
            ArrayNode array = JsonNodeFactory.instance.arrayNode();
            node.forEach(item -> array.add(canonicalize(item)));
            return array;
        }
        return node.deepCopy();
    }

    private void removeExpiredEntries() {
        Instant now = Instant.now();
        pendingBySession.entrySet().removeIf(entry -> entry.getValue().expiresAt().isBefore(now));
    }

    private boolean secureEquals(String expected, String supplied) {
        if (expected == null || supplied == null) return false;
        return MessageDigest.isEqual(
                expected.getBytes(StandardCharsets.UTF_8),
                supplied.getBytes(StandardCharsets.UTF_8));
    }

    private String requireText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " must not be blank");
        }
        return value;
    }

    private record SessionScope(Long userId, String sessionId) {
    }

    private record PendingAction(String token,
                                 String toolName,
                                 String targetKey,
                                 byte[] previewDigest,
                                 String domainImpactToken,
                                 Instant expiresAt) {
    }

    public record PendingActionContext(String toolName, String targetKey, String impactToken) {
    }

    public record ConsumeResult(boolean approved,
                                String errorCode,
                                String message,
                                String domainImpactToken) {

        private static ConsumeResult approved(String domainImpactToken) {
            return new ConsumeResult(true, null, null, domainImpactToken);
        }

        private static ConsumeResult rejected(String errorCode, String message) {
            return new ConsumeResult(false, errorCode, message, null);
        }
    }
}
