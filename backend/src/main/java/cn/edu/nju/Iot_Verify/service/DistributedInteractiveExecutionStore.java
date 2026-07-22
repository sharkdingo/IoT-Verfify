package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStatusDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.data.redis.core.StringRedisTemplate;
import org.springframework.data.redis.core.script.DefaultRedisScript;
import org.springframework.stereotype.Component;

import java.time.Duration;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

/** Redis-backed ownership, status, and stop propagation for interactive HTTP operations. */
@Slf4j
@Component
public class DistributedInteractiveExecutionStore {

    private static final Duration ACTIVE_TTL = Duration.ofSeconds(30);
    private static final Duration COMPLETED_TTL = Duration.ofSeconds(15);
    private static final DefaultRedisScript<Long> RELEASE_SCRIPT = new DefaultRedisScript<>(
            "if redis.call('get', KEYS[1]) == ARGV[1] then return redis.call('del', KEYS[1]) else return 0 end",
            Long.class);
    private static final DefaultRedisScript<Long> STATUS_SCRIPT = new DefaultRedisScript<>(
            "if redis.call('get', KEYS[1]) ~= ARGV[1] then return 0 end; "
                    + "local stage = ARGV[3]; "
                    + "if redis.call('get', KEYS[3]) == ARGV[1] then stage = 'CANCELLING' end; "
                    + "redis.call('hset', KEYS[2], 'state', ARGV[2]); "
                    + "redis.call('hset', KEYS[2], 'stage', stage); "
                    + "redis.call('hset', KEYS[2], 'startedAt', ARGV[4]); "
                    + "redis.call('hset', KEYS[2], 'token', ARGV[1]); "
                    + "redis.call('pexpire', KEYS[2], ARGV[5]); return 1",
            Long.class);
    private static final DefaultRedisScript<Long> CANCEL_SCRIPT = new DefaultRedisScript<>(
            "local token = redis.call('get', KEYS[1]); "
                    + "if not token then return 0 end; "
                    + "redis.call('psetex', KEYS[2], ARGV[1], token); "
                    + "redis.call('hset', KEYS[3], 'stage', ARGV[2]); "
                    + "redis.call('pexpire', KEYS[3], ARGV[1]); return 1",
            Long.class);
    private static final DefaultRedisScript<Long> POLL_SCRIPT = new DefaultRedisScript<>(
            "if redis.call('get', KEYS[1]) ~= ARGV[1] then return -1 end; "
                    + "if ARGV[3] == '1' and redis.call('get', KEYS[2]) ~= ARGV[1] then return -1 end; "
                    + "redis.call('pexpire', KEYS[1], ARGV[2]); "
                    + "if ARGV[3] == '1' then redis.call('pexpire', KEYS[2], ARGV[2]) end; "
                    + "redis.call('pexpire', KEYS[3], ARGV[2]); "
                    + "if redis.call('get', KEYS[4]) == ARGV[1] then return 1 else return 0 end",
            Long.class);
    private static final DefaultRedisScript<Long> FINISH_SCRIPT = new DefaultRedisScript<>(
            "if redis.call('get', KEYS[1]) ~= ARGV[1] then return 0 end; "
                    + "redis.call('hset', KEYS[3], 'state', 'FINISHED'); "
                    + "redis.call('hset', KEYS[3], 'stage', ARGV[2]); "
                    + "redis.call('hset', KEYS[3], 'startedAt', ARGV[3]); "
                    + "redis.call('hset', KEYS[3], 'token', ARGV[1]); "
                    + "redis.call('pexpire', KEYS[3], ARGV[4]); "
                    + "if redis.call('get', KEYS[4]) == ARGV[1] then redis.call('del', KEYS[4]) end; "
                    + "if ARGV[5] == '1' and redis.call('get', KEYS[2]) == ARGV[1] then redis.call('del', KEYS[2]) end; "
                    + "redis.call('del', KEYS[1]); return 1",
            Long.class);
    private static final DefaultRedisScript<Long> ABANDON_SCRIPT = new DefaultRedisScript<>(
            "if redis.call('get', KEYS[1]) ~= ARGV[1] then return 0 end; "
                    + "redis.call('del', KEYS[3]); "
                    + "if redis.call('get', KEYS[4]) == ARGV[1] then redis.call('del', KEYS[4]) end; "
                    + "if ARGV[2] == '1' and redis.call('get', KEYS[2]) == ARGV[1] then redis.call('del', KEYS[2]) end; "
                    + "redis.call('del', KEYS[1]); return 1",
            Long.class);
    private static final DefaultRedisScript<String> STATUS_READ_SCRIPT = new DefaultRedisScript<>(
            "local state = redis.call('hget', KEYS[1], 'state'); "
                    + "if not state then return nil end; "
                    + "local stage = redis.call('hget', KEYS[1], 'stage'); "
                    + "local startedAt = redis.call('hget', KEYS[1], 'startedAt'); "
                    + "local statusToken = redis.call('hget', KEYS[1], 'token'); "
                    + "if not stage or not startedAt or not statusToken then return nil end; "
                    + "local ownerToken = redis.call('get', KEYS[2]); "
                    + "if state == 'FINISHED' and ownerToken and ownerToken ~= statusToken then return nil end; "
                    + "if state ~= 'FINISHED' and (not ownerToken or ownerToken ~= statusToken) then return nil end; "
                    + "return state .. '\\n' .. stage .. '\\n' .. startedAt",
            String.class);

    private final StringRedisTemplate redisTemplate;

    public DistributedInteractiveExecutionStore(StringRedisTemplate redisTemplate) {
        this.redisTemplate = redisTemplate;
    }

    public Lease acquire(String kind, Long userId, String requestId, boolean exclusivePerUser) {
        Lease lease = new Lease(kind, userId, requestId, UUID.randomUUID().toString(),
                exclusivePerUser, System.currentTimeMillis());
        boolean ownerAcquired = false;
        boolean userAcquired = false;
        try {
            ownerAcquired = Boolean.TRUE.equals(redisTemplate.opsForValue()
                    .setIfAbsent(lease.ownerKey(), lease.token, ACTIVE_TTL));
            if (!ownerAcquired) throw new BusyException(BusyScope.REQUEST);
            if (exclusivePerUser) {
                userAcquired = Boolean.TRUE.equals(redisTemplate.opsForValue()
                        .setIfAbsent(lease.userKey(), lease.token, ACTIVE_TTL));
                if (!userAcquired) throw new BusyException(BusyScope.USER);
            }
            lease.redisBacked = true;
            writeStatus(lease, "WAITING", InteractiveOperationStage.QUEUED, ACTIVE_TTL);
            return lease;
        } catch (BusyException e) {
            if (ownerAcquired) releaseKey(lease.ownerKey(), lease.token);
            if (userAcquired) releaseKey(lease.userKey(), lease.token);
            throw e;
        } catch (RuntimeException e) {
            if (ownerAcquired) releaseKey(lease.ownerKey(), lease.token);
            if (userAcquired) releaseKey(lease.userKey(), lease.token);
            lease.redisBacked = false;
            log.warn("Redis interactive execution registry is unavailable; using local tracking for {}: {}",
                    kind, e.toString());
            return lease;
        }
    }

    public void update(Lease lease, String state, InteractiveOperationStage stage) {
        if (lease == null || !lease.redisBacked) return;
        try {
            writeStatus(lease, state, stage, ACTIVE_TTL);
        } catch (RuntimeException e) {
            log.warn("Could not update distributed interactive status {}: {}", lease.statusKey(), e.toString());
        }
    }

    public Optional<InteractiveOperationStatusDto> getStatus(String kind, Long userId, String requestId) {
        String statusKey = statusKey(kind, userId, requestId);
        try {
            String encoded = redisTemplate.execute(
                    STATUS_READ_SCRIPT,
                    List.of(statusKey, ownerKey(kind, userId, requestId)));
            if (encoded == null || encoded.isBlank()) return Optional.empty();
            String[] fields = encoded.split("\\n", -1);
            if (fields.length != 3) return Optional.empty();
            String state = fields[0];
            String stage = fields[1];
            long startedAt = parseLong(fields[2], System.currentTimeMillis());
            return Optional.of(InteractiveOperationStatusDto.builder()
                    .requestId(requestId)
                    .state(state)
                    .stage(InteractiveOperationStage.valueOf(stage))
                    .elapsedMs(Math.max(0, System.currentTimeMillis() - startedAt))
                    .build());
        } catch (RuntimeException e) {
            log.warn("Could not read distributed interactive status {}: {}", statusKey, e.toString());
            return Optional.empty();
        }
    }

    public boolean requestCancellation(String kind, Long userId, String requestId) {
        String ownerKey = ownerKey(kind, userId, requestId);
        try {
            Long published = redisTemplate.execute(
                    CANCEL_SCRIPT,
                    List.of(ownerKey, cancelKey(kind, userId, requestId),
                            statusKey(kind, userId, requestId)),
                    Long.toString(ACTIVE_TTL.toMillis()),
                    InteractiveOperationStage.CANCELLING.name());
            return Long.valueOf(1L).equals(published);
        } catch (RuntimeException e) {
            log.warn("Could not publish distributed interactive cancellation for {}/{}: {}",
                    userId, requestId, e.toString());
            return false;
        }
    }

    /** Returns true when cancellation was requested or this worker no longer owns its lease. */
    public boolean shouldStop(Lease lease) {
        if (lease == null || !lease.redisBacked) return false;
        try {
            Long result = redisTemplate.execute(
                    POLL_SCRIPT,
                    List.of(lease.ownerKey(), lease.userKey(), lease.statusKey(), lease.cancelKey()),
                    lease.token,
                    Long.toString(ACTIVE_TTL.toMillis()),
                    lease.exclusivePerUser ? "1" : "0");
            if (result == null || result < 0) return true;
            lease.lastConfirmedAtMillis = System.currentTimeMillis();
            return result == 1L;
        } catch (RuntimeException e) {
            if (System.currentTimeMillis() - lease.lastConfirmedAtMillis >= ACTIVE_TTL.toMillis()) {
                return true;
            }
            log.warn("Could not poll distributed interactive execution {}: {}", lease.ownerKey(), e.toString());
            return false;
        }
    }

    public void finish(Lease lease, InteractiveOperationStage stage) {
        if (lease == null || !lease.redisBacked) return;
        try {
            redisTemplate.execute(
                    FINISH_SCRIPT,
                    List.of(lease.ownerKey(), lease.userKey(), lease.statusKey(), lease.cancelKey()),
                    lease.token,
                    stage.name(),
                    Long.toString(lease.startedAtMillis),
                    Long.toString(COMPLETED_TTL.toMillis()),
                    lease.exclusivePerUser ? "1" : "0");
        } catch (RuntimeException e) {
            log.warn("Could not publish final interactive status {}: {}", lease.statusKey(), e.toString());
        }
    }

    public void abandon(Lease lease) {
        if (lease == null || !lease.redisBacked) return;
        try {
            redisTemplate.execute(
                    ABANDON_SCRIPT,
                    List.of(lease.ownerKey(), lease.userKey(), lease.statusKey(), lease.cancelKey()),
                    lease.token,
                    lease.exclusivePerUser ? "1" : "0");
        } catch (RuntimeException e) {
            log.warn("Could not abandon interactive execution {}: {}", lease.ownerKey(), e.toString());
        }
    }

    private void writeStatus(Lease lease, String state, InteractiveOperationStage stage, Duration ttl) {
        Long updated = redisTemplate.execute(
                STATUS_SCRIPT,
                List.of(lease.ownerKey(), lease.statusKey(), lease.cancelKey()),
                lease.token,
                state,
                stage.name(),
                Long.toString(lease.startedAtMillis),
                Long.toString(ttl.toMillis()));
        if (!Long.valueOf(1L).equals(updated)) {
            throw new IllegalStateException("Interactive execution lease is no longer owned");
        }
    }

    private void releaseKey(String key, String token) {
        try {
            redisTemplate.execute(RELEASE_SCRIPT, List.of(key), token);
        } catch (RuntimeException e) {
            log.warn("Could not release distributed interactive lease {}: {}", key, e.toString());
        }
    }

    private static long parseLong(String value, long fallback) {
        try {
            return Long.parseLong(value);
        } catch (NumberFormatException ignored) {
            return fallback;
        }
    }

    private static String prefix(String kind, Long userId, String requestId) {
        return "iot-verify:interactive:" + kind + ":" + userId + ":" + requestId;
    }

    private static String ownerKey(String kind, Long userId, String requestId) {
        return prefix(kind, userId, requestId) + ":owner";
    }

    private static String statusKey(String kind, Long userId, String requestId) {
        return prefix(kind, userId, requestId) + ":status";
    }

    private static String cancelKey(String kind, Long userId, String requestId) {
        return prefix(kind, userId, requestId) + ":cancel";
    }

    private static String userKey(String kind, Long userId) {
        return "iot-verify:interactive:" + kind + ":" + userId + ":active";
    }

    public enum BusyScope {
        REQUEST,
        USER
    }

    public static final class BusyException extends RuntimeException {
        private final BusyScope scope;

        private BusyException(BusyScope scope) {
            this.scope = scope;
        }

        public BusyScope getScope() {
            return scope;
        }
    }

    public static final class Lease {
        private final String kind;
        private final Long userId;
        private final String requestId;
        private final String token;
        private final boolean exclusivePerUser;
        private final long startedAtMillis;
        private volatile boolean redisBacked;
        private volatile long lastConfirmedAtMillis = System.currentTimeMillis();

        private Lease(String kind, Long userId, String requestId, String token,
                      boolean exclusivePerUser, long startedAtMillis) {
            this.kind = kind;
            this.userId = userId;
            this.requestId = requestId;
            this.token = token;
            this.exclusivePerUser = exclusivePerUser;
            this.startedAtMillis = startedAtMillis;
        }

        private String ownerKey() { return DistributedInteractiveExecutionStore.ownerKey(kind, userId, requestId); }
        private String statusKey() { return DistributedInteractiveExecutionStore.statusKey(kind, userId, requestId); }
        private String cancelKey() { return DistributedInteractiveExecutionStore.cancelKey(kind, userId, requestId); }
        private String userKey() { return DistributedInteractiveExecutionStore.userKey(kind, userId); }

        boolean isRedisBacked() { return redisBacked; }
    }
}
