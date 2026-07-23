package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.TaskView;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.time.LocalDateTime;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Supplier;

/** Renews an async task lease only after acquiring that task's database row lock. */
final class TaskLeaseRenewal {

    private static final Set<String> ACTIVE_STATUSES = Set.of("PENDING", "RUNNING");

    private TaskLeaseRenewal() {
    }

    static <T extends TaskView> boolean renew(
            TransactionTemplate transactionTemplate,
            Supplier<Optional<T>> lockTask,
            Supplier<LocalDateTime> databaseClock,
            Consumer<T> flushTask,
            String workerId,
            Duration leaseDuration) {
        Boolean renewed = transactionTemplate.execute(status -> {
            T task = lockTask.get().orElse(null);
            if (task == null) return false;

            LocalDateTime now = Objects.requireNonNull(
                    databaseClock.get(), "Database current timestamp must not be null");
            LocalDateTime currentExpiry = task.getLeaseExpiresAt();
            if (!Objects.equals(workerId, task.getWorkerId())
                    || !ACTIVE_STATUSES.contains(task.getTaskStatusName())
                    || currentExpiry == null
                    || !currentExpiry.isAfter(now)) {
                return false;
            }

            task.setLeaseExpiresAt(now.plus(leaseDuration));
            flushTask.accept(task);
            return true;
        });
        return Boolean.TRUE.equals(renewed);
    }
}
