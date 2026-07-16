package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

import java.util.Locale;

@Getter
public class AsyncTaskQuotaExceededException extends BaseException {

    public enum QuotaType {
        ACTIVE,
        STORED
    }

    private final String taskKind;
    private final QuotaType quotaType;
    private final String reasonCode;
    private final long taskCount;
    private final int maxTasksPerUser;

    public AsyncTaskQuotaExceededException(
            String taskKind,
            QuotaType quotaType,
            long taskCount,
            int maxTasksPerUser) {
        super(429, quotaType == QuotaType.ACTIVE
                ? "Active " + taskKind + " task limit reached"
                : "Stored " + taskKind + " task limit reached; delete old history or failed tasks first");
        this.taskKind = taskKind;
        this.quotaType = quotaType;
        this.reasonCode = taskKind.toUpperCase(Locale.ROOT)
                + "_" + quotaType.name() + "_TASK_LIMIT_REACHED";
        this.taskCount = taskCount;
        this.maxTasksPerUser = maxTasksPerUser;
    }
}
