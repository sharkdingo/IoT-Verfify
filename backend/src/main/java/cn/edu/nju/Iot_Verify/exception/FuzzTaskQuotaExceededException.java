package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class FuzzTaskQuotaExceededException extends BaseException {

    public static final String REASON_CODE = "FUZZ_ACTIVE_TASK_LIMIT_REACHED";

    private final long activeTaskCount;
    private final int maxActiveTasksPerUser;

    public FuzzTaskQuotaExceededException(long activeTaskCount, int maxActiveTasksPerUser) {
        super(429, "Active counterexample exploration task limit reached");
        this.activeTaskCount = activeTaskCount;
        this.maxActiveTasksPerUser = maxActiveTasksPerUser;
    }
}
