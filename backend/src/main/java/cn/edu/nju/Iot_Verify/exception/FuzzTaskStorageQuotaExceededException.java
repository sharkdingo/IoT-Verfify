package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class FuzzTaskStorageQuotaExceededException extends BaseException {

    public static final String REASON_CODE = "FUZZ_STORED_TASK_LIMIT_REACHED";

    private final long storedTaskCount;
    private final int maxStoredTasksPerUser;

    public FuzzTaskStorageQuotaExceededException(
            long storedTaskCount, int maxStoredTasksPerUser) {
        super(429, "Stored counterexample search task limit reached; "
                + "delete old history or failed tasks before starting another search");
        this.storedTaskCount = storedTaskCount;
        this.maxStoredTasksPerUser = maxStoredTasksPerUser;
    }
}
