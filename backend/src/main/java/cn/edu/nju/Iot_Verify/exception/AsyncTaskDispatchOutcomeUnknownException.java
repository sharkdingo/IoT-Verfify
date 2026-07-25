package cn.edu.nju.Iot_Verify.exception;

/**
 * Raised when an async task was persisted, its dispatch call did not return successfully,
 * and removal of the task record could not be confirmed. Callers must reconcile the task
 * by id before retrying.
 */
public class AsyncTaskDispatchOutcomeUnknownException extends ServiceUnavailableException {

    public static final String REASON_CODE = "TASK_DISPATCH_OUTCOME_UNKNOWN";

    private final String taskKind;
    private final Long taskId;

    public AsyncTaskDispatchOutcomeUnknownException(String taskType, Long taskId, Throwable cause) {
        super("The " + taskType + " task dispatch did not return successfully, and cleanup "
                + "of its task record could not be confirmed. Check task " + taskId
                + " before retrying.", cause);
        this.taskKind = taskType;
        this.taskId = taskId;
    }

    public String getTaskKind() {
        return taskKind;
    }

    public Long getTaskId() {
        return taskId;
    }
}
