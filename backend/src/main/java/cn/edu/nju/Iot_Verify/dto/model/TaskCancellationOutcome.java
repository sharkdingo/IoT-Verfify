package cn.edu.nju.Iot_Verify.dto.model;

/** User-relevant outcome of an asynchronous task cancellation attempt. */
public enum TaskCancellationOutcome {
    ACCEPTED,
    ALREADY_CANCELLED,
    ALREADY_COMPLETED,
    ALREADY_FAILED,
    NO_LONGER_CANCELLABLE
}
