package cn.edu.nju.Iot_Verify.component.ai.model;

/** Persisted terminal outcome of one user-visible chat execution. */
public enum ChatExecutionStatus {
    COMPLETED,
    AWAITING_CONFIRMATION,
    PARTIAL,
    STOPPED,
    DISCONNECTED,
    FAILED
}
