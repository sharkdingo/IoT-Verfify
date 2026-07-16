package cn.edu.nju.Iot_Verify.dto.model;

/** Stable, localizable phase codes shared by persisted background tasks. */
public enum TaskProgressStage {
    QUEUED,
    STARTING,
    GENERATING_MODEL,
    EXECUTING_MODEL_CHECKER,
    PARSING_RESULTS,
    RUNNING_SIMULATION,
    PREPARING_EXPLORATION,
    EXPLORING_CANDIDATES,
    PERSISTING_RESULT
}
