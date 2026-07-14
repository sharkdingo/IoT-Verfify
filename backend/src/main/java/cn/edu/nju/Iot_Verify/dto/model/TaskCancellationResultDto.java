package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Explains what a cancellation request actually changed. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class TaskCancellationResultDto {
    private Long taskId;
    private boolean cancellationAccepted;
    private TaskCancellationOutcome cancellationOutcome;
    private String taskStatus;

    /** True when a RUNNING task was marked cancelled while its worker may still be stopping. */
    private boolean executionMayStillBeStopping;
}
