package cn.edu.nju.Iot_Verify.dto.model;

import lombok.Builder;
import lombok.Data;

/** Current server-observed state for a cancellable synchronous operation. */
@Data
@Builder
public class InteractiveOperationStatusDto {
    private String requestId;
    private String state;
    private InteractiveOperationStage stage;
    private long elapsedMs;
}
