package cn.edu.nju.Iot_Verify.dto.model;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Separates a completed model execution from whether it was added to run history. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class RunPersistenceDto {
    public enum Status {
        SAVED,
        NOT_REQUESTED,
        FAILED,
        OUTCOME_UNKNOWN
    }

    private Status status;
    private Long runId;
    private String reasonCode;

    public static RunPersistenceDto saved(Long runId) {
        return RunPersistenceDto.builder().status(Status.SAVED).runId(runId).build();
    }

    public static RunPersistenceDto notRequested() {
        return RunPersistenceDto.builder().status(Status.NOT_REQUESTED).build();
    }

    public static RunPersistenceDto failed(String reasonCode) {
        return RunPersistenceDto.builder().status(Status.FAILED).reasonCode(reasonCode).build();
    }

    public static RunPersistenceDto outcomeUnknown(String reasonCode) {
        return RunPersistenceDto.builder().status(Status.OUTCOME_UNKNOWN).reasonCode(reasonCode).build();
    }
}
