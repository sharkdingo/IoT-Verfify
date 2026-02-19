package cn.edu.nju.Iot_Verify.dto.trace;

import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * Trace state in one counterexample step.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceStateDto {
    @NotNull(message = "State index is required")
    private Integer stateIndex;

    @Valid
    @NotNull(message = "Devices list is required")
    private List<TraceDeviceDto> devices;

    private List<Integer> rules;

    @Valid
    private List<TraceTrustPrivacyDto> trustPrivacies;

    /**
     * Environment variables in this state, for example a_temperature.
     */
    @Valid
    private List<TraceVariableDto> envVariables;
}
