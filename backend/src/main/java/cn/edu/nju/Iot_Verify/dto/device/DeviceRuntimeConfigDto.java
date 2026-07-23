package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.List;

/** User-domain initial model configuration shared by non-visual device creation paths. */
@Data
public class DeviceRuntimeConfigDto {
    @Size(max = 50, message = "State must be at most 50 characters")
    private String state;
    @Size(max = 20, message = "State trust must be at most 20 characters")
    private String currentStateTrust;
    @Size(max = 20, message = "State privacy must be at most 20 characters")
    private String currentStatePrivacy;
    @Size(max = RequestLimits.MAX_DEVICE_VARIABLES,
            message = "At most 100 local variable values are allowed")
    private List<@Valid @NotNull(message = "Variable item cannot be null") VariableStateDto> variables;
    @Size(max = RequestLimits.MAX_DEVICE_PRIVACIES,
            message = "At most 100 local sensitivity values are allowed")
    private List<@Valid @NotNull(message = "Privacy item cannot be null") PrivacyStateDto> privacies;
}
