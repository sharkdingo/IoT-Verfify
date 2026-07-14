package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/** Complete device-local runtime subresource; identity, type, label and layout are not writable. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class DeviceRuntimeUpdateDto {

    @Size(max = 50, message = "State must be at most 50 characters")
    private String state;
    private String currentStateTrust;
    private String currentStatePrivacy;
    @Size(max = 200, message = "At most 200 local variable values are allowed")
    private List<@Valid @NotNull(message = "Variable item cannot be null") VariableStateDto> variables;
    @Size(max = 200, message = "At most 200 local sensitivity values are allowed")
    private List<@Valid @NotNull(message = "Privacy item cannot be null") PrivacyStateDto> privacies;
}
