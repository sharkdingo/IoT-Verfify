package cn.edu.nju.Iot_Verify.dto.device;

import lombok.Data;

import java.util.List;

/** User-domain initial model configuration shared by non-visual device creation paths. */
@Data
public class DeviceRuntimeConfigDto {
    private String state;
    private String currentStateTrust;
    private String currentStatePrivacy;
    private List<VariableStateDto> variables;
    private List<PrivacyStateDto> privacies;
}
