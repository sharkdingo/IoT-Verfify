package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

import java.util.List;

/**
 * 设备验证 DTO
 *
 * 仅包含 NuSMV 验证所需的字段，与 DeviceNodeDto（画布 CRUD）分离。
 *
 * 字段语义：
 * - varName / templateName / state: 设备身份和当前状态
 * - currentStateTrust: 设备级信任覆盖 → smv.instanceStateTrust
 * - variables: 每变量的值和信任 → smv.variableValues + smv.instanceVariableTrust
 * - privacies: 每状态/变量的隐私覆盖 → smv.instanceVariablePrivacy
 */
@Data
public class DeviceVerificationDto {

    @NotBlank(message = "Device varName is required")
    private String varName;

    @NotBlank(message = "Template name is required")
    private String templateName;

    private String state;

    // 运行时验证状态
    private String currentStateTrust;
    private List<VariableStateDto> variables;
    private List<PrivacyStateDto> privacies;
}
