package cn.edu.nju.Iot_Verify.dto.trace;

import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import lombok.Data;

import java.util.List;

/**
 * 轨迹中的设备状态
 */
@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceDeviceDto {
    /**
     * 设备编号
     */
    @NotBlank(message = "Device ID is required")
    private String deviceId;
    
    /**
     * 设备标签
     */
    private String deviceLabel;
    
    /**
     * 模板名称
     */
    @NotBlank(message = "Template name is required")
    private String templateName;
    
    /**
     * 当前状态
     */
    @NotBlank(message = "State is required")
    private String newState;
    
    /**
     * 变量变化列表
     */
    @Valid
    private List<TraceVariableDto> variables;
    
    /**
     * 状态信任变化列表
     */
    @Valid
    private List<TraceTrustPrivacyDto> trustPrivacy;
    
    /**
     * 隐私变化列表
     */
    @Valid
    private List<TraceTrustPrivacyDto> privacies;
}
