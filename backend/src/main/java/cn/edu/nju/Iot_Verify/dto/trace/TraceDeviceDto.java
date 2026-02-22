package cn.edu.nju.Iot_Verify.dto.trace;

import com.fasterxml.jackson.annotation.JsonAlias;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import lombok.Data;

import java.util.List;

/**
 * 轨迹中的设备状态
 */
@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class TraceDeviceDto {
    /**
     * 设备编号
     */
    private String deviceId;

    /**
     * 设备标签
     */
    private String deviceLabel;

    /**
     * 模板名称
     */
    private String templateName;

    /**
     * 当前状态值（反序列化时兼容历史 JSON 中的 "newState" 字段）
     */
    @JsonAlias("newState")
    private String state;

    /**
     * 状态机名称（模式名，如 "ThermostatMode"）
     */
    private String mode;

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
