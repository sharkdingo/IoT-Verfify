package cn.edu.nju.Iot_Verify.dto.trace;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

/**
 * 轨迹中的设备状态
 */
@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceDeviceDto {
    /**
     * Model-boundary device identity: NuSMV-safe varName derived from DeviceNode.id.
     */
    private String deviceId;

    /**
     * Display label snapshot. Never used for identity resolution.
     */
    private String deviceLabel;

    /**
     * 模板名称
     */
    private String templateName;

    /** Frozen source used only to decide whether bundled model identifiers may be localized. */
    private ModelTokenSource modelTokenSource;

    /**
     * 当前状态值。权威 JSON 字段为 "state"。
     */
    private String state;

    /**
     * 状态机名称（模式名，如 "ThermostatMode"）
     */
    private String mode;

    /** User-facing compromise state for this model snapshot; internal is_attack is not serialized as a variable. */
    private Boolean compromised;

    /**
     * 变量变化列表
     */
    @Valid
    @NotNull
    private List<TraceVariableDto> variables = new ArrayList<>();

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
