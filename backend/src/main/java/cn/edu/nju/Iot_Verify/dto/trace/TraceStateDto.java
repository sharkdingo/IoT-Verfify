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
 * 轨迹状态
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceStateDto {
    /**
     * 状态序号
     * 使用 Integer 包装类型以支持 null 值
     */
    @NotNull(message = "State index is required")
    private Integer stateIndex;

    /**
     * 设备状态变化列表
     */
    @Valid
    @NotNull(message = "Devices list is required")
    private List<TraceDeviceDto> devices;
    
    /**
     * 触发的规则编号列表
     */
    private List<Integer> rules;
    
    /**
     * 信任/隐私变化列表
     */
    @Valid
    private List<TraceTrustPrivacyDto> trustPrivacies;
}
