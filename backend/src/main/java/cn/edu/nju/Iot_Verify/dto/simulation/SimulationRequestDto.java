package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import jakarta.validation.Valid;
import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

/**
 * 模拟请求 DTO
 *
 * 与 VerificationRequestDto 的区别：无 specs（模拟不检查规约），新增 steps 控制模拟步数。
 */
@Data
public class SimulationRequestDto {

    @Valid
    @NotNull(message = "Devices list cannot be null")
    private List<DeviceVerificationDto> devices;

    @Valid
    private List<RuleDto> rules = new ArrayList<>();

    /** 模拟步数，默认 10 步 */
    @Min(1) @Max(100)
    private int steps = 10;

    private boolean isAttack = false;

    @Min(0) @Max(50)
    private int intensity = 3;

    private boolean enablePrivacy = false;
}
