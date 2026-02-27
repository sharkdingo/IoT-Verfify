package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
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

    @JsonProperty("isAttack")
    private boolean isAttack = false;

    @Min(0) @Max(50)
    private int intensity = 3;

    private boolean enablePrivacy = false;

    // 阻止 Lombok 生成的 isAttack()/setAttack() 被 Jackson 序列化
    @JsonIgnore
    public boolean isAttack() {
        return isAttack;
    }

    @JsonIgnore
    public void setAttack(boolean attack) {
        this.isAttack = attack;
    }
}
