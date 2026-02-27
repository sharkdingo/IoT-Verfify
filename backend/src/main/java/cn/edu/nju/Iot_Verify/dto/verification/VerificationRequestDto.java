package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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
 * 验证请求
 *
 * 参考 MEDIC-test 中的攻击模式支持，添加 isAttack 和 intensity 参数
 *
 * 注意：Trace 会自动保存（当检测到违规时），无需前端传入 saveTrace 参数
 */
@Data
public class VerificationRequestDto {
    /**
     * 设备验证数据列表（仅包含验证所需字段，不含 UI 布局信息）
     */
    @Valid
    @NotNull(message = "Devices list cannot be null")
    private List<DeviceVerificationDto> devices;

    /**
     * 规则列表
     */
    @Valid
    private List<RuleDto> rules = new ArrayList<>();

    /**
     * 
     * 规格列表
     */
    @Valid
    @NotNull(message = "Specs list cannot be null")
    private List<SpecificationDto> specs;
    
    /**
     * 是否启用攻击模式
     * 参考 MEDIC-test SMVGeneration.java 中的 isAttack 标志
     */
    @JsonProperty("isAttack")
    private boolean isAttack = false;
    
    /**
     * 攻击强度 (0-50)
     * 参考 MEDIC-test SMVGeneration.java 中的 intensity 参数
     *
     * 用法：
     * - intensity 控制攻击的强度，范围 0-50
     * - 通过 INVAR intensity<=N 全局约束攻击预算
     * - intensity=0 时所有 is_attack 被强制为 FALSE（零预算无攻击）
     * - intensity 同时按比例控制传感器数值范围扩展
     */
    @Min(0) @Max(50)
    private int intensity = 3;

    /**
     * 是否启用隐私维度建模
     * 参考 MEDIC-test SMVGeneration.java 中的 now==3 标志
     *
     * 启用后会为每个设备状态/变量生成 privacy 变量，增加 NuSMV 状态空间。
     * 仅在 specs 中包含 privacy 相关条件时建议启用。
     * 默认关闭以提升验证性能。
     */
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
