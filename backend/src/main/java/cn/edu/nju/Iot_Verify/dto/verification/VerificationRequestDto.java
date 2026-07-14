package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

/**
 * 验证请求
 *
 * 参考 MEDIC-test 中的攻击模式支持，添加 isAttack 和 attackBudget 参数
 *
 * 注意：Trace 会自动保存（当检测到违规时），无需前端传入 saveTrace 参数
 */
@Data
public class VerificationRequestDto {
    /**
     * 设备验证数据列表（仅包含验证所需字段，不含 UI 布局信息）
     */
    @Valid
    @NotEmpty(message = "Devices list cannot be empty")
    private List<@Valid @NotNull(message = "Device item cannot be null") DeviceVerificationDto> devices;

    /**
     * Board-level environment pool. Device prefixes in rules/specs describe read permission, while
     * the actual scenario value comes from this shared pool.
     */
    @Valid
    private List<@Valid @NotNull(message = "Environment variable item cannot be null") BoardEnvironmentVariableDto> environmentVariables = new ArrayList<>();

    /**
     * 规则列表
     */
    @Valid
    private List<@Valid @NotNull(message = "Rule item cannot be null") RuleDto> rules = new ArrayList<>();

    /**
     * 
     * 规格列表
     */
    @Valid
    @NotEmpty(message = "Specs list cannot be empty")
    private List<@Valid @NotNull(message = "Specification item cannot be null") SpecificationDto> specs;
    
    /**
     * 是否启用攻击模式
     * 参考 MEDIC-test SMVGeneration.java 中的 isAttack 标志
     */
    @JsonProperty("isAttack")
    private boolean isAttack = false;
    
    /**
     * 攻击预算（启用攻击建模时必须显式提供 1-50；关闭时必须为 0）
     * Limits how many modeled device-instance or automation-link points may be compromised
     * in one verification branch.
     * It never changes a device variable's declared domain. A compromised instance's
     * template-declared falsifiable readings may produce any value within their domains,
     * while a TAP-rule command sent to that target is dropped. A compromised automation
     * link independently drops that rule's command. Other device-internal transitions
     * are not frozen. Each submitted rule is one modeled automation-link point.
     */
    @Min(0) @Max(50)
    private int attackBudget = 0;

    /**
     * 是否启用隐私维度建模
     * 参考 MEDIC-test SMVGeneration.java 中的 now==3 标志
     *
     * 启用后会为每个设备状态/变量生成 privacy 标签变量，增加 NuSMV 状态空间。
     * privacy 条件存在时服务端会强制启用，以免把未建模的属性当成已验证。
     * This tracks sensitivity-label propagation; it does not implement access control or encryption.
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
