package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * 验证请求
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
    @Size(max = RequestLimits.MAX_DEVICES, message = "At most 100 devices can be verified")
    private List<@Valid @NotNull(message = "Device item cannot be null") DeviceVerificationDto> devices;

    /**
     * Board-level environment pool. Device prefixes in rules/specs describe read permission, while
     * the actual scenario value comes from this shared pool.
     */
    @Valid
    @Size(max = RequestLimits.MAX_ENVIRONMENT_VARIABLES, message = "At most 200 environment variables can be verified")
    private List<@Valid @NotNull(message = "Environment variable item cannot be null") BoardEnvironmentVariableDto> environmentVariables = new ArrayList<>();

    /**
     * 规则列表
     */
    @Valid
    @Size(max = RequestLimits.MAX_RULES, message = "At most 100 rules can be verified")
    private List<@Valid @NotNull(message = "Rule item cannot be null") RuleDto> rules = new ArrayList<>();

    /**
     * 
     * 规格列表
     */
    @Valid
    @NotEmpty(message = "Specs list cannot be empty")
    @Size(max = RequestLimits.MAX_SPECS, message = "At most 100 specifications can be verified")
    private List<@Valid @NotNull(message = "Specification item cannot be null") SpecificationDto> specs;
    
    /** Per-run attack selection. Trust labels remain independent board/model inputs. */
    @Valid
    @NotNull(message = "Attack scenario is required")
    private AttackScenarioDto attackScenario;

    /**
     * 是否启用隐私维度建模
     * 参考 MEDIC-test SMVGeneration.java 中的 now==3 标志
     *
     * 启用后会为每个设备状态/变量生成 privacy 标签变量，增加 NuSMV 状态空间。
     * privacy 条件存在时服务端会强制启用，以免把未建模的属性当成已验证。
     * This tracks sensitivity-label propagation; it does not implement access control or encryption.
     */
    private boolean enablePrivacy = false;

    @JsonIgnore
    public boolean isAttack() {
        return resolvedAttackScenario().isEnabled();
    }

    @JsonIgnore
    public int getAttackBudget() {
        return resolvedAttackScenario().effectiveBudget();
    }

    @JsonIgnore
    public AttackScenarioDto resolvedAttackScenario() {
        return Objects.requireNonNull(attackScenario, "attackScenario is required");
    }
}
