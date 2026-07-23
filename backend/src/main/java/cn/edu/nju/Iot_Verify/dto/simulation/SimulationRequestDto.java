package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.validation.Valid;
import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * 模拟请求 DTO
 *
 * 与 VerificationRequestDto 的区别：无 specs（模拟不检查规约），新增 steps 控制模拟步数。
 */
@Data
public class SimulationRequestDto {

    @Valid
    @NotEmpty(message = "Devices list cannot be empty")
    @Size(max = RequestLimits.MAX_DEVICES, message = "At most 100 devices can be simulated")
    private List<@Valid @NotNull(message = "Device item cannot be null") DeviceVerificationDto> devices;

    /**
     * Board-level environment pool. Device templates grant read permission; values live here.
     */
    @Valid
    @Size(max = RequestLimits.MAX_ENVIRONMENT_VARIABLES, message = "At most 200 environment variables can be simulated")
    private List<@Valid @NotNull(message = "Environment variable item cannot be null") BoardEnvironmentVariableDto> environmentVariables = new ArrayList<>();

    @Valid
    @Size(max = RequestLimits.MAX_RULES, message = "At most 100 rules can be simulated")
    private List<@Valid @NotNull(message = "Rule item cannot be null") RuleDto> rules = new ArrayList<>();

    /** 模拟步数，默认 10 步 */
    @Min(1) @Max(100)
    private int steps = 10;

    /** Per-run attack selection. Simulation accepts only NONE or explicit points. */
    @Valid
    @NotNull(message = "Attack scenario is required")
    private AttackScenarioDto attackScenario;

    /** Track sensitivity-label propagation; this does not model access control or encryption. */
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
