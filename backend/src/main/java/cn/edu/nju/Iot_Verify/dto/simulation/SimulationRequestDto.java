package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
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

    // The scene is NOT part of this request; the server reads it from the caller's persisted board so
    // a run always describes the board the user saved. The strict request parser rejects any attempt
    // to supply these fields, so they only ever hold the service's own frozen board snapshot.
    private List<DeviceVerificationDto> devices;

    /** Frozen canvas layout for faithful read-only replay; it is not part of NuSMV semantics. */
    private List<DeviceNodeDto> playbackNodes;

    /** Board-level environment pool, captured with the same board read as the devices. */
    private List<BoardEnvironmentVariableDto> environmentVariables = new ArrayList<>();

    private List<RuleDto> rules = new ArrayList<>();

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
