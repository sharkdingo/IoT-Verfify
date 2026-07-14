package cn.edu.nju.Iot_Verify.dto.fix;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 应用某条修复建议的请求。
 *
 * <p>The client selects a strategy and optional preference ranges. The server recomputes and
 * re-verifies the fix from the trace context before persisting it.</p>
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixApplyRequestDto {

    /** Strategy name: parameter / condition / remove. */
    @NotBlank(message = "strategy must not be blank")
    @Pattern(regexp = "parameter|condition|remove",
            message = "strategy must be one of parameter, condition, remove")
    private String strategy;

    /**
     * 生成该建议时 /fix 使用的参数范围选择（若有）。每项选择使用 ParameterAdjustment.targetId，
     * apply 服务端重算时必须复现同一搜索空间，否则带 range 生成的合法 parameter 建议会重算出不同结果而被拒。
     */
    private List<@Valid @NotNull(message = "preferredRangeSelections item must not be null")
            PreferredRangeSelection> preferredRangeSelections;
}
