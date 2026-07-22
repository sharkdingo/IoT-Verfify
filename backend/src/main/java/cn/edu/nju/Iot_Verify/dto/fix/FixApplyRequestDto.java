package cn.edu.nju.Iot_Verify.dto.fix;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.ToString;

import java.util.List;

/**
 * 应用某条修复建议的请求。
 *
 * <p>The client submits the exact displayed suggestion and its server-issued signature. The server
 * verifies the signature and current board snapshot before persisting that same suggestion.</p>
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

    @Valid
    @NotNull(message = "suggestion must not be null")
    private FixSuggestionDto suggestion;

    @NotBlank(message = "suggestionToken must not be blank")
    @ToString.Exclude
    private String suggestionToken;

    /**
     * 生成该建议时 /fix 使用的参数范围选择（若有）。每项选择使用 ParameterTarget.targetId，
     * The signed suggestion binds these ranges so a different parameter search cannot be applied.
     */
    private List<@Valid @NotNull(message = "preferredRangeSelections item must not be null")
            PreferredRangeSelection> preferredRangeSelections;
}
