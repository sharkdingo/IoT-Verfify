package cn.edu.nju.Iot_Verify.dto.fix;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.Map;

/**
 * 应用某条修复建议的请求。
 *
 * <p>前端把当前展示的建议原样回传（WYSIWYG），后端在服务端重算并比对一致后把改动落库。</p>
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixApplyRequestDto {

    /** 策略名：parameter / condition / disable。必须与 suggestion.strategy 一致。 */
    @NotBlank(message = "strategy must not be blank")
    private String strategy;

    /** 用户所见的修复建议（必须是 verified 的）。 */
    @NotNull(message = "suggestion must not be null")
    private FixSuggestionDto suggestion;

    /**
     * 生成该建议时 /fix 使用的 preferredRanges（若有）。apply 服务端重算时必须复现同一搜索空间，
     * 否则带 range 生成的合法 parameter 建议会重算出不同结果而被拒。keys 形如 {@code r0_c1}。
     */
    private Map<String, PreferredRange> preferredRanges;
}
