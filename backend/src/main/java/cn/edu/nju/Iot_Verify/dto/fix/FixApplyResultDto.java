package cn.edu.nju.Iot_Verify.dto.fix;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 应用修复建议后的结果。
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixApplyResultDto {

    /** 是否成功落库。 */
    private boolean applied;

    /** 已应用的策略。 */
    private String strategy;

    /** Whether the server recomputed and forward-verified the applied suggestion. */
    private boolean verificationRechecked;

    /** Whether prior verification evidence was reused after the complete model snapshot matched. */
    private boolean verificationEvidenceReused;

    /** The signed suggestion that was actually applied. */
    private FixSuggestionDto appliedSuggestion;

    private int previousRuleCount;

    private int currentRuleCount;

    /** 人类可读的结果说明（成功摘要或拒绝原因）。 */
    private String message;

    /** 落库后的完整规则列表（前端据此刷新，无需再拉一次）。 */
    private List<RuleDto> rules;
}
