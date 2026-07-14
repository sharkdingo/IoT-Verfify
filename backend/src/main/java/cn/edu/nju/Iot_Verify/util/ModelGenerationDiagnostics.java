package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;

import java.util.List;

/** Structured counts derived from the generator's stable check-log markers. */
public final class ModelGenerationDiagnostics {

    private static final String DISABLED_RULE_MARKER = "[rule-disabled]";

    private ModelGenerationDiagnostics() {}

    public static int disabledRuleCount(List<String> logs) {
        if (logs == null) return 0;
        return (int) logs.stream()
                .filter(java.util.Objects::nonNull)
                .filter(log -> log.contains(DISABLED_RULE_MARKER))
                .count();
    }

    public static int disabledRuleCount(List<ModelGenerationIssueDto> issues, List<String> fallbackLogs) {
        if (issues != null && !issues.isEmpty()) {
            return (int) issues.stream()
                    .filter(java.util.Objects::nonNull)
                    .filter(issue -> "RULE_DISABLED".equals(issue.getIssueType()))
                    .count();
        }
        return disabledRuleCount(fallbackLogs);
    }
}
