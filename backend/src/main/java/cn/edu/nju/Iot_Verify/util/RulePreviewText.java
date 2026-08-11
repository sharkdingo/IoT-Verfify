package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;

/**
 * Bounds the human-readable rule preview at its declared limit.
 *
 * <p>Exists because the preview is composed <em>server-side</em> in two places — {@code ManageRuleTool}
 * when the model supplies no label, and {@code FixStrategyApplier} when an automatic fix rewrites a rule
 * — and both compose before validation runs. The rendered length is driven by the device labels, which
 * are legal up to {@link RequestLimits#MAX_DEVICE_LABEL_LENGTH}: measured, a rule at the legal maximum of
 * {@link RequestLimits#MAX_RULE_CONDITIONS} conditions with 60-character labels renders 4226 characters,
 * so a rule the product accepts composes a preview the product then rejects. Truncating here keeps the
 * bound (the column is {@code TEXT}, and worst case renders ~73k characters) without failing a write over
 * a display string the caller never supplied.
 */
public final class RulePreviewText {

    /** Marks a cut so the UI does not present a truncated preview as the complete rule. */
    private static final String ELLIPSIS = "…";

    public static String bounded(String preview) {
        if (preview == null || preview.length() <= RequestLimits.MAX_DESCRIPTION_LENGTH) {
            return preview;
        }
        return preview.substring(0, RequestLimits.MAX_DESCRIPTION_LENGTH - ELLIPSIS.length()) + ELLIPSIS;
    }

    private RulePreviewText() {
    }
}
