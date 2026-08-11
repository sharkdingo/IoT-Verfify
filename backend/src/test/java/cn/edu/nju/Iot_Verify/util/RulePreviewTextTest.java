package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The preview bound exists because a rule the product accepts could compose a preview the product then
 * rejects. These tests pin that arithmetic rather than only the truncation helper, so the reason survives.
 */
class RulePreviewTextTest {

    @Test
    void aLegalRuleCanRenderAPreviewLongerThanTheCap() {
        // Reproduces the composition in ManageRuleTool.buildRuleString / FixStrategyApplier.buildRuleString:
        // "IF <label>.<attribute> <rel> <value> AND ... THEN <label>.<action>". Device labels are legal to
        // MAX_DEVICE_LABEL_LENGTH (255), so at the legal maximum condition count the rendered preview passes
        // 4000 characters well before anything else objects — measured 4226 at a 60-character label.
        String label = "D".repeat(60);
        List<String> conditions = new ArrayList<>();
        for (int i = 0; i < RequestLimits.MAX_RULE_CONDITIONS; i++) {
            conditions.add(label + ".temperature >= 25");
        }
        String rendered = "IF " + String.join(" AND ", conditions) + " THEN " + label + ".setCoolMode";

        assertTrue(rendered.length() > RequestLimits.MAX_DESCRIPTION_LENGTH,
                () -> "a rule at the legal condition cap should be able to exceed the preview cap, "
                        + "otherwise this bound guards nothing; rendered " + rendered.length());
        assertEquals(RequestLimits.MAX_DESCRIPTION_LENGTH, RulePreviewText.bounded(rendered).length());
    }

    @Test
    void marksATruncatedPreviewSoItIsNotReadAsTheCompleteRule() {
        String bounded = RulePreviewText.bounded("x".repeat(RequestLimits.MAX_DESCRIPTION_LENGTH + 1));

        assertEquals(RequestLimits.MAX_DESCRIPTION_LENGTH, bounded.length());
        assertTrue(bounded.endsWith("…"), () -> "a cut preview must say so, got tail " + bounded.substring(bounded.length() - 4));
    }

    @Test
    void leavesAPreviewAtOrBelowTheCapExactlyAsComposed() {
        String atCap = "y".repeat(RequestLimits.MAX_DESCRIPTION_LENGTH);

        assertSame(atCap, RulePreviewText.bounded(atCap));
        assertSame(null, RulePreviewText.bounded(null));
    }
}
