package cn.edu.nju.Iot_Verify.component.aitool.spec;

/** Single model-facing authority for IoT-Verify specification template semantics. */
public final class SpecificationTemplateSemantics {

    private SpecificationTemplateSemantics() {
    }

    public static String chinesePromptReference() {
        return """
                1. Always: AG(A)。仅使用 aConditions；A 的合取在所有路径的所有状态都必须成立，不是 IF/THEN 条件句。
                2. Eventually: AF(A)。仅使用 aConditions；从初始状态出发，A 在所有路径上最终成立，不是 EF，也没有前置触发条件。
                3. Never: AG !(A)。仅使用 aConditions；A 的合取在所有建模路径中永不发生。
                4. Immediate: AG((IF) -> AX(THEN))。仅使用 ifConditions/thenConditions；IF 成立后的下一状态满足 THEN。
                5. Response: AG((IF) -> AF(THEN))。仅使用 ifConditions/thenConditions；IF 成立后，THEN 在所有后续路径上最终成立。
                6. Persistence: G((IF) -> F G(THEN))。仅使用 ifConditions/thenConditions；IF 成立后，THEN 最终开始持续成立。
                7. Untrusted-source safety: AG !(A 与其解析出的 untrusted 来源标签)。仅使用 aConditions；它保护事件不被不可信来源触发，不等同于普通 Never。
                """;
    }
}
