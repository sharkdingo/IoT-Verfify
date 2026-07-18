package cn.edu.nju.Iot_Verify.component.nusmv.generator;

/** Initialization policy for one generated NuSMV attack-choice variable. */
public enum AttackActivation {
    DISABLED,
    NONDETERMINISTIC,
    FIXED_COMPROMISED,
    FIXED_SAFE;

    public boolean isModeled() {
        return this != DISABLED;
    }

    public String initialExpression() {
        return switch (this) {
            case NONDETERMINISTIC -> "{TRUE, FALSE}";
            case FIXED_COMPROMISED -> "TRUE";
            case FIXED_SAFE -> "FALSE";
            case DISABLED -> throw new IllegalStateException("Disabled attack points have no initializer");
        };
    }
}
