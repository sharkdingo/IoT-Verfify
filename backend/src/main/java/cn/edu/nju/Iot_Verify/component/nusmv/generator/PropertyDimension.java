package cn.edu.nju.Iot_Verify.component.nusmv.generator;

/**
 * Trust / Privacy 维度枚举
 * 用于合并 trust 和 privacy 的重复生成逻辑
 */
public enum PropertyDimension {
    TRUST("trust_", "trusted", "untrusted"),
    PRIVACY("privacy_", "private", "public");

    /** SMV 变量名前缀，如 "trust_" / "privacy_" */
    public final String prefix;
    /** 规则触发时设置的"激活"值，如 trusted / private */
    public final String activeValue;
    /** Value assigned when a rule fires but the propagated label is not active. */
    public final String inactiveValue;

    PropertyDimension(String prefix, String activeValue, String inactiveValue) {
        this.prefix = prefix;
        this.activeValue = activeValue;
        this.inactiveValue = inactiveValue;
    }
}
