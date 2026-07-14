// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecConditionDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Pattern;
import lombok.Data;

/**
 * 规格条件 DTO
 *
 * targetType 支持:
 * - state: 检查设备状态，如 "state=cool"
 * - mode: 检查设备模式值，如 "HvacMode=cool"
 * - variable: 检查变量值，如 "temperature>30"
 * - api: 检查 API 信号，如 "fanAuto_a=FALSE"
 * - trust: 检查当前模式状态或变量的来源标签
 * - privacy: 检查当前模式状态或变量的敏感度标签
 */
@Data
public class SpecConditionDto {
    private String id;
    @Pattern(regexp = "^(a|if|then)$", message = "Side must be one of: a, if, then")
    private String side;        // 'a' | 'if' | 'then'
    /**
     * Device reference. Board storage uses the raw DeviceNode.id; verification/simulation
     * requests use the normalized NuSMV varName. deviceLabel is display-only.
     */
    @NotBlank(message = "Device ID is required for spec condition")
    private String deviceId;
    private String deviceLabel;
    /**
     * 目标类型: state | mode | variable | api | trust | privacy
     */
    @NotBlank(message = "Target type is required for spec condition")
    @Pattern(regexp = "(?i:state|mode|variable|api|trust|privacy)",
             message = "targetType must be one of: state, mode, variable, api, trust, privacy")
    private String targetType;
    @NotBlank(message = "Key is required for spec condition")
    private String key;
    /**
     * Required only for trust/privacy. "state" means the label of the currently active
     * state in the mode named by key; "variable" means the variable named by key.
     * This keeps generated NuSMV names such as Mode_on out of the authored contract.
     */
    @Pattern(regexp = "(?i:state|variable)",
            message = "propertyScope must be one of: state, variable")
    private String propertyScope;
    @NotBlank(message = "Relation is required for spec condition")
    @Pattern(
            regexp = "^\\s*(=|==|!=|>|>=|<|<=|(?i:eq|neq|gt|gte|lt|lte|in|not_in|not in))\\s*$",
            message = "Relation must be one of =, !=, >, >=, <, <=, in, not_in, not in, or aliases EQ, NEQ, GT, GTE, LT, LTE"
    )
    private String relation;
    @NotBlank(message = "Value is required for spec condition")
    private String value;

}
