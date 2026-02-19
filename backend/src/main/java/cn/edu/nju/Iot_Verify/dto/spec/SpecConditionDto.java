// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecConditionDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

/**
 * 规格条件 DTO
 *
 * targetType 支持:
 * - state: 检查设备状态，如 "state=cool"
 * - variable: 检查变量值，如 "temperature>30"
 * - api: 检查 API 信号，如 "fanAuto_a=FALSE"
 * - trust: 检查信任度，如 "trust_ThermostatMode_cool=untrusted"
 * - privacy: 检查隐私级别，如 "privacy_ThermostatMode_cool=private"
 */
@Data
public class SpecConditionDto {
    private String id;
    private String side;        // 'a' | 'if' | 'then'
    @NotBlank(message = "Device ID is required for spec condition")
    private String deviceId;
    private String deviceLabel;
    /**
     * 目标类型: state | variable | api | trust | privacy
     */
    @NotBlank(message = "Target type is required for spec condition")
    private String targetType;
    @NotBlank(message = "Key is required for spec condition")
    private String key;
    @NotBlank(message = "Relation is required for spec condition")
    private String relation;
    @NotBlank(message = "Value is required for spec condition")
    private String value;
}
