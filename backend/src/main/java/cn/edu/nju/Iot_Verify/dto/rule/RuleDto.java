package cn.edu.nju.Iot_Verify.dto.rule;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 规则 DTO
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class RuleDto {

    private Long id;
    private Long userId;

    @Valid
    @NotNull(message = "Conditions cannot be null")
    private List<Condition> conditions;

    @Valid
    @NotNull(message = "Command cannot be null")
    private Command command;

    private String ruleString;

    /**
     * 条件
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class Condition {
        /**
         * 来源设备名称
         */
        @NotBlank(message = "Condition device name is required")
        private String deviceName;

        /**
         * 属性（如 state、temperature）
         */
        @NotBlank(message = "Condition attribute is required")
        private String attribute;

        /**
         * 关系（=、>、<）
         */
        @NotBlank(message = "Condition relation is required")
        private String relation;

        /**
         * 值
         */
        @NotBlank(message = "Condition value is required")
        private String value;
    }

    /**
     * 命令
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class Command {
        /**
         * 目标设备名称
         */
        @NotBlank(message = "Command device name is required")
        private String deviceName;

        /**
         * 动作/API
         */
        @NotBlank(message = "Command action is required")
        private String action;

        /**
         * 隐私设备
         */
        private String contentDevice;

        /**
         * 隐私内容
         */
        private String content;
    }
}
