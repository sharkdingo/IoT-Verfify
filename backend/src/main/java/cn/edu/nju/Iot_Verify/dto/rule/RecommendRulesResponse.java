package cn.edu.nju.Iot_Verify.dto.rule;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 规则推荐响应 DTO
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class RecommendRulesResponse {

    private String message;
    private Integer count;
    private List<RuleRecommendation> recommendations;

    /**
     * 单条规则推荐
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class RuleRecommendation {
        /**
         * 推荐类别: security, energy_saving, comfort, automation
         */
        private String category;

        /**
         * 规则描述（自然语言）
         */
        private String description;

        /**
         * 优先级: high, medium, low
         */
        private String priority;

        /**
         * 置信度: 0.0 - 1.0
         */
        private Double confidence;

        /**
         * 是否需要用户输入更多参数
         */
        private Boolean requiresUserInput;

        /**
         * 触发条件列表
         */
        private List<ConditionDto> conditions;

        /**
         * 执行命令
         */
        private CommandDto command;
    }

    /**
     * 条件 DTO
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class ConditionDto {
        private String deviceName;
        private String attribute;
        private String relation;
        private String value;
    }

    /**
     * 命令 DTO
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class CommandDto {
        private String deviceName;
        private String action;
        private String contentDevice;
        private String content;
    }
}
