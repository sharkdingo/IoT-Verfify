package cn.edu.nju.Iot_Verify.dto.verification;

import lombok.Builder;
import lombok.Data;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 验证任务 DTO
 * 
 * 用于Controller层返回任务信息，不包含敏感内部字段
 */
@Data
@Builder
public class VerificationTaskDto {
    /**
     * 任务ID
     */
    private Long id;

    /**
     * 任务状态
     */
    private String status;

    /**
     * 创建时间
     */
    private LocalDateTime createdAt;

    /**
     * 开始时间
     */
    private LocalDateTime startedAt;

    /**
     * 完成时间
     */
    private LocalDateTime completedAt;

    /**
     * 处理时间（毫秒）
     */
    private Long processingTimeMs;

    /**
     * 是否安全
     */
    private Boolean isSafe;

    /**
     * 违规规格数量
     */
    private Integer violatedSpecCount;

    /**
     * 检查日志
     */
    private List<String> checkLogs;

    /**
     * 错误消息
     */
    private String errorMessage;
}
