package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

/**
 * 验证任务持久化实体
 */
@Entity
@Table(name = "verification_task")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class VerificationTaskPo {

    public enum TaskStatus {
        PENDING, RUNNING, COMPLETED, FAILED, CANCELLED
    }

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    @Column(nullable = false)
    private Long userId;

    @Enumerated(EnumType.STRING)
    @Column(nullable = false)
    private TaskStatus status;

    @Column(nullable = false)
    private LocalDateTime createdAt;

    private LocalDateTime startedAt;

    private LocalDateTime completedAt;

    private Long processingTimeMs;

    private Boolean isSafe;

    private Integer violatedSpecCount;

    @Column(columnDefinition = "TEXT")
    private String checkLogsJson;

    @Column(columnDefinition = "TEXT")
    private String errorMessage;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) createdAt = LocalDateTime.now();
        if (status == null) status = TaskStatus.PENDING;
    }
}
