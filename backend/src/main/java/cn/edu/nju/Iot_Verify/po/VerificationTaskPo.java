package cn.edu.nju.Iot_Verify.po;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.persistence.*;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 验证任务持久化实体
 */
@Entity
@Table(name = "verification_task", indexes = {
        @Index(name = "idx_verification_task_user_id", columnList = "user_id")
})
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class VerificationTaskPo implements TaskView {

    public enum TaskStatus {
        PENDING, RUNNING, COMPLETED, FAILED, CANCELLED
    }

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Enumerated(EnumType.STRING)
    @Column(nullable = false)
    private TaskStatus status;

    @Column(nullable = false)
    private LocalDateTime createdAt;

    private LocalDateTime startedAt;

    private LocalDateTime completedAt;

    private Long processingTimeMs;

    @Column(name = "is_attack", nullable = false)
    @Builder.Default
    private Boolean isAttack = false;

    @Column(name = "attack_budget", nullable = false)
    @Builder.Default
    private Integer attackBudget = 0;

    @Column(name = "modeled_device_attack_points", nullable = false)
    @Builder.Default
    private Integer modeledDeviceAttackPointCount = 0;

    @Column(name = "modeled_falsifiable_reading_devices", nullable = false)
    @Builder.Default
    private Integer modeledFalsifiableReadingDeviceCount = 0;

    @Column(name = "modeled_automation_link_attack_points", nullable = false)
    @Builder.Default
    private Integer modeledAutomationLinkAttackPointCount = 0;

    @Column(name = "enable_privacy", nullable = false)
    @Builder.Default
    private Boolean enablePrivacy = false;

    @Column(name = "model_snapshot_json", columnDefinition = "TEXT")
    @JsonIgnore
    private String modelSnapshotJson;

    @Enumerated(EnumType.STRING)
    private VerificationOutcome outcome;

    private Integer violatedSpecCount;

    private Integer disabledRuleCount;

    private Integer skippedSpecCount;

    @Column(columnDefinition = "TEXT")
    @JsonIgnore
    private String specResultsJson;

    @Column(columnDefinition = "TEXT")
    @JsonIgnore
    private String checkLogsJson;

    @Column(columnDefinition = "TEXT")
    @JsonIgnore
    private String generationIssuesJson;

    @Transient
    private List<String> checkLogs;

    @Column(columnDefinition = "TEXT")
    private String nusmvOutput;

    @Column(columnDefinition = "TEXT")
    private String errorMessage;

    /** 0-100 progress percentage, persisted for multi-instance visibility */
    private Integer progress;

    @Override
    public boolean isTerminalStatus() {
        return status == TaskStatus.COMPLETED
                || status == TaskStatus.FAILED
                || status == TaskStatus.CANCELLED;
    }

    @Override
    public boolean isCancelledStatus() {
        return status == TaskStatus.CANCELLED;
    }

    @Override
    public String getTaskStatusName() {
        return status == null ? "UNKNOWN" : status.name();
    }

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) createdAt = LocalDateTime.now();
        if (status == null) status = TaskStatus.PENDING;
        if (isAttack == null) isAttack = false;
        if (attackBudget == null) attackBudget = 0;
        if (modeledDeviceAttackPointCount == null) modeledDeviceAttackPointCount = 0;
        if (modeledFalsifiableReadingDeviceCount == null) modeledFalsifiableReadingDeviceCount = 0;
        if (modeledAutomationLinkAttackPointCount == null) modeledAutomationLinkAttackPointCount = 0;
        if (enablePrivacy == null) enablePrivacy = false;
    }
}
