package cn.edu.nju.Iot_Verify.po;

import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.persistence.*;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

@Entity
@Table(name = "simulation_task", indexes = {
        @Index(name = "idx_simulation_task_user_id", columnList = "user_id")
})
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class SimulationTaskPo {

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

    private Integer requestedSteps;

    private Integer steps;

    private Long simulationTraceId;

    @Column(columnDefinition = "TEXT")
    @JsonIgnore
    private String checkLogsJson;

    @Transient
    private List<String> checkLogs;

    @Column(columnDefinition = "TEXT")
    private String errorMessage;

    /** 0-100 progress percentage, persisted for multi-instance visibility */
    private Integer progress;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) createdAt = LocalDateTime.now();
        if (status == null) status = TaskStatus.PENDING;
    }
}

