package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

import java.time.LocalDateTime;

/**
 * 模拟轨迹持久化实体
 */
@Entity
@Table(name = "simulation_trace", indexes = {
        @Index(name = "idx_sim_trace_user_id", columnList = "user_id")
})
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class SimulationTracePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(nullable = false)
    private Long userId;

    private int requestedSteps;

    private int steps;

    @Column(name = "states_json", columnDefinition = "JSON", nullable = false)
    private String statesJson;

    @Column(name = "logs_json", columnDefinition = "TEXT")
    private String logsJson;

    @Column(name = "generation_issues_json", columnDefinition = "TEXT")
    private String generationIssuesJson;

    @Column(name = "nusmv_output", columnDefinition = "TEXT")
    private String nusmvOutput;

    @Column(name = "request_json", columnDefinition = "JSON")
    private String requestJson;

    @Column(name = "template_snapshots_json", columnDefinition = "JSON")
    private String templateSnapshotsJson;

    @Column(name = "model_snapshot_json", columnDefinition = "TEXT")
    private String modelSnapshotJson;

    @Column(name = "is_attack")
    private Boolean isAttack;

    @Column(name = "attack_budget")
    private Integer attackBudget;

    @Column(name = "enable_privacy")
    private Boolean enablePrivacy;

    @Column(name = "modeled_device_attack_point_count")
    private Integer modeledDeviceAttackPointCount;

    @Column(name = "modeled_falsifiable_reading_device_count")
    private Integer modeledFalsifiableReadingDeviceCount;

    @Column(name = "modeled_automation_link_attack_point_count")
    private Integer modeledAutomationLinkAttackPointCount;

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) {
            createdAt = LocalDateTime.now();
        }
    }
}
