package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

import java.time.LocalDateTime;

@Entity
@Table(name = "trace", indexes = {
        @Index(name = "idx_trace_user_id", columnList = "user_id")
})
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class TracePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(nullable = false)
    private Long userId;

    @Column(name = "verification_task_id", nullable = false)
    private Long verificationTaskId;

    @Column(name = "violated_spec_id", nullable = false, length = 100)
    private String violatedSpecId;

    @Column(name = "violated_spec_json", columnDefinition = "JSON")
    private String violatedSpecJson;

    @Column(name = "checked_expression", columnDefinition = "TEXT")
    private String checkedExpression;

    @Column(name = "states_json", columnDefinition = "JSON", nullable = false)
    private String statesJson;

    @Column(name = "state_count")
    private Integer stateCount;

    @Column(name = "request_json", columnDefinition = "JSON")
    private String requestJson;

    @Column(name = "template_snapshots_json", columnDefinition = "JSON")
    private String templateSnapshotsJson;

    @Column(name = "model_snapshot_json", columnDefinition = "TEXT")
    private String modelSnapshotJson;

    @Column(name = "model_semantics_json", columnDefinition = "TEXT")
    private String modelSemanticsJson;

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

    private Integer disabledRuleCount;

    private Integer skippedSpecCount;

    @Column(name = "generation_issues_json", columnDefinition = "TEXT")
    private String generationIssuesJson;

    /*
     * No per-trace copy of the SMV model.
     *
     * There was a `smv_model_content TEXT` column here, holding a byte-identical duplicate of the model
     * on the owning `verification_task` row: one model string is generated per run and was written to
     * the run and to each of its traces, so a run with three violated specifications stored it four
     * times. Measured on a development database before removal: 30 trace rows carrying 345 KB of
     * duplicated model text, growing with every run.
     *
     * The duplication was justified by "a counterexample must stay self-contained after its run is
     * deleted", which the code contradicts — `VerificationServiceImpl.deleteRunInternal` deletes every
     * trace and then the run in one transaction, so a trace cannot outlive its run. The trace-keyed
     * download endpoint it fed is gone too.
     *
     * `ddl-auto: update` never drops a column, so an existing database keeps `smv_model_content` as
     * dead storage until dropped by hand. It is nullable and unread, so leaving it is harmless.
     */

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) {
            createdAt = LocalDateTime.now();
        }
    }
}
