package cn.edu.nju.Iot_Verify.po;

import com.fasterxml.jackson.annotation.JsonIgnore;
import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.GeneratedValue;
import jakarta.persistence.GenerationType;
import jakarta.persistence.Id;
import jakarta.persistence.Index;
import jakarta.persistence.PrePersist;
import jakarta.persistence.Table;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

@Entity
@Table(name = "fuzz_finding", indexes = {
        @Index(name = "idx_fuzz_finding_user_run", columnList = "user_id,fuzz_task_id"),
        @Index(name = "idx_fuzz_finding_spec", columnList = "violated_spec_id")
})
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class FuzzFindingPo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "fuzz_task_id", nullable = false)
    private Long fuzzTaskId;

    @Column(name = "violated_spec_id", nullable = false, length = 100)
    private String violatedSpecId;

    @Column(name = "violated_spec_json", nullable = false, columnDefinition = "LONGTEXT")
    @JsonIgnore
    private String violatedSpecJson;

    @Column(name = "first_violation_step", nullable = false)
    private Integer firstViolationStep;

    @Column(name = "states_json", nullable = false, columnDefinition = "LONGTEXT")
    @JsonIgnore
    private String statesJson;

    @Column(name = "input_events_json", nullable = false, columnDefinition = "LONGTEXT")
    @JsonIgnore
    private String inputEventsJson;

    @Column(nullable = false)
    private Long seed;

    @Column(name = "state_count", nullable = false)
    private Integer stateCount;

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) createdAt = LocalDateTime.now();
        if (stateCount == null) stateCount = 0;
    }
}
