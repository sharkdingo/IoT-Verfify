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
public class TracePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    @Column(nullable = false)
    private Long userId;

    @Column(name = "verification_task_id")
    private Long verificationTaskId;

    @Column(name = "violated_spec_id", nullable = false, length = 100)
    private String violatedSpecId;

    @Column(name = "violated_spec_json", columnDefinition = "JSON")
    private String violatedSpecJson;

    @Column(name = "states_json", columnDefinition = "JSON", nullable = false)
    private String statesJson;

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) {
            createdAt = LocalDateTime.now();
        }
    }
}
