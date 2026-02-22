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
public class SimulationTracePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    @Column(nullable = false)
    private Long userId;

    private int requestedSteps;

    private int steps;

    @Column(name = "states_json", columnDefinition = "JSON", nullable = false)
    private String statesJson;

    @Column(name = "logs_json", columnDefinition = "TEXT")
    private String logsJson;

    @Column(name = "nusmv_output", columnDefinition = "TEXT")
    private String nusmvOutput;

    @Column(name = "request_json", columnDefinition = "JSON")
    private String requestJson;

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) {
            createdAt = LocalDateTime.now();
        }
    }
}
