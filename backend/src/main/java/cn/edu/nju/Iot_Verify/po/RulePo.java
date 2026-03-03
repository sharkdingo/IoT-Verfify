package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;
import java.time.LocalDateTime;

@Entity
@Table(name = "rules", indexes = {
        @Index(name = "idx_rules_user_id", columnList = "user_id")
})
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class RulePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "conditions_json", columnDefinition = "JSON")
    private String conditionsJson;

    @Column(name = "command_json", columnDefinition = "JSON")
    private String commandJson;

    @Column(name = "rule_string", columnDefinition = "TEXT")
    private String ruleString;

    @Column(name = "created_at", nullable = false)
    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        if (createdAt == null) {
            createdAt = LocalDateTime.now();
        }
    }
}
