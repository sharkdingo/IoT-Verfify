package cn.edu.nju.Iot_Verify.po;

import cn.edu.nju.Iot_Verify.component.ai.state.AiSessionStateStore;
import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.EnumType;
import jakarta.persistence.Enumerated;
import jakarta.persistence.Id;
import jakarta.persistence.Index;
import jakarta.persistence.Lob;
import jakarta.persistence.PrePersist;
import jakarta.persistence.PreUpdate;
import jakarta.persistence.Table;
import jakarta.persistence.Version;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.time.Instant;

/** Durable short-lived AI workflow state, shared by every backend instance. */
@Data
@Entity
@Table(name = "ai_session_state", indexes = {
        @Index(name = "idx_ai_session_state_expiry", columnList = "expires_at"),
        @Index(name = "idx_ai_session_state_user_session", columnList = "user_id,session_id")
})
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class AiSessionStatePo {

    @Id
    @Column(name = "state_key", length = 200, nullable = false)
    @EqualsAndHashCode.Include
    private String stateKey;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "session_id", length = 64, nullable = false)
    private String sessionId;

    @Enumerated(EnumType.STRING)
    @Column(name = "state_kind", length = 40, nullable = false)
    private AiSessionStateStore.Kind stateKind;

    @Lob
    @Column(name = "payload_json", columnDefinition = "LONGTEXT", nullable = false)
    @ToString.Exclude
    private String payloadJson;

    @Column(name = "expires_at", nullable = false)
    private Instant expiresAt;

    @Version
    private Long version;

    @Column(name = "updated_at", nullable = false)
    private Instant updatedAt;

    @PrePersist
    @PreUpdate
    void touch() {
        updatedAt = Instant.now();
    }
}
