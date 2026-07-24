// src/main/java/cn/edu/nju/Iot_Verify/po/ChatSessionPo.java
package cn.edu.nju.Iot_Verify.po;

import java.time.LocalDateTime;
import java.util.LinkedHashSet;
import java.util.Set;

import jakarta.persistence.*;
import lombok.Data;
import lombok.EqualsAndHashCode;
import org.hibernate.annotations.OnDelete;
import org.hibernate.annotations.OnDeleteAction;

@Data
@Entity
@Table(name = "chat_session", indexes = {
        @Index(name = "idx_chat_session_user_id", columnList = "user_id")
})
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class ChatSessionPo {
    @Id
    @EqualsAndHashCode.Include
    private String id; // UUID

    @Column(name = "user_id", nullable = false)
    private Long userId;

    private String title; // 会话标题

    private LocalDateTime createdAt;
    private LocalDateTime updatedAt;

    @Column(name = "active_execution_id", length = 36)
    private String activeExecutionId;

    @Column(name = "active_execution_turn_id", length = 64)
    private String activeExecutionTurnId;

    @Column(name = "active_execution_expires_at")
    private LocalDateTime activeExecutionExpiresAt;

    @Column(name = "execution_stop_requested")
    private Boolean executionStopRequested;

    @Column(name = "execution_user_stop_requested")
    private Boolean executionUserStopRequested;

    @ElementCollection
    @CollectionTable(
            name = "chat_session_pre_admission_stop",
            joinColumns = @JoinColumn(name = "session_id"),
            foreignKey = @ForeignKey(name = "fk_chat_pre_admission_stop_session"),
            uniqueConstraints = @UniqueConstraint(
                    name = "uk_chat_pre_admission_stop_session_turn",
                    columnNames = {"session_id", "turn_id"}))
    @Column(name = "turn_id", nullable = false, length = 64)
    @OnDelete(action = OnDeleteAction.CASCADE)
    private Set<String> preAdmissionStopTurnIds = new LinkedHashSet<>();

    @PrePersist
    protected void onCreate() {
        if (createdAt != null && updatedAt != null) return;
        LocalDateTime now = LocalDateTime.now();
        if (createdAt == null) createdAt = now;
        if (updatedAt == null) updatedAt = now;
    }
}
