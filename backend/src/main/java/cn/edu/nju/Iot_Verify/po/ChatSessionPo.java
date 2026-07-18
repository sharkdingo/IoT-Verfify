// src/main/java/cn/edu/nju/Iot_Verify/po/ChatSessionPo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.Data;
import lombok.EqualsAndHashCode;
import java.time.LocalDateTime;

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

    @Column(name = "active_execution_expires_at")
    private LocalDateTime activeExecutionExpiresAt;

    @Column(name = "execution_stop_requested")
    private Boolean executionStopRequested;

    @Column(name = "execution_user_stop_requested")
    private Boolean executionUserStopRequested;

    @PrePersist
    protected void onCreate() {
        createdAt = LocalDateTime.now();
        updatedAt = LocalDateTime.now();
    }
}
