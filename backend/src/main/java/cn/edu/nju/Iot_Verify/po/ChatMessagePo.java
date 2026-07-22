// src/main/java/cn/edu/nju/Iot_Verify/po/ChatMessagePo.java
package cn.edu.nju.Iot_Verify.po;

import cn.edu.nju.Iot_Verify.component.ai.model.ChatExecutionStatus;
import jakarta.persistence.*;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;
import java.time.LocalDateTime;

/**
 * 消息表：对应具体的聊天记录
 */
@Data
@Entity
@Table(name = "chat_message", indexes = {
        @Index(name = "idx_chat_message_session_id", columnList = "session_id")
})
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class ChatMessagePo {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(nullable = false)
    private String sessionId;

    @Column(nullable = false) // "user", "assistant", "system"
    private String role;

    @Column(columnDefinition = "LONGTEXT")
    @ToString.Exclude
    private String content;

    @Column(name = "turn_id", length = 64)
    private String turnId;

    @Lob
    @Column(name = "execution_trace_json", columnDefinition = "LONGTEXT")
    @ToString.Exclude
    private String executionTraceJson;

    @Column(name = "execution_elapsed_seconds")
    private Integer executionElapsedSeconds;

    @Enumerated(EnumType.STRING)
    @Column(name = "execution_status", length = 32)
    private ChatExecutionStatus executionStatus;

    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        createdAt = LocalDateTime.now();
    }
}
