// src/main/java/cn/edu/nju/Iot_Verify/po/ChatMessagePo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.Data;
import java.time.LocalDateTime;

/**
 * 消息表：对应具体的聊天记录
 */
@Data
@Entity
@Table(name = "chat_message", indexes = {
        @Index(name = "idx_chat_message_session_id", columnList = "session_id")
})
public class ChatMessagePo {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    @Column(nullable = false)
    private String sessionId;

    @Column(nullable = false) // "user", "assistant", "system"
    private String role;

    @Column(columnDefinition = "TEXT") // 支持长文本
    private String content;

    private LocalDateTime createdAt;

    @PrePersist
    protected void onCreate() {
        createdAt = LocalDateTime.now();
    }
}