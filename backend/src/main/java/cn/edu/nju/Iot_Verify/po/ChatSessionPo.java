// src/main/java/cn/edu/nju/Iot_Verify/po/ChatSessionPo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.Data;
import java.time.LocalDateTime;

@Data
@Entity
@Table(name = "chat_session")
public class ChatSessionPo {
    @Id
    private String id; // UUID

    @Column(name = "user_id", nullable = false)
    private Long userId;

    private String title; // 会话标题

    private LocalDateTime createdAt;
    private LocalDateTime updatedAt;

    @PrePersist
    protected void onCreate() {
        createdAt = LocalDateTime.now();
        updatedAt = LocalDateTime.now();
    }
}
