package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ChatMessageResponseDto {
    private Long id;
    private String sessionId;
    private String role;
    private String content;
    private LocalDateTime createdAt;
}
