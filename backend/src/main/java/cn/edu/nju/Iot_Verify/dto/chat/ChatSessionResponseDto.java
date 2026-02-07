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
public class ChatSessionResponseDto {
    private String id;
    private Long userId;
    private String title;
    private LocalDateTime createdAt;
    private LocalDateTime updatedAt;
}
