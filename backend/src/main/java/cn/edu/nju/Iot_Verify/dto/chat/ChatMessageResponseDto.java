package cn.edu.nju.Iot_Verify.dto.chat;

import cn.edu.nju.Iot_Verify.component.ai.model.ChatExecutionStatus;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.ToString;

import java.time.LocalDateTime;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ChatMessageResponseDto {
    private Long id;
    private String sessionId;
    private String role;
    @ToString.Exclude
    private String content;
    private String turnId;
    private LocalDateTime createdAt;
    @ToString.Exclude
    private List<StreamResponseDto.ProgressDto> executionTrace;
    private Integer executionElapsedSeconds;
    private ChatExecutionStatus executionStatus;
}
