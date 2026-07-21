package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.Builder;
import lombok.Value;

import java.util.List;

@Value
@Builder
public class ChatPendingConfirmationDto {
    String sessionId;
    @Builder.Default
    List<ChatConfirmationCommandDto.Kind> kinds = List.of();
}
