package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/** A bounded chat history window. {@code nextBeforeId} is an opaque older-message cursor. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ChatHistoryPageDto {
    private List<ChatMessageResponseDto> messages;
    private Long nextBeforeId;
    private boolean hasMore;
}
