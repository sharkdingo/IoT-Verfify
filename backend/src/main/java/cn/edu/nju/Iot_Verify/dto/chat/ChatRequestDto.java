package cn.edu.nju.Iot_Verify.dto.chat;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Size;
import jakarta.validation.Valid;
import lombok.Data;
import lombok.ToString;

@Data
public class ChatRequestDto {

    @NotBlank(message = "Session ID is required")
    @Size(max = 64, message = "Session ID must not exceed 64 characters")
    private String sessionId;

    @NotBlank(message = "Content is required")
    @Size(max = RequestLimits.MAX_CHAT_CONTENT_LENGTH, message = "Content must not exceed 10000 characters")
    @ToString.Exclude
    private String content;

    @Size(max = 64, message = "Turn ID must not exceed 64 characters")
    private String turnId;

    @Valid
    private ChatConfirmationCommandDto confirmation;
}
