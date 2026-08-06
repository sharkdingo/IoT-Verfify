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

    @NotBlank(message = "Turn ID is required")
    @Size(max = 64, message = "Turn ID must not exceed 64 characters")
    private String turnId;

    /**
     * The UI language this turn is being read in, as a BCP 47 tag ({@code zh-CN} / {@code en}).
     *
     * <p>Without it the backend can only guess, by looking for Han characters in {@code content} — so a user
     * whose interface is Chinese got English status prose the moment they typed "hi". The guess is wrong for
     * every message that carries no Han character, which includes device ids, English product names, and
     * ordinary greetings. Optional: an absent value falls back to that inspection rather than assuming a
     * language, because an older client sending nothing must not be told its locale is English.
     */
    @Size(max = 35, message = "Locale must not exceed 35 characters")
    private String locale;

    @Valid
    private ChatConfirmationCommandDto confirmation;
}
