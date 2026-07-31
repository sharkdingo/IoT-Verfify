package cn.edu.nju.Iot_Verify.dto.chat;

import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Positive;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class ChatTerminalSeenRequestDto {
    @NotNull
    @Positive
    private Long terminalMessageId;
}
