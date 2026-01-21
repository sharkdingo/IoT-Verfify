package cn.edu.nju.Iot_Verify.dto;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class ChatRequestDto {

    @NotBlank(message = "Session ID is required")
    private String sessionId;

    @NotBlank(message = "Content is required")
    private String content;
}
