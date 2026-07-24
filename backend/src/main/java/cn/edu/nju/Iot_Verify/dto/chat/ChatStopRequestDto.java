package cn.edu.nju.Iot_Verify.dto.chat;

import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class ChatStopRequestDto {

    @Size(max = 64, message = "Turn ID must not exceed 64 characters")
    @Pattern(regexp = ".*\\S.*", message = "Turn ID must not be blank")
    private String turnId;
}
