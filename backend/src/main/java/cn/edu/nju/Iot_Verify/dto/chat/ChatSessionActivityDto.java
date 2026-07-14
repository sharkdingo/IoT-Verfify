package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ChatSessionActivityDto {
    private String sessionId;
    private boolean active;
}
