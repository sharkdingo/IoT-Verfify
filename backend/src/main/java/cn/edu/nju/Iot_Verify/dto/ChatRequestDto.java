// src/main/java/cn/edu/nju/Iot_Verify/dto/ChatRequestDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

@Data
public class ChatRequestDto {
    // 当前会话 ID
    private String sessionId;
    // 用户本次输入的问题
    private String content;
}