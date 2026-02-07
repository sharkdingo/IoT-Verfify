package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.Data;
import lombok.NoArgsConstructor;
import java.util.Map;

@Data
@NoArgsConstructor
public class StreamResponseDto {
    private String content;      // 正常的聊天文本
    private CommandDto command;  // <--- 改为对象，支持携带参数

    public StreamResponseDto(String content) {
        this.content = content;
    }

    public StreamResponseDto(String content, CommandDto command) {
        this.content = content;
        this.command = command;
    }

    // 内部静态类或独立文件定义 CommandDto
    @Data
    @NoArgsConstructor
    public static class CommandDto {
        private String type;             // 指令类型，如 "REFRESH_DATA", "SHOW_TOAST", "NAVIGATE"
        private Map<String, Object> payload; // 指令参数，如 {"target": "device_list"}, {"url": "/rules"}

        public CommandDto(String type, Map<String, Object> payload) {
            this.type = type;
            this.payload = payload;
        }
    }
}