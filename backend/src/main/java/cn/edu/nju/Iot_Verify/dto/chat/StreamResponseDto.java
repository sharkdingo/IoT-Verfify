package cn.edu.nju.Iot_Verify.dto.chat;

import lombok.Data;
import lombok.NoArgsConstructor;
import java.util.Map;

@Data
@NoArgsConstructor
public class StreamResponseDto {
    private String content;      // 正常的聊天文本
    private CommandDto command;  // <--- 改为对象，支持携带参数
    private ProgressDto progress;

    public StreamResponseDto(String content) {
        this.content = content;
    }

    public StreamResponseDto(String content, CommandDto command) {
        this.content = content;
        this.command = command;
    }

    public static StreamResponseDto progress(String stage, String toolName, Integer round) {
        return progress(stage, toolName, round, null, null, null, null, null);
    }

    public static StreamResponseDto progress(String stage,
                                             String toolName,
                                             Integer round,
                                             String outcome,
                                             Integer successfulSteps,
                                             Integer failedSteps,
                                             Integer unconfirmedSteps) {
        return progress(stage, toolName, round, outcome, successfulSteps, failedSteps, unconfirmedSteps, null);
    }

    public static StreamResponseDto progress(String stage,
                                             String toolName,
                                             Integer round,
                                             String outcome,
                                             Integer successfulSteps,
                                             Integer failedSteps,
                                             Integer unconfirmedSteps,
                                             String detail) {
        StreamResponseDto response = new StreamResponseDto();
        response.setProgress(new ProgressDto(
                stage,
                toolName,
                round,
                outcome,
                successfulSteps,
                failedSteps,
                unconfirmedSteps,
                detail
        ));
        return response;
    }

    @Data
    @NoArgsConstructor
    public static class ProgressDto {
        private String stage;
        private String toolName;
        private Integer round;
        private String outcome;
        private Integer successfulSteps;
        private Integer failedSteps;
        private Integer unconfirmedSteps;
        private String detail;

        public ProgressDto(String stage,
                           String toolName,
                           Integer round,
                           String outcome,
                           Integer successfulSteps,
                           Integer failedSteps,
                           Integer unconfirmedSteps,
                           String detail) {
            this.stage = stage;
            this.toolName = toolName;
            this.round = round;
            this.outcome = outcome;
            this.successfulSteps = successfulSteps;
            this.failedSteps = failedSteps;
            this.unconfirmedSteps = unconfirmedSteps;
            this.detail = detail;
        }
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
