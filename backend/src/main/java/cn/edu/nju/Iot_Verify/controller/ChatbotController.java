package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.ChatRequest;
import cn.edu.nju.Iot_Verify.service.ArkAiChatService;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.servlet.http.HttpServletResponse;
import org.springframework.web.bind.annotation.*;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;

/**
 * 与前端 ai-suspended-ball-chat 对接的接口
 */
@RestController
@RequestMapping("/api/ai")
public class ChatbotController {

    private final ArkAiChatService arkAiChatService;
    private final ObjectMapper objectMapper = new ObjectMapper();

    public ChatbotController(ArkAiChatService arkAiChatService) {
        this.arkAiChatService = arkAiChatService;
    }

    /**
     * 流式聊天接口：
     * 前端 <SuspendedBallChat url="/api/ai/chat" :enable-streaming="true" ... />
     */
    @PostMapping("/chat")
    public void chat(@RequestBody ChatRequest request, HttpServletResponse response) {

        // 1. 配置 SSE 响应头（你有全局 CorsFilter 的话，这里的 CORS 可以去掉）
        response.setContentType("text/event-stream");
        response.setCharacterEncoding("UTF-8");
        response.setHeader("Cache-Control", "no-cache");
        response.setHeader("Connection", "keep-alive");
//        response.setHeader("Access-Control-Allow-Origin", "*");

        try (PrintWriter writer = response.getWriter()) {

            // 2. 调用 service，逐块把豆包返回的内容写成组件要求的 JSON
            arkAiChatService.streamChat(request, delta -> {
                // {"code":0,"result":"...","is_end":false}\n\n
                sendSseChunk(writer, 0, delta, false);
            });

            // 3. 最后一块：告诉前端结束了
            sendSseChunk(writer, 0, "", true);

        } catch (Exception e) {
            e.printStackTrace();
            // 出错时返回一条错误 JSON（仍按组件的错误格式）
            try (PrintWriter writer = response.getWriter()) {
                Map<String, Object> err = new HashMap<>();
                err.put("code", 4);
                err.put("message", "Service Error");
                err.put("error", e.getMessage());
                writer.write(objectMapper.writeValueAsString(err) + "\n\n");
                writer.flush();
            } catch (IOException ignored) {
            }
        }
    }

    /**
     * 写出一行 SSE 数据：每行一个 JSON，对空行分隔（\n\n）
     */
    private void sendSseChunk(PrintWriter writer, int code, String result, boolean isEnd) {
        try {
            Map<String, Object> data = new HashMap<>();
            data.put("code", code);
            data.put("result", result);
            data.put("is_end", isEnd);

            String json = objectMapper.writeValueAsString(data);
            writer.write(json + "\n\n");
            writer.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
