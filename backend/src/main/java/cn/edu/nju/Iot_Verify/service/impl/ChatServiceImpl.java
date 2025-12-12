package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.StreamResponseDto;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.service.ChatService;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.*;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.MediaType;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

@Slf4j
@Service
@RequiredArgsConstructor
public class ChatServiceImpl implements ChatService {

    private final ChatSessionRepository sessionRepo;
    private final ChatMessageRepository messageRepo;
    private final ArkAiClient arkAiClient;
    private final AiToolManager aiToolManager;
    private final ObjectMapper objectMapper; // Spring 自动注入 Jackson

    // ... getUserSessions, createSession, getHistory, deleteSession 保持不变 ...
    @Override
    public List<ChatSessionPo> getUserSessions(String userId) {
        return sessionRepo.findByUserIdOrderByUpdatedAtDesc(userId);
    }

    @Override
    @Transactional
    public ChatSessionPo createSession(String userId) {
        ChatSessionPo session = new ChatSessionPo();
        session.setId(UUID.randomUUID().toString());
        session.setUserId(userId);
        session.setTitle("新对话");
        session.setUpdatedAt(LocalDateTime.now());
        return sessionRepo.save(session);
    }

    @Override
    public List<ChatMessagePo> getHistory(String sessionId) {
        return messageRepo.findBySessionIdOrderByCreatedAtAsc(sessionId);
    }

    @Override
    @Transactional
    public void deleteSession(String sessionId) {
        messageRepo.deleteBySessionId(sessionId);
        sessionRepo.deleteById(sessionId);
    }

    @Override
    public void processStreamChat(String sessionId, String content, SseEmitter emitter) {
        StringBuilder finalAnswer = new StringBuilder();

        try {
            // 1. 保存用户提问
            saveSimpleMsg(sessionId, "user", content);

            // 2. 更新会话时间
            sessionRepo.findById(sessionId).ifPresent(s -> {
                s.setUpdatedAt(LocalDateTime.now());
                if (s.getTitle().equals("新对话") || s.getTitle().startsWith("对话 ")) {
                    String newTitle = content.length() > 12 ? content.substring(0, 12) + "...": content;
                    newTitle = newTitle.replace("\n", " ").trim();
                    s.setTitle(newTitle);
                }
                sessionRepo.save(s);
            });

            // 3. 准备上下文
            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, 2000);
            List<ChatMessagePo> sortedPO = new ArrayList<>(historyPO);
            Collections.reverse(sortedPO);

            List<ChatMessage> sdkMessages = arkAiClient.convertToSdkMessages(sortedPO);

            // 注入 System Prompt
            String systemPromptContent = """
        你是 IoT-Verify 平台的智能专家助手。这是一个基于 NuSMV 的智能家居仿真与形式化验证平台。
        你的行为准则：
        0. **Markdown 格式严格隔离原则（至关重要）**：
          - 必须在**所有块级元素**（表格、列表、代码块、标题）之前，**插入一个空行**（即连续按两次回车）。
          - **表格**：表格上方必须有一个空行，表格行之间必须紧凑，不要插入空行。
          - **示例**：
          文本内容...
        
          | 表头 | 内容 |
          - 代码块等也是如此
        1. **必须响应工具结果**：当工具（如 add_device, verify_model）执行完毕后，你必须根据返回的 JSON 或文本结果，用自然语言向用户汇报执行情况。严禁直接返回空内容或沉默。
        2. **处理系统提示**：如果工具返回结果中包含“【系统提示】”（例如模板不匹配导致的自动替换），你必须在回复中明确告知用户这一变更。
        3. **场景化解释**：对于设备操作，确认名称和状态；对于 NuSMV 验证结果，解释是“验证通过”还是“发现了安全反例”，并引导用户查看动画演示。
        4. **不透露数据库内的内在变量**：即用户不需要知道的变量；如在回复中提及设备时，直接使用设备名称即可。无需显示 ID（例如：不要说“设备A (ID: X)”，请直接说“设备 A”）
        5. **闲聊模式**：当用户提出的问题与 IoT 设备管理或验证无关（如数学计算、日常问候）时，直接回答问题本身，**不要解释**为什么不需要调用工具，也不要提及 IoT-Verify 平台的范畴
        6. **安全无害**：你不应该做出反人类，暴力的举动或言论
        """;

            ChatMessage systemPrompt = ChatMessage.builder()
                    .role(ChatMessageRole.SYSTEM)
                    .content(systemPromptContent)
                    .build();
            sdkMessages.add(0, systemPrompt);

            // 4. 意图识别
            List<ChatTool> tools = aiToolManager.getAllToolDefinitions();
            ChatCompletionResult result = arkAiClient.checkIntent(sdkMessages, tools);

            if (result.getChoices() == null || result.getChoices().isEmpty()) {
                sendSseErrorMessage(emitter, "AI 服务无响应");
                return;
            }

            ChatMessage aiMsg = result.getChoices().get(0).getMessage();

            // 5. 判断是否调用工具
            if (aiMsg.getToolCalls() != null && !aiMsg.getToolCalls().isEmpty()) {

                // === 分支 A: 调用工具 ===
                saveAiToolCallRequest(sessionId, aiMsg.getToolCalls());
                sdkMessages.add(aiMsg);
                sendSseChunk(emitter, "正在执行指令...\n"); // 这里可以用辅助方法，因为还没涉及断开控制

                boolean needAction = false;
                StreamResponseDto.CommandDto command = null;

                for (ChatToolCall toolCall : aiMsg.getToolCalls()) {
                    String functionName = toolCall.getFunction().getName();
                    // 如果执行的是创建或删除设备的工具，标记需要刷新，之后还需要添加
                    if (functionName.equals("add_device") || functionName.equals("delete_device")) {
                        command = new StreamResponseDto.CommandDto(
                                "REFRESH_DATA",
                                Map.of("target", "device_list") // 告诉前端刷新哪个部分
                        );
                        needAction = true;
                    }
                    String argsJson = toolCall.getFunction().getArguments();
                    String toolResult = aiToolManager.execute(functionName, argsJson);

                    saveToolExecutionResult(sessionId, toolCall.getId(), toolResult);

                    ChatMessage toolMsg = ChatMessage.builder()
                            .role(ChatMessageRole.TOOL)
                            .content(toolResult)
                            .toolCallId(toolCall.getId())
                            .build();
                    sdkMessages.add(toolMsg);
                }
                // 发送指令包
                if (needAction) {
                    try {
                        // content 为空，仅发送指令
                        // 前端收到后会触发 command 回调，但不会在对话框显示空白气泡（因为 content 是空串）
                        StreamResponseDto packet = new StreamResponseDto("", command);
                        emitter.send(SseEmitter.event().data(packet, MediaType.APPLICATION_JSON));
                    } catch (IOException e) {
                        log.warn("发送前端指令失败", e);
                    }
                }
                // 定义原子布尔值，标记前端是否断开
                AtomicBoolean isDisconnect = new AtomicBoolean(false);
                //log.info("正在进行二次请求，向 AI 汇报工具结果...");
                arkAiClient.streamChat(sdkMessages, (delta) -> {
                    // 1. 如果之前已经捕获到断开异常，直接阻断后续处理
                    if (isDisconnect.get()) return;
                    if (delta != null && !delta.isEmpty()) {
                        // 🚀 核心修改：使用辅助方法发送数据，并根据返回值判断连接状态
                        boolean success = sendSseChunk(emitter, delta);

                        if (success) {
                            finalAnswer.append(delta);
                        } else {
                            log.info("SSE 连接中断，停止接收 AI 响应");
                            isDisconnect.set(true);
                        }
                    }
                });
                // 兜底逻辑
                if (finalAnswer.isEmpty()) {
                    log.warn("AI 沉默或连接中断，触发后端兜底持久化。");
                    ChatMessage lastToolMsg = sdkMessages.get(sdkMessages.size() - 1);
                    String fallbackText = "已为您完成操作: " + lastToolMsg.getContent(); // 这里可以根据你的 System Prompt 风格调整
                    // 1. 只有没断开的时候，才往前端推
                    if (!isDisconnect.get()) {
                        sendSseChunk(emitter, fallbackText);
                    }
                    // 2. 无论是否断开，都要 append 到 finalAnswer，这样下面就会存库
                    finalAnswer.append(fallbackText);
                }
            } else {
                // === 分支 B: 普通对话 ===
                String text = aiMsg.getContent() != null ? aiMsg.getContent().toString() : "";
                if (!text.isEmpty()) {
                    // 这里直接发送全量文本，通常很快，不需要复杂的断开控制
                    sendSseChunk(emitter, text);
                    finalAnswer.append(text);
                }
            }
            // 6. 保存 AI 最终回复
            if (!finalAnswer.isEmpty()) {
                saveSimpleMsg(sessionId, "assistant", finalAnswer.toString());
            }
            emitter.complete();
        } catch (Exception e) {
            log.error("Chat Error", e);
            sendSseErrorMessage(emitter, "系统异常: " + e.getMessage());
        }
    }

    // ============ 私有辅助方法 (持久化核心) ============

    /**
     * 保存普通文本消息 (User 或 Assistant)
     */
    private void saveSimpleMsg(String sid, String role, String content) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole(role);
        po.setContent(content);
        messageRepo.saveAndFlush(po);
    }

    /**
     * 保存 AI 发起的工具调用请求
     * 格式: ArkAiClient.TOOL_CALLS_PREFIX + JSON
     */
    private void saveAiToolCallRequest(String sid, List<ChatToolCall> toolCalls) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("assistant");
        try {
            String json = objectMapper.writeValueAsString(toolCalls);
            po.setContent(ArkAiClient.TOOL_CALLS_PREFIX + json);
        } catch (Exception e) {
            log.error("序列化 ToolCalls 失败", e);
            po.setContent("调用工具中..."); // 兜底文本
        }
        messageRepo.saveAndFlush(po);
    }
    /**
     * 保存工具执行结果
     * 格式: toolCallId + ArkAiClient.TOOL_RESULT_SEPARATOR + resultJson
     */
    private void saveToolExecutionResult(String sid, String toolCallId, String result) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("tool"); // 数据库存 "tool"
        // 拼接 ID 和 内容
        po.setContent(toolCallId + ArkAiClient.TOOL_RESULT_SEPARATOR + result);
        messageRepo.saveAndFlush(po);
    }

    /**
     * 智能获取历史记录，防止 Token 爆炸
     * @param limitCharCount 估算的字符限制（中文 1字符 ≈ 0.7~1 Token）
     */
    private List<ChatMessagePo> getSmartHistory(String sessionId, int limitCharCount) {
        List<ChatMessagePo> recentMessages = messageRepo.findTop10BySessionIdOrderByCreatedAtDesc(sessionId);
        List<ChatMessagePo> safeHistory = new ArrayList<>();
        int currentLength = 0;
        for (ChatMessagePo msg : recentMessages) {
            int msgLen = (msg.getContent() == null) ? 0 : msg.getContent().length();
            if (currentLength + msgLen < limitCharCount) {
                safeHistory.add(msg);
                currentLength += msgLen;
            } else {
                break;
            }
        }
        return safeHistory;
    }

    // ============ SSE 辅助 ============

    /**
     * 发送 SSE 块 (统一 JSON 包装)
     * @return true 表示发送成功，false 表示发送失败（通常是客户端断开）
     */
    private boolean sendSseChunk(SseEmitter emitter, String data) {
        try {
            if (data != null) {
                // 统一使用 StreamResponseDto 包装，确保换行符安全传输
                StreamResponseDto chunk = new StreamResponseDto(data);
                emitter.send(SseEmitter.event().data(chunk, MediaType.APPLICATION_JSON));
                return true;
            }
        } catch (IOException e) {
            // 返回 false 让调用方知道连接已断开，可以停止 AI 生成
            return false;
        }
        return true;
    }

    private void sendSseErrorMessage(SseEmitter emitter, String msg) {
        try {
            // 🛠️ 优化：错误消息也包装成 JSON，保持协议一致性
            StreamResponseDto errorChunk = new StreamResponseDto("[ERROR] " + msg);
            emitter.send(SseEmitter.event().data(errorChunk, MediaType.APPLICATION_JSON));
            emitter.complete();
        } catch (IOException ex) {
            emitter.completeWithError(ex);
        }
    }
}