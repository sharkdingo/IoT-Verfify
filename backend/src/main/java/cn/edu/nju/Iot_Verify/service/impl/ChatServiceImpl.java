package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.ChatService;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
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
    private final ObjectMapper objectMapper;
    private final ChatMapper chatMapper;

    @Override
    public List<ChatSessionResponseDto> getUserSessions(Long userId) {
        return chatMapper.toChatSessionDtoList(sessionRepo.findByUserIdOrderByUpdatedAtDesc(userId));
    }

    @Override
    @Transactional
    public ChatSessionResponseDto createSession(Long userId) {
        ChatSessionPo session = new ChatSessionPo();
        session.setId(UUID.randomUUID().toString());
        session.setUserId(userId);
        session.setTitle("New Chat");
        session.setUpdatedAt(LocalDateTime.now());
        return chatMapper.toChatSessionDto(sessionRepo.save(session));
    }

    @Override
    public List<ChatMessageResponseDto> getHistory(Long userId, String sessionId) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        return chatMapper.toChatMessageDtoList(messageRepo.findBySessionIdOrderByCreatedAtAsc(sessionId));
    }

    @Override
    @Transactional
    public void deleteSession(Long userId, String sessionId) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        messageRepo.deleteBySessionId(sessionId);
        sessionRepo.deleteById(Objects.requireNonNull(sessionId, "sessionId must not be null"));
    }

    @Override
    public void processStreamChat(Long userId, String sessionId, String content, SseEmitter emitter) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));

        UserContextHolder.setUserId(userId);
        StringBuilder finalAnswer = new StringBuilder();

        try {
            saveSimpleMsg(sessionId, "user", content);

            sessionRepo.findById(Objects.requireNonNull(sessionId, "sessionId must not be null")).ifPresent(s -> {
                s.setUpdatedAt(LocalDateTime.now());
                if (s.getTitle().equals("New Chat") || s.getTitle().startsWith("Chat ")) {
                    String newTitle = content.length() > 12 ? content.substring(0, 12) + "..." : content;
                    newTitle = newTitle.replace("\n", " ").trim();
                    s.setTitle(newTitle);
                }
                sessionRepo.save(s);
            });

            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, 2000);
            List<ChatMessagePo> sortedPO = new ArrayList<>(historyPO);
            Collections.reverse(sortedPO);

            List<ChatMessage> sdkMessages = arkAiClient.convertToSdkMessages(sortedPO);

            String systemPromptContent = """
        You are the intelligent expert assistant for the IoT-Verify platform. This is a smart home simulation and formal verification platform based on NuSMV.
        Your behavior guidelines:
        0. **Markdown format isolation principle (critical)**:
          - You must insert a blank line **before all block-level elements** (tables, lists, code blocks, headers).
          - **Tables**: A blank line must precede tables, and table rows must be compact without blank lines between them.
        1. **Must respond to tool results**: When a tool (like add_device, verify_model) finishes executing, you must report the execution status in natural language based on the returned JSON or text. Never return empty content or stay silent.
        2. **Handle system prompts**: If the tool result contains "【System Notice】" (e.g., template mismatch causing auto-replacement), you must clearly inform the user of this change.
        3. **Contextual explanation**: For device operations, confirm names and states; for NuSMV verification results, explain whether it "passed verification" or "found a safety counterexample", and guide users to view the animation demo.
        4. **Hide internal variables**: Variables that users don't need to know; when mentioning devices, use device names directly. No need to show IDs.
        5. **Casual mode**: When users ask questions unrelated to IoT device management or verification (like math calculations, greetings), answer the question directly without explaining why no tool is needed.
        6. **Safe and harmless**: You should not make anti-human or violent actions or statements.
        """;

            ChatMessage systemPrompt = ChatMessage.builder()
                    .role(ChatMessageRole.SYSTEM)
                    .content(systemPromptContent)
                    .build();
            sdkMessages.add(0, systemPrompt);

            List<ChatTool> tools = aiToolManager.getAllToolDefinitions();
            ChatCompletionResult result = arkAiClient.checkIntent(sdkMessages, tools);

            if (result.getChoices() == null || result.getChoices().isEmpty()) {
                sendSseErrorMessage(emitter, "AI service not responding");
                return;
            }

            ChatMessage aiMsg = result.getChoices().get(0).getMessage();

            if (aiMsg.getToolCalls() != null && !aiMsg.getToolCalls().isEmpty()) {

                saveAiToolCallRequest(sessionId, aiMsg.getToolCalls());
                sdkMessages.add(aiMsg);
                sendSseChunk(emitter, "Executing command...\n");

                Set<StreamResponseDto.CommandDto> commandSet = new HashSet<>();

                for (ChatToolCall toolCall : aiMsg.getToolCalls()) {
                    String functionName = toolCall.getFunction().getName();
                    if (functionName.equals("add_device") || functionName.equals("delete_device")) {
                        commandSet.add(new StreamResponseDto.CommandDto(
                                "REFRESH_DATA",
                                Map.of("target", "device_list")
                        ));
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
                if (!commandSet.isEmpty()) {
                    for (StreamResponseDto.CommandDto cmd : commandSet) {
                        try {
                            StreamResponseDto packet = new StreamResponseDto("", cmd);
                            emitter.send(SseEmitter.event().data(packet, MediaType.APPLICATION_JSON));
                            log.info("Sent frontend command: type={}, payload={}", cmd.getType(), cmd.getPayload());
                        } catch (IOException e) {
                            log.warn("Failed to send command", e);
                        }
                    }
                }
                AtomicBoolean isDisconnect = new AtomicBoolean(false);
                arkAiClient.streamChat(sdkMessages, (delta) -> {
                    if (isDisconnect.get()) return;
                    if (delta != null && !delta.isEmpty()) {
                        boolean success = sendSseChunk(emitter, delta);

                        if (success) {
                            finalAnswer.append(delta);
                        } else {
                            log.info("SSE connection interrupted, stopping AI response");
                            isDisconnect.set(true);
                        }
                    }
                });
                if (finalAnswer.isEmpty()) {
                    log.warn("AI silent or connection interrupted, triggering backend fallback persistence.");
                    ChatMessage lastToolMsg = sdkMessages.get(sdkMessages.size() - 1);
                    String fallbackText = "Operation completed: " + lastToolMsg.getContent();
                    if (!isDisconnect.get()) {
                        sendSseChunk(emitter, fallbackText);
                    }
                    finalAnswer.append(fallbackText);
                }
            } else {
                String text = aiMsg.getContent() != null ? aiMsg.getContent().toString() : "";
                if (!text.isEmpty()) {
                    sendSseChunk(emitter, text);
                    finalAnswer.append(text);
                }
            }
            if (!finalAnswer.isEmpty()) {
                saveSimpleMsg(sessionId, "assistant", finalAnswer.toString());
            }
            emitter.complete();
        } catch (Exception e) {
            log.error("Chat Error", e);
            sendSseErrorMessage(emitter, "System error: " + e.getMessage());
        } finally {
            UserContextHolder.clear();
        }
    }

    private void saveSimpleMsg(String sid, String role, String content) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole(role);
        po.setContent(content);
        messageRepo.saveAndFlush(po);
    }

    private void saveAiToolCallRequest(String sid, List<ChatToolCall> toolCalls) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("assistant");
        try {
            String json = objectMapper.writeValueAsString(toolCalls);
            po.setContent(ArkAiClient.TOOL_CALLS_PREFIX + json);
        } catch (Exception e) {
            log.error("Failed to serialize ToolCalls", e);
            po.setContent("Calling tool...");
        }
        messageRepo.saveAndFlush(po);
    }

    private void saveToolExecutionResult(String sid, String toolCallId, String result) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("tool");
        po.setContent(toolCallId + ArkAiClient.TOOL_RESULT_SEPARATOR + result);
        messageRepo.saveAndFlush(po);
    }

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

    private boolean sendSseChunk(SseEmitter emitter, String data) {
        try {
            if (data != null) {
                StreamResponseDto chunk = new StreamResponseDto(data);
                emitter.send(SseEmitter.event().data(chunk, MediaType.APPLICATION_JSON));
                return true;
            }
        } catch (IOException e) {
            return false;
        }
        return true;
    }

    private void sendSseErrorMessage(SseEmitter emitter, String msg) {
        try {
            StreamResponseDto errorChunk = new StreamResponseDto("[ERROR] " + msg);
            emitter.send(SseEmitter.event().data(errorChunk, MediaType.APPLICATION_JSON));
            emitter.complete();
        } catch (IOException ex) {
            emitter.completeWithError(ex);
        }
    }
}
