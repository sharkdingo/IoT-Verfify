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
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionResult;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import com.volcengine.ark.runtime.model.completion.chat.ChatToolCall;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.MediaType;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicBoolean;

@Slf4j
@Service
@RequiredArgsConstructor
public class ChatServiceImpl implements ChatService {

    private static final int MAX_TOOL_ROUNDS = 5;
    private static final int HISTORY_CHAR_LIMIT = 4000;

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
            touchSessionTitle(sessionId, content);

            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, HISTORY_CHAR_LIMIT);
            List<ChatMessage> sdkMessages = arkAiClient.convertToSdkMessages(historyPO);
            sdkMessages.add(0, buildSystemPrompt());

            List<ChatTool> tools = aiToolManager.getAllToolDefinitions();
            Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
            ToolLoopResult loopResult = executeToolLoop(sessionId, sdkMessages, tools, commandSet, emitter);

            if (!commandSet.isEmpty()) {
                sendFrontendCommands(emitter, commandSet);
            }

            if (!loopResult.text().isBlank()) {
                if (sendSseChunk(emitter, loopResult.text())) {
                    finalAnswer.append(loopResult.text());
                }
            } else {
                streamAssistantReply(sdkMessages, finalAnswer, emitter);
            }

            if (finalAnswer.isEmpty() && loopResult.hadToolCalls()) {
                String fallbackText = "Operation completed. Please check the latest board data.";
                sendSseChunk(emitter, fallbackText);
                finalAnswer.append(fallbackText);
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

    private void touchSessionTitle(String sessionId, String content) {
        sessionRepo.findById(Objects.requireNonNull(sessionId, "sessionId must not be null")).ifPresent(s -> {
            s.setUpdatedAt(LocalDateTime.now());
            if ("New Chat".equals(s.getTitle()) || s.getTitle().startsWith("Chat ")) {
                String newTitle = content.length() > 12 ? content.substring(0, 12) + "..." : content;
                newTitle = newTitle.replace("\n", " ").trim();
                s.setTitle(newTitle);
            }
            sessionRepo.save(s);
        });
    }

    private ChatMessage buildSystemPrompt() {
        String systemPromptContent = """
        You are the intelligent expert assistant for the IoT-Verify platform. This is a smart home simulation and formal verification platform based on NuSMV.
        Your behavior guidelines:
        0. Markdown format isolation principle:
          - Insert a blank line before all block-level elements (tables, lists, code blocks, headers).
          - Tables must be compact without blank lines between rows.
        1. Must respond to tool results: after any tool execution, summarize outcome in natural language.
        2. Handle system notices: if a tool result contains system notice text, explicitly explain it.
        3. Explain verification/simulation in user-friendly language.
        4. Avoid exposing internal IDs unless user asks.
        5. For casual non-IoT questions, answer directly.

        Available tools:
        - Device: add_device, delete_device, search_devices
        - Rule: list_rules, manage_rule
        - Spec: list_specs, manage_spec
        - Template: list_templates, add_template, delete_template
        - Verification sync: verify_model
        - Verification async: verify_model_async, verify_task_status, cancel_verify_task
        - Simulation sync: simulate_model
        - Simulation async: simulate_model_async, simulate_task_status, cancel_simulate_task
        - Traces: list_traces
        - Board: board_overview
        """;

        return ChatMessage.builder()
                .role(ChatMessageRole.SYSTEM)
                .content(systemPromptContent)
                .build();
    }

    private ToolLoopResult executeToolLoop(String sessionId,
                                           List<ChatMessage> sdkMessages,
                                           List<ChatTool> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter) {
        boolean hadToolCalls = false;

        for (int round = 0; round < MAX_TOOL_ROUNDS; round++) {
            ChatCompletionResult result = arkAiClient.checkIntent(sdkMessages, tools);
            if (result.getChoices() == null || result.getChoices().isEmpty()) {
                return new ToolLoopResult("", hadToolCalls);
            }

            ChatMessage aiMsg = result.getChoices().get(0).getMessage();
            if (aiMsg == null) {
                return new ToolLoopResult("", hadToolCalls);
            }

            List<ChatToolCall> toolCalls = aiMsg.getToolCalls();
            if (toolCalls == null || toolCalls.isEmpty()) {
                String aiText = safeContent(aiMsg);
                if (!aiText.isBlank()) {
                    sdkMessages.add(aiMsg);
                }
                return new ToolLoopResult(aiText, hadToolCalls);
            }

            hadToolCalls = true;
            saveAiToolCallRequest(sessionId, toolCalls);
            sdkMessages.add(aiMsg);
            sendSseChunk(emitter, "Executing command...\n");

            for (ChatToolCall toolCall : toolCalls) {
                String toolCallId = toolCall != null && toolCall.getId() != null ? toolCall.getId() : "";
                String functionName = "";
                String argsJson = "{}";

                if (toolCall != null && toolCall.getFunction() != null) {
                    functionName = safeString(toolCall.getFunction().getName());
                    argsJson = safeString(toolCall.getFunction().getArguments());
                    if (argsJson.isBlank()) {
                        argsJson = "{}";
                    }
                }

                String toolResult;
                if (functionName.isBlank()) {
                    toolResult = jsonError("Invalid tool call: missing function name.");
                } else {
                    collectRefreshCommand(functionName, commandSet);
                    toolResult = aiToolManager.execute(functionName, argsJson);
                }

                saveToolExecutionResult(sessionId, toolCallId, toolResult);
                sdkMessages.add(ChatMessage.builder()
                        .role(ChatMessageRole.TOOL)
                        .content(toolResult)
                        .toolCallId(toolCallId)
                        .build());
            }
        }

        log.warn("Tool call loop reached max rounds: {}", MAX_TOOL_ROUNDS);
        return new ToolLoopResult("", hadToolCalls);
    }

    private void streamAssistantReply(List<ChatMessage> sdkMessages, StringBuilder finalAnswer, SseEmitter emitter) {
        AtomicBoolean isDisconnect = new AtomicBoolean(false);
        arkAiClient.streamChat(sdkMessages, delta -> {
            if (isDisconnect.get()) {
                return;
            }
            if (delta == null || delta.isEmpty()) {
                return;
            }
            boolean success = sendSseChunk(emitter, delta);
            if (success) {
                finalAnswer.append(delta);
            } else {
                log.info("SSE connection interrupted, stopping AI response");
                isDisconnect.set(true);
            }
        });
    }

    private void sendFrontendCommands(SseEmitter emitter, Set<StreamResponseDto.CommandDto> commandSet) {
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

    private void collectRefreshCommand(String functionName, Set<StreamResponseDto.CommandDto> commandSet) {
        switch (functionName) {
            case "add_device", "delete_device" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "device_list")));
            case "manage_rule" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "rule_list")));
            case "manage_spec" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "spec_list")));
            case "add_template", "delete_template" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "template_list")));
            case "verify_model", "verify_model_async" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "verification_result")));
            case "simulate_model", "simulate_model_async" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "simulation_result")));
            default -> {
            }
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
            po.setContent(objectMapper.writeValueAsString(Map.of(
                    "type", ArkAiClient.TOOL_CALLS_JSON_TYPE,
                    "toolCalls", toolCalls
            )));
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
        try {
            po.setContent(objectMapper.writeValueAsString(Map.of(
                    "type", ArkAiClient.TOOL_RESULT_JSON_TYPE,
                    "toolCallId", safeString(toolCallId),
                    "result", safeString(result)
            )));
        } catch (Exception e) {
            po.setContent(safeString(toolCallId) + ArkAiClient.TOOL_RESULT_SEPARATOR + safeString(result));
        }
        messageRepo.saveAndFlush(po);
    }

    private List<ChatMessagePo> getSmartHistory(String sessionId, int limitCharCount) {
        List<ChatMessagePo> allMessages = new ArrayList<>(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc(sessionId));
        java.util.Collections.reverse(allMessages);
        Deque<ChatMessagePo> safeHistory = new ArrayDeque<>();
        int currentLength = 0;

        for (int i = allMessages.size() - 1; i >= 0; i--) {
            ChatMessagePo current = allMessages.get(i);
            if (current == null) {
                continue;
            }

            if (isToolMessage(current)) {
                int assistantIndex = i;
                while (assistantIndex >= 0 && isToolMessage(allMessages.get(assistantIndex))) {
                    assistantIndex--;
                }
                int firstToolIndex = assistantIndex + 1;
                if (assistantIndex >= 0 && isAssistantToolCallMessage(allMessages.get(assistantIndex))) {
                    int blockLength = 0;
                    for (int j = assistantIndex; j <= i; j++) {
                        blockLength += messageLength(allMessages.get(j));
                    }
                    if (currentLength + blockLength > limitCharCount) {
                        break;
                    }
                    for (int j = i; j >= assistantIndex; j--) {
                        safeHistory.addFirst(allMessages.get(j));
                    }
                    currentLength += blockLength;
                    i = assistantIndex;
                    continue;
                }
                // Skip isolated tool blocks when corresponding assistant tool_call message is out of window.
                i = firstToolIndex;
                continue;
            }

            int msgLen = messageLength(current);
            if (currentLength + msgLen > limitCharCount) {
                break;
            }
            safeHistory.addFirst(current);
            currentLength += msgLen;
        }

        return new ArrayList<>(safeHistory);
    }

    private boolean isToolMessage(ChatMessagePo msg) {
        return msg != null && "tool".equalsIgnoreCase(msg.getRole());
    }

    private boolean isAssistantToolCallMessage(ChatMessagePo msg) {
        if (msg == null || !"assistant".equalsIgnoreCase(msg.getRole())) {
            return false;
        }
        String content = safeString(msg.getContent());
        if (content.startsWith(ArkAiClient.TOOL_CALLS_PREFIX)) {
            return true;
        }
        try {
            JsonNode root = objectMapper.readTree(content);
            return root.isObject()
                    && ArkAiClient.TOOL_CALLS_JSON_TYPE.equals(root.path("type").asText(""))
                    && root.has("toolCalls");
        } catch (Exception ignore) {
            return false;
        }
    }

    private int messageLength(ChatMessagePo msg) {
        return msg == null || msg.getContent() == null ? 0 : msg.getContent().length();
    }

    private String safeContent(ChatMessage message) {
        if (message == null || message.getContent() == null) {
            return "";
        }
        return message.getContent().toString();
    }

    private String safeString(String value) {
        return value == null ? "" : value;
    }

    private String jsonError(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception e) {
            return "{\"error\":\"" + message + "\"}";
        }
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

    private record ToolLoopResult(String text, boolean hadToolCalls) {
    }
}
