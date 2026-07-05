package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.ChatIntentRouter;
import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.ChatService;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.MediaType;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;
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
    private final LlmChatService llmChatService;
    private final LlmMessageCodec messageCodec;
    private final ChatIntentRouter chatIntentRouter;
    private final AiToolManager aiToolManager;
    private final ObjectMapper objectMapper;
    private final ChatMapper chatMapper;
    private final TransactionTemplate transactionTemplate;

    @Override
    @Transactional(readOnly = true)
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
    @Transactional(readOnly = true)
    public List<ChatMessageResponseDto> getHistory(Long userId, String sessionId) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        List<ChatMessagePo> visibleMessages = filterFrontendVisibleMessages(
                messageRepo.findBySessionIdOrderByCreatedAtAsc(sessionId)
        );
        return chatMapper.toChatMessageDtoList(visibleMessages);
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
        UserContextHolder.setUserId(userId);
        StringBuilder finalAnswer = new StringBuilder();
        AtomicBoolean isDisconnect = new AtomicBoolean(false);
        emitter.onCompletion(() -> isDisconnect.set(true));
        emitter.onTimeout(() -> isDisconnect.set(true));
        emitter.onError(ex -> isDisconnect.set(true));

        try {
            sessionRepo.findByIdAndUserId(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));

            transactionTemplate.executeWithoutResult(status -> {
                saveSimpleMsg(sessionId, "user", content);
                touchSessionTitle(sessionId, userId, content);
            });

            Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
            ToolLoopResult loopResult = new ToolLoopResult(false, false);
            ChatIntentRouter.Decision routeDecision = chatIntentRouter.route(content);
            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, HISTORY_CHAR_LIMIT);
            List<LlmMessage> messages = new ArrayList<>();
            messages.add(routeDecision.requiresToolLoop() ? buildToolPlanningSystemPrompt() : buildVisibleReplySystemPrompt(false));
            messages.addAll(llmChatService.toMessages(historyPO));

            if (routeDecision.requiresToolLoop()) {
                log.debug("Routing chat message to tool loop: reason={}", routeDecision.reason());
                List<LlmToolSpec> tools = aiToolManager.getAllToolDefinitions();
                loopResult = executeToolLoop(sessionId, messages, tools, commandSet, emitter, isDisconnect);
            } else {
                log.debug("Skipping tool planning for conversational chat message: reason={}", routeDecision.reason());
            }

            if (isDisconnect.get()) {
                log.info("Client disconnected during tool loop, stopping chat processing");
                return;
            }

            if (!commandSet.isEmpty()) {
                if (!sendFrontendCommands(emitter, commandSet)) {
                    isDisconnect.set(true);
                    return;
                }
            }

            if (loopResult.reachedMaxRounds()) {
                String fallbackText = "The operation required too many steps and may be incomplete. Please check the current board state.";
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                }
            } else {
                streamAssistantReply(withVisibleReplyPrompt(messages, loopResult.hadToolCalls()), finalAnswer, emitter, isDisconnect);
            }

            if (finalAnswer.isEmpty() && !isDisconnect.get()) {
                String fallbackText = loopResult.hadToolCalls()
                        ? "The operation completed, but I could not generate a final response. Please check the current board state."
                        : "I could not generate a response. Please try again.";
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                }
            }

            if (!finalAnswer.isEmpty()) {
                transactionTemplate.executeWithoutResult(status ->
                        saveSimpleMsg(sessionId, "assistant", finalAnswer.toString()));
            }
            completeEmitter(emitter, isDisconnect);
        } catch (Exception e) {
            if (isDisconnect.get() || isClientDisconnect(e)) {
                log.info("Chat stream ended after client disconnect: {}", e.toString());
                return;
            }
            log.error("Chat Error", e);
            sendSseErrorMessage(emitter, errorMessageFor(e));
        } finally {
            UserContextHolder.clear();
        }
    }

    private void touchSessionTitle(String sessionId, Long userId, String content) {
        sessionRepo.findByIdAndUserId(Objects.requireNonNull(sessionId, "sessionId must not be null"), userId).ifPresent(s -> {
            s.setUpdatedAt(LocalDateTime.now());
            if ("New Chat".equals(s.getTitle()) || s.getTitle().startsWith("Chat ")) {
                String newTitle = content.length() > 12 ? content.substring(0, 12) + "..." : content;
                newTitle = newTitle.replace("\n", " ").trim();
                s.setTitle(newTitle);
            }
            sessionRepo.save(s);
        });
    }

    private LlmMessage buildToolPlanningSystemPrompt() {
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

        Rule Recommendation Guidelines:
        - When users want to create rules or ask for rule suggestions, use recommend_rules tool first
        - analyze the device capabilities (APIs, variables, states) from the recommendation result
        - Only recommend rules using APIs and variables that actually exist in the device templates
        - Present recommended rules in a clear format and ask user to confirm before creating
        - Set confidence level based on how well the rule matches device capabilities

        Available tools:
        - Device: add_device, delete_device, search_devices
        - Rule: list_rules, manage_rule, check_duplicate_rule, recommend_rules, recommend_related_devices
        - Spec: list_specs, manage_spec, recommend_specifications
        - Template: list_templates, add_template, delete_template
        - Verification sync: verify_model
        - Verification async: verify_model_async, verify_task_status, cancel_verify_task
        - Verification traces: list_traces, get_trace, delete_trace, fix_violation
        - Simulation sync: simulate_model
        - Simulation async: simulate_model_async, simulate_task_status, cancel_simulate_task
        - Simulation traces: list_simulation_traces, get_simulation_trace, delete_simulation_trace
        - Board: board_overview
        """;

        return LlmMessage.system(systemPromptContent);
    }

    private LlmMessage buildVisibleReplySystemPrompt(boolean afterToolExecution) {
        String toolContext = afterToolExecution
                ? """
                Tool executions may already be present in the conversation history. Use those tool results
                to summarize what happened and what the user should know next.
                """
                : """
                No tools are available for this response. Answer as a normal conversational assistant.
                If the user appears to request a platform operation, ask them to state the operation clearly
                instead of inventing or printing a tool call.
                """;

        String systemPromptContent = """
        You are the intelligent expert assistant for the IoT-Verify platform. This is a smart home simulation and formal verification platform based on NuSMV.

        Visible response rules:
        - Stream only user-visible natural language or Markdown.
        - Do not emit tool-call JSON, XML tags, pseudo-tags, function names, or internal control formats.
        - Do not claim that a platform operation has been performed unless a tool result in the conversation proves it.
        - For casual non-IoT questions, answer directly.
        - Explain verification, simulation, rules, and specifications in user-friendly language.

        %s
        """.formatted(toolContext);

        return LlmMessage.system(systemPromptContent);
    }

    private List<LlmMessage> withVisibleReplyPrompt(List<LlmMessage> messages, boolean afterToolExecution) {
        List<LlmMessage> finalMessages = new ArrayList<>();
        finalMessages.add(buildVisibleReplySystemPrompt(afterToolExecution));
        if (messages != null && messages.size() > 1) {
            finalMessages.addAll(messages.subList(1, messages.size()));
        }
        return finalMessages;
    }

    private ToolLoopResult executeToolLoop(String sessionId,
                                           List<LlmMessage> messages,
                                           List<LlmToolSpec> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter,
                                           AtomicBoolean isDisconnect) {
        boolean hadToolCalls = false;

        for (int round = 0; round < MAX_TOOL_ROUNDS; round++) {
            if (isDisconnect.get()) {
                log.info("Client disconnected, stopping tool loop");
                return new ToolLoopResult(hadToolCalls, false);
            }
            LlmChatResponse response = llmChatService.chatWithTools(messages, tools);
            if (response == null) {
                log.warn("LLM provider returned null tool-planning response");
                return new ToolLoopResult(hadToolCalls, false);
            }

            List<LlmToolCall> toolCalls = response.toolCalls();
            if (toolCalls.isEmpty()) {
                String aiText = response.text();
                if (!aiText.isBlank()) {
                    log.debug("Tool planning completed with final text; regenerating visible answer through streaming.");
                }
                return new ToolLoopResult(hadToolCalls, false);
            }

            hadToolCalls = true;
            transactionTemplate.executeWithoutResult(status ->
                    saveAiToolCallRequest(sessionId, toolCalls));
            messages.add(LlmMessage.assistantToolCalls(toolCalls));

            for (LlmToolCall toolCall : toolCalls) {
                if (isDisconnect.get()) {
                    log.info("Client disconnected, stopping remaining tool calls");
                    return new ToolLoopResult(hadToolCalls, false);
                }
                String toolCallId = toolCall.id();
                String functionName = safeString(toolCall.name());
                String argsJson = safeString(toolCall.argumentsJson());
                if (argsJson.isBlank()) {
                    argsJson = "{}";
                }

                String toolResult;
                if (functionName.isBlank()) {
                    toolResult = jsonError("Invalid tool call: missing function name.", "VALIDATION_ERROR", 400);
                } else {
                    toolResult = aiToolManager.execute(functionName, argsJson);
                    if (isToolExecutionSuccessful(toolResult)) {
                        collectRefreshCommand(functionName, commandSet);
                    }
                }

                final String finalToolResult = toolResult;
                transactionTemplate.executeWithoutResult(status ->
                        saveToolExecutionResult(sessionId, toolCallId, finalToolResult));
                messages.add(LlmMessage.tool(toolCallId, toolResult));
            }
        }

        log.warn("Tool call loop reached max rounds: {}", MAX_TOOL_ROUNDS);
        return new ToolLoopResult(hadToolCalls, true);
    }

    private void streamAssistantReply(List<LlmMessage> messages,
                                      StringBuilder finalAnswer,
                                      SseEmitter emitter,
                                      AtomicBoolean isDisconnect) {
        llmChatService.streamReply(messages, delta -> {
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
        }, isDisconnect::get);
    }

    private boolean isToolExecutionSuccessful(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return false;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            if (!root.isObject()) {
                return false;
            }
            String error = root.path("error").asText("");
            return error == null || error.isBlank();
        } catch (Exception ignore) {
            return false;
        }
    }

    private boolean sendFrontendCommands(SseEmitter emitter, Set<StreamResponseDto.CommandDto> commandSet) {
        for (StreamResponseDto.CommandDto cmd : commandSet) {
            try {
                StreamResponseDto packet = new StreamResponseDto("", cmd);
                emitter.send(SseEmitter.event().data(packet, MediaType.APPLICATION_JSON));
                log.info("Sent frontend command: type={}, payload={}", cmd.getType(), cmd.getPayload());
            } catch (IOException | IllegalStateException e) {
                log.warn("Failed to send command", e);
                return false;
            }
        }
        return true;
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

    private void saveAiToolCallRequest(String sid, List<LlmToolCall> toolCalls) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("assistant");
        po.setContent(messageCodec.serializeToolCalls(toolCalls));
        messageRepo.saveAndFlush(po);
    }

    private void saveToolExecutionResult(String sid, String toolCallId, String result) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("tool");
        po.setContent(messageCodec.serializeToolResult(toolCallId, result));
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
                        // Always keep the newest coherent tool-call block,
                        // otherwise the next completion may miss required tool context.
                        if (safeHistory.isEmpty()) {
                            for (int j = i; j >= assistantIndex; j--) {
                                safeHistory.addFirst(allMessages.get(j));
                            }
                        }
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
                // Ensure the latest user/assistant message is never dropped from context.
                if (safeHistory.isEmpty()) {
                    safeHistory.addFirst(current);
                }
                break;
            }
            safeHistory.addFirst(current);
            currentLength += msgLen;
        }

        return new ArrayList<>(safeHistory);
    }

    private boolean isToolMessage(ChatMessagePo msg) {
        return messageCodec.isToolResultContent(msg);
    }

    private boolean isAssistantToolCallMessage(ChatMessagePo msg) {
        return messageCodec.isAssistantToolCallContent(msg);
    }

    private boolean isFrontendVisibleMessage(ChatMessagePo msg) {
        if (msg == null) {
            return false;
        }
        if (isToolMessage(msg) || isAssistantToolCallMessage(msg)) {
            return false;
        }
        return true;
    }

    private List<ChatMessagePo> filterFrontendVisibleMessages(List<ChatMessagePo> messages) {
        if (messages == null || messages.isEmpty()) {
            return List.of();
        }

        List<ChatMessagePo> visible = new ArrayList<>();
        for (int i = 0; i < messages.size(); i++) {
            ChatMessagePo msg = messages.get(i);
            if (!isFrontendVisibleMessage(msg)) {
                continue;
            }
            if (isAssistantToolPlaceholderAdjacentToTool(messages, i)) {
                continue;
            }
            visible.add(msg);
        }
        return visible;
    }

    private boolean isAssistantToolPlaceholderAdjacentToTool(List<ChatMessagePo> messages, int index) {
        if (messages == null || index < 0 || index >= messages.size()) {
            return false;
        }
        ChatMessagePo current = messages.get(index);
        if (current == null || !"assistant".equalsIgnoreCase(current.getRole())) {
            return false;
        }
        if (!"Calling tool...".equalsIgnoreCase(safeString(current.getContent()).trim())) {
            return false;
        }

        ChatMessagePo prev = index > 0 ? messages.get(index - 1) : null;
        ChatMessagePo next = index + 1 < messages.size() ? messages.get(index + 1) : null;
        return isToolMessage(prev) || isToolMessage(next);
    }

    private int messageLength(ChatMessagePo msg) {
        return msg == null || msg.getContent() == null ? 0 : msg.getContent().length();
    }

    private String safeString(String value) {
        return value == null ? "" : value;
    }

    private String jsonError(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }

    private boolean sendSseChunk(SseEmitter emitter, String data) {
        try {
            if (data != null) {
                StreamResponseDto chunk = new StreamResponseDto(data);
                emitter.send(SseEmitter.event().data(chunk, MediaType.APPLICATION_JSON));
                return true;
            }
        } catch (IOException | IllegalStateException e) {
            return false;
        }
        return true;
    }

    private void sendSseErrorMessage(SseEmitter emitter, String msg) {
        if (sendSseChunk(emitter, "[ERROR] " + msg)) {
            completeEmitter(emitter, new AtomicBoolean(false));
        }
    }

    private void completeEmitter(SseEmitter emitter, AtomicBoolean isDisconnect) {
        if (isDisconnect.get()) {
            return;
        }
        try {
            emitter.complete();
        } catch (IllegalStateException e) {
            isDisconnect.set(true);
            log.debug("SSE emitter was already unusable during completion: {}", e.getMessage());
        }
    }

    private String errorMessageFor(Exception e) {
        if (e instanceof ServiceUnavailableException) {
            return "AI service is temporarily unavailable. Please check the model endpoint and try again.";
        }
        if (e instanceof ResourceNotFoundException) {
            return "Chat session was not found or is no longer accessible.";
        }
        return "System error, please try again later.";
    }

    private boolean isClientDisconnect(Throwable e) {
        Throwable current = e;
        while (current != null) {
            String className = current.getClass().getName();
            String message = current.getMessage();
            if (className.contains("ClientAbortException")
                    || className.contains("AsyncRequestNotUsableException")
                    || containsIgnoreCase(message, "broken pipe")
                    || containsIgnoreCase(message, "connection reset")
                    || containsIgnoreCase(message, "response not usable")) {
                return true;
            }
            current = current.getCause();
        }
        return false;
    }

    private boolean containsIgnoreCase(String value, String needle) {
        return value != null && value.toLowerCase(java.util.Locale.ROOT).contains(needle);
    }

    private record ToolLoopResult(boolean hadToolCalls, boolean reachedMaxRounds) {
    }
}
