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
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ChatSessionBusyException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.ChatExecutionControl;
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
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

@Slf4j
@Service
@RequiredArgsConstructor
public class ChatServiceImpl implements ChatService, ChatExecutionControl {

    private static final int MAX_TOOL_ROUNDS = 5;
    private static final int HISTORY_CHAR_LIMIT = 4000;

    private final ChatSessionRepository sessionRepo;
    private final ChatMessageRepository messageRepo;
    private final UserRepository userRepository;
    private final LlmChatService llmChatService;
    private final LlmMessageCodec messageCodec;
    private final ChatIntentRouter chatIntentRouter;
    private final AiToolManager aiToolManager;
    private final AiDestructiveActionGuard destructiveActionGuard;
    private final ObjectMapper objectMapper;
    private final ChatMapper chatMapper;
    private final TransactionTemplate transactionTemplate;
    private final ConcurrentMap<String, ActiveStreamRequest> activeStreamRequests = new ConcurrentHashMap<>();
    private final ConcurrentMap<String, Object> sessionLocks = new ConcurrentHashMap<>();

    @Override
    @Transactional(readOnly = true)
    public List<ChatSessionResponseDto> getUserSessions(Long userId) {
        return chatMapper.toChatSessionDtoList(sessionRepo.findByUserIdOrderByUpdatedAtDesc(userId));
    }

    @Override
    @Transactional
    public ChatSessionResponseDto createSession(Long userId) {
        requireActiveUserForWrite(userId);
        ChatSessionPo session = new ChatSessionPo();
        session.setId(UUID.randomUUID().toString());
        session.setUserId(userId);
        session.setTitle(null);
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
        synchronized (sessionLock(sessionId)) {
            requireActiveUserForWrite(userId);
            sessionRepo.findByIdAndUserId(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
            if (activeStreamRequests.containsKey(sessionId)) {
                throw new ChatSessionBusyException(sessionId);
            }
            messageRepo.deleteBySessionId(sessionId);
            sessionRepo.deleteById(Objects.requireNonNull(sessionId, "sessionId must not be null"));
            destructiveActionGuard.clearSession(userId, sessionId);
        }
    }

    @Override
    public void beginStreamRequest(Long userId, String sessionId) {
        synchronized (sessionLock(sessionId)) {
            sessionRepo.findByIdAndUserId(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
            ActiveStreamRequest request = new ActiveStreamRequest(userId);
            ActiveStreamRequest existing = activeStreamRequests.putIfAbsent(sessionId, request);
            if (existing != null) {
                throw new ChatSessionBusyException(sessionId);
            }
        }
    }

    @Override
    public void endStreamRequest(Long userId, String sessionId) {
        if (sessionId != null) {
            activeStreamRequests.computeIfPresent(sessionId,
                    (ignored, request) -> Objects.equals(request.userId(), userId) ? null : request);
        }
    }

    @Override
    public void requestLocalUserExecutionStop(Long userId) {
        if (userId == null) return;
        destructiveActionGuard.clearUser(userId);
        activeStreamRequests.forEach((sessionId, request) -> {
            if (!Objects.equals(request.userId(), userId)) return;
            request.stopRequested().set(true);
            SseEmitter emitter = request.emitter().get();
            if (emitter != null) {
                try {
                    emitter.complete();
                } catch (IllegalStateException e) {
                    log.debug("Chat emitter was already complete while stopping session {}", sessionId);
                }
            }
        });
    }

    @Override
    @Transactional(readOnly = true)
    public ChatSessionActivityDto getSessionActivity(Long userId, String sessionId) {
        synchronized (sessionLock(sessionId)) {
            sessionRepo.findByIdAndUserId(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
            return ChatSessionActivityDto.builder()
                    .sessionId(sessionId)
                    .active(activeStreamRequests.containsKey(sessionId))
                    .build();
        }
    }

    private Object sessionLock(String sessionId) {
        return sessionLocks.computeIfAbsent(
                Objects.requireNonNull(sessionId, "sessionId must not be null"), ignored -> new Object());
    }

    @Override
    public void processStreamChat(Long userId, String sessionId, String content, SseEmitter emitter) {
        boolean explicitConfirmation = chatIntentRouter.isExplicitConfirmation(content);
        UserContextHolder.setUserId(userId);
        UserContextHolder.setChatSessionId(sessionId);
        UserContextHolder.setDestructiveActionConfirmed(explicitConfirmation);
        if (!explicitConfirmation) {
            destructiveActionGuard.clearSession(userId, sessionId);
        }
        boolean preferChinese = prefersChinese(content);
        StringBuilder finalAnswer = new StringBuilder();
        ActiveStreamRequest activeRequest = activeStreamRequests.get(sessionId);
        AtomicBoolean isDisconnect = activeRequest != null && Objects.equals(activeRequest.userId(), userId)
                ? activeRequest.stopRequested() : new AtomicBoolean(false);
        if (activeRequest != null && Objects.equals(activeRequest.userId(), userId)) {
            activeRequest.emitter().compareAndSet(null, emitter);
        }
        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        ToolLoopResult loopResult = ToolLoopResult.empty();
        emitter.onCompletion(() -> isDisconnect.set(true));
        emitter.onTimeout(() -> isDisconnect.set(true));
        emitter.onError(ex -> isDisconnect.set(true));

        try {
            if (isDisconnect.get()) {
                try {
                    emitter.complete();
                } catch (IllegalStateException e) {
                    log.debug("Chat emitter was already complete before session {} started", sessionId);
                }
                return;
            }
            sessionRepo.findByIdAndUserId(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));

            executeOwnedSessionWrite(userId, sessionId, () -> {
                saveSimpleMsg(sessionId, "user", content);
                touchSessionTitle(sessionId, userId, content);
            });
            if (!sendSseProgress(emitter, "CONTEXT_READY", null, null)) {
                isDisconnect.set(true);
                return;
            }

            ChatIntentRouter.Decision routeDecision = chatIntentRouter.route(content);
            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, HISTORY_CHAR_LIMIT);
            List<LlmMessage> messages = new ArrayList<>();
            messages.add(routeDecision.requiresToolLoop() ? buildToolPlanningSystemPrompt() : buildVisibleReplySystemPrompt(false));
            messages.addAll(llmChatService.toMessages(historyPO));

            if (routeDecision.requiresToolLoop()) {
                log.debug("Routing chat message to tool loop: reason={}", routeDecision.reason());
                List<LlmToolSpec> tools = selectRelevantTools(
                        aiToolManager.getAllToolDefinitions(), content, routeDecision.reason());
                log.debug("Selected {} tool definition(s) for chat planning", tools.size());
                loopResult = executeToolLoop(userId, sessionId, messages, tools, commandSet, emitter, isDisconnect);
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

            String executionNotice = toolExecutionNotice(loopResult, preferChinese);
            if (!executionNotice.isBlank() && sendSseChunk(emitter, executionNotice)) {
                finalAnswer.append(executionNotice);
            }

            boolean finalResponseProduced = false;
            if (loopResult.reachedMaxRounds()) {
                String fallbackText = maxRoundsFallback(loopResult, preferChinese);
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                    finalResponseProduced = true;
                }
            } else {
                int replyStart = finalAnswer.length();
                if (!sendSseProgress(emitter, "WRITING_RESPONSE", null, null)) {
                    isDisconnect.set(true);
                    return;
                }
                streamAssistantReply(withVisibleReplyPrompt(messages, loopResult.hadToolCalls()), finalAnswer, emitter, isDisconnect);
                finalResponseProduced = finalAnswer.length() > replyStart;
            }

            if (!finalResponseProduced && !isDisconnect.get()) {
                String fallbackText = missingFinalResponseFallback(loopResult, preferChinese);
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                }
            }

            if (!finalAnswer.isEmpty()) {
                executeOwnedSessionWrite(userId, sessionId, () ->
                        saveSimpleMsg(sessionId, "assistant", finalAnswer.toString()));
            }
            completeEmitter(emitter, isDisconnect);
        } catch (Exception e) {
            if (isDisconnect.get() || isClientDisconnect(e)) {
                log.info("Chat stream ended after client disconnect: {}", e.toString());
                return;
            }
            log.error("Chat Error", e);
            String errorMessage = errorMessageFor(e, preferChinese);
            if (!commandSet.isEmpty()) {
                sendFrontendCommands(emitter, commandSet);
                errorMessage += preferChinese
                        ? " 一个或多个较早的工具写入可能已经完成；客户端已请求刷新受影响数据。重试前请检查当前状态。"
                        : " One or more earlier tool mutations may already have completed; "
                            + "the client was asked to refresh affected data. Review current state before retrying.";
            }
            sendSseErrorMessage(emitter, errorMessage);
        } finally {
            UserContextHolder.clear();
        }
    }

    private void touchSessionTitle(String sessionId, Long userId, String content) {
        sessionRepo.findByIdAndUserId(Objects.requireNonNull(sessionId, "sessionId must not be null"), userId).ifPresent(s -> {
            s.setUpdatedAt(LocalDateTime.now());
            if (isUntitledSessionTitle(s.getTitle())) {
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
        6. Treat resultAvailable=false or resultStatus=RESULT_UNAVAILABLE as an unconfirmed outcome,
           never as success. Do not retry a possibly committed mutation until refreshed state is inspected.
        7. If any tool result has requiresUserConfirmation=true, stop tool planning for this user turn.
           Never accept a proposed alternative, rename, deletion, or other pending action on the user's behalf.

        Recommendation Guidelines:
        - A recommendation is a reviewed candidate, not an applied change and not a formal-verification result.
        - If the user asks only to recommend or explore, return the candidates and ask what to apply. Do not call
          add_device, manage_rule, or manage_spec in the same turn on the user's behalf.
        - If a recommendation result reports filteredItems, truncatedCount, or adjustedItems, preserve those
          distinctions: rejected candidates have itemized reasons; truncated candidates were never inspected;
          deterministic defaults/normalizations are adjustments, not AI-authored values.
        - Applying one device/rule/specification recommendation is a targeted append. recommend_scenario is instead
          a complete scene-replacement draft and cannot be described as a local addition or as already applied.

        Rule Recommendation Guidelines:
        - When users want to create rules or ask for rule suggestions, use recommend_rules tool first
        - analyze the device capabilities (APIs, variables, modes, states) from the recommendation result
        - Only recommend rules using APIs, variables, modes, or states that actually exist in the device templates
        - Present recommended rules in a clear format and ask user to confirm before creating
        - Explain why each suggestion matches the user's goal and the available device capabilities; do not invent a numeric confidence score

        Destructive Action Guidelines:
        - Device, template, rule, specification, and saved-trace deletion is always a two-turn operation.
        - On the first turn, call the delete tool with confirmed=false and summarize the returned target and impact.
        - Stop and ask the user for explicit confirmation. Never set confirmed=true in the same user turn as the preview.
        - Set confirmed=true only when the latest user message explicitly confirms the previously previewed deletion.
        - If dependencies or target data changed after preview, explain the conflict and request a new preview.

        Available tools:
        - Device: add_device, delete_device, search_devices
        - Rule: list_rules, manage_rule, check_duplicate_rule, check_rule_similarity, recommend_rules, recommend_related_devices
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
        - Reply in the language used by the user's latest message. Preserve literal device, template, rule,
          and specification labels even when those labels use another language.
        - Do not emit tool-call JSON, XML tags, pseudo-tags, function names, or internal control formats.
        - Do not claim that a platform operation has been performed unless a tool result in the conversation proves it.
        - If a tool result has requiresUserConfirmation=true, state that no change was made, explain the exact reason and any proposed alternative or collateral impact, and ask the user to choose or confirm it.
        - If a tool result contains error/errorCode or operation=notCreated, never describe that step as completed. Explain the user-facing reason and preserve any suggested next choice.
        - If a tool result has resultAvailable=false or resultStatus=RESULT_UNAVAILABLE, state that the outcome is unconfirmed. If mutationMayHaveCommitted=true, explain that current state must be checked before retrying.
        - If a mutation result has verificationStatus=NOT_VERIFIED, say that the item was created but has not been formally verified.
        - For every recommendation result, report rawCandidateCount, inspectedCount, validatedCount/count,
          filteredCount, and truncatedCount in user language. Explain every filteredItems reason with its candidate
          label/type. Explain adjustedItems separately. Never invent a reason for truncated candidates because they
          were not inspected, and never describe a kept candidate as applied unless a later mutation result proves it.
        - A recommend_scenario result is an unverified full-replacement draft. State that applying it would replace
          devices, the shared environment pool, rules, and specifications after a separate impact confirmation.
        - For verification, only outcome=SATISFIED with modelComplete=true supports a complete checked-scope pass.
          SATISFIED with modelComplete=false means only emitted properties passed; VIOLATED proves at least one
          checked property failed but does not restore omitted scope; INCONCLUSIVE is never a safety conclusion.
          Always disclose disabledRuleCount, skippedSpecCount, and generationIssues when present.
        - Simulation is one possible formal-model trajectory, not a prediction of the physical home. If
          modelComplete=false, say which modeled rules were omitted before interpreting the trajectory.
        - Automatic-fix output is a proposal. fixable=false or an empty suggestions list must include the returned
          summary, strategy-attempt reasons, and warnings. A verified suggestion still is not applied; Board drift
          and the repaired property are checked again by the separate apply action.
        - Do not expose device node ids, rule/spec/task/trace ids, generated NuSMV names, raw formulas, or zero-based positions unless the user explicitly asks for technical details. Prefer the returned display labels and descriptions.
        - formulaPreview is descriptive preview text. Only checkedExpression is the expression actually sent to the model checker for that run.
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

    private ToolLoopResult executeToolLoop(Long userId,
                                           String sessionId,
                                           List<LlmMessage> messages,
                                           List<LlmToolSpec> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter,
                                           AtomicBoolean isDisconnect) {
        boolean hadToolCalls = false;
        int successfulToolCalls = 0;
        int failedToolCalls = 0;
        int resultUnavailableToolCalls = 0;
        int uncertainMutationCalls = 0;
        boolean confirmationPending = false;

        for (int round = 0; round < MAX_TOOL_ROUNDS; round++) {
            if (isDisconnect.get()) {
                log.info("Client disconnected, stopping tool loop");
                return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            if (!sendSseProgress(emitter, "PLANNING", null, round + 1)) {
                isDisconnect.set(true);
                return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            LlmChatResponse response = llmChatService.chatWithTools(messages, tools);
            if (isDisconnect.get()) {
                log.info("Chat execution stopped after tool planning for session {}", sessionId);
                return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            if (response == null) {
                log.warn("LLM provider returned null tool-planning response");
                return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            List<LlmToolCall> toolCalls = response.toolCalls();
            if (toolCalls.isEmpty()) {
                String aiText = response.text();
                if (!aiText.isBlank()) {
                    log.debug("Tool planning completed with final text; regenerating visible answer through streaming.");
                }
                return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            hadToolCalls = true;
            executeOwnedSessionWrite(userId, sessionId, () ->
                    saveAiToolCallRequest(sessionId, toolCalls));
            messages.add(LlmMessage.assistantToolCalls(toolCalls));

            for (LlmToolCall toolCall : toolCalls) {
                if (isDisconnect.get()) {
                    log.info("Client disconnected, stopping remaining tool calls");
                    return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                            confirmationPending);
                }
                String toolCallId = toolCall.id();
                String functionName = safeString(toolCall.name());
                String argsJson = safeString(toolCall.argumentsJson());
                if (argsJson.isBlank()) {
                    argsJson = "{}";
                }

                String toolResult;
                ToolExecutionOutcome executionOutcome;
                if (functionName.isBlank()) {
                    toolResult = jsonError("Invalid tool call: missing function name.", "VALIDATION_ERROR", 400);
                    executionOutcome = ToolExecutionOutcome.FAILED;
                } else {
                    if (!sendSseProgress(emitter, "TOOL_EXECUTION", functionName, round + 1)) {
                        isDisconnect.set(true);
                        return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                                failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                                confirmationPending);
                    }
                    toolResult = aiToolManager.execute(functionName, argsJson);
                    if (isDisconnect.get()) {
                        log.info("Chat execution stopped after tool execution for session {}", sessionId);
                        return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                                failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                                confirmationPending);
                    }
                    executionOutcome = classifyToolExecution(toolResult);
                    if (executionOutcome == ToolExecutionOutcome.USABLE
                            || (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE
                                && mutationMayHaveCommitted(toolResult))) {
                        collectRefreshCommand(functionName, commandSet);
                    }
                }

                boolean requiresConfirmation = requiresUserConfirmation(toolResult);
                if (requiresConfirmation) {
                    confirmationPending = true;
                } else if (executionOutcome == ToolExecutionOutcome.USABLE) {
                    successfulToolCalls++;
                } else if (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE) {
                    resultUnavailableToolCalls++;
                    if (mutationMayHaveCommitted(toolResult)) {
                        uncertainMutationCalls++;
                    }
                } else {
                    failedToolCalls++;
                }

                final String finalToolResult = toolResult;
                executeOwnedSessionWrite(userId, sessionId, () ->
                        saveToolExecutionResult(sessionId, toolCallId, finalToolResult));
                messages.add(LlmMessage.tool(toolCallId, toolResult));
                if (requiresConfirmation) {
                    return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls, true);
                }
                if (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE) {
                    return new ToolLoopResult(hadToolCalls, false, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls, false);
                }
            }
        }

        log.warn("Tool call loop reached max rounds: {}", MAX_TOOL_ROUNDS);
        return new ToolLoopResult(hadToolCalls, true, successfulToolCalls,
                failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                confirmationPending);
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

    private ToolExecutionOutcome classifyToolExecution(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return ToolExecutionOutcome.FAILED;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            if (!root.isObject()) {
                return ToolExecutionOutcome.FAILED;
            }
            if (root.path("requiresUserConfirmation").asBoolean(false)) {
                return ToolExecutionOutcome.FAILED;
            }
            String error = root.path("error").asText("");
            if (error != null && !error.isBlank()) {
                return ToolExecutionOutcome.FAILED;
            }
            if ((root.has("resultAvailable") && !root.path("resultAvailable").asBoolean(true))
                    || "RESULT_UNAVAILABLE".equals(root.path("resultStatus").asText())) {
                return ToolExecutionOutcome.RESULT_UNAVAILABLE;
            }
            return ToolExecutionOutcome.USABLE;
        } catch (Exception ignore) {
            return ToolExecutionOutcome.FAILED;
        }
    }

    private boolean mutationMayHaveCommitted(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return false;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            return root.isObject() && root.path("mutationMayHaveCommitted").asBoolean(false);
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

    private boolean sendSseProgress(SseEmitter emitter, String stage, String toolName, Integer round) {
        try {
            emitter.send(SseEmitter.event()
                    .data(StreamResponseDto.progress(stage, toolName, round), MediaType.APPLICATION_JSON));
            return true;
        } catch (IOException | IllegalStateException e) {
            log.debug("Failed to send chat progress stage {}: {}", stage, e.toString());
            return false;
        }
    }

    private List<LlmToolSpec> selectRelevantTools(
            List<LlmToolSpec> allTools, String content, String routeReason) {
        if (allTools == null || allTools.isEmpty()
                || "explicit_confirmation".equals(routeReason)) {
            return allTools == null ? List.of() : allTools;
        }
        String normalized = content == null ? "" : content.toLowerCase(Locale.ROOT);
        Set<String> selected = new LinkedHashSet<>();
        selected.add("board_overview");

        for (LlmToolSpec tool : allTools) {
            if (tool != null && tool.name() != null && normalized.contains(tool.name().toLowerCase(Locale.ROOT))) {
                selected.add(tool.name());
            }
        }
        if (containsAny(normalized, "device", "node", "sensor", "设备", "节点", "传感器")) {
            selected.addAll(Set.of("add_device", "delete_device", "search_devices",
                    "recommend_related_devices", "list_templates"));
        }
        if (containsAny(normalized, "rule", "automation", "trigger", "规则", "自动化", "联动", "触发")) {
            selected.addAll(Set.of("list_rules", "manage_rule", "check_duplicate_rule",
                    "check_rule_similarity", "recommend_rules"));
        }
        if (containsAny(normalized, "spec", "property", "safety", "ctl", "ltl", "规约", "安全性", "约束")) {
            selected.addAll(Set.of("list_specs", "manage_spec", "recommend_specifications"));
        }
        if (containsAny(normalized, "template", "manifest", "capabil", "模板", "清单", "能力")) {
            selected.addAll(Set.of("list_templates", "add_template", "delete_template"));
        }
        if (containsAny(normalized, "verify", "verification", "nusmv", "counterexample", "trace",
                "fix", "验证", "反例", "轨迹", "修复")) {
            selected.addAll(Set.of("verify_model", "verify_model_async", "verify_task_status",
                    "cancel_verify_task", "list_traces", "get_trace", "delete_trace", "fix_violation"));
        }
        if (containsAny(normalized, "simulate", "simulation", "scenario", "仿真", "模拟", "场景")) {
            selected.addAll(Set.of("simulate_model", "simulate_model_async", "simulate_task_status",
                    "cancel_simulate_task", "list_simulation_traces", "get_simulation_trace",
                    "delete_simulation_trace", "recommend_scenario"));
        }

        List<LlmToolSpec> filtered = allTools.stream()
                .filter(Objects::nonNull)
                .filter(tool -> selected.contains(tool.name()))
                .toList();
        return filtered.isEmpty() ? allTools : filtered;
    }

    private boolean containsAny(String value, String... needles) {
        for (String needle : needles) {
            if (value.contains(needle)) return true;
        }
        return false;
    }

    private void collectRefreshCommand(String functionName, Set<StreamResponseDto.CommandDto> commandSet) {
        switch (functionName) {
            case "add_device" -> {
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "device_list")));
                commandSet.add(new StreamResponseDto.CommandDto(
                        "REFRESH_DATA", Map.of("target", "environment_list")));
            }
            case "delete_device" -> {
                commandSet.add(new StreamResponseDto.CommandDto(
                        "REFRESH_DATA", Map.of("target", "device_list")));
                commandSet.add(new StreamResponseDto.CommandDto(
                        "REFRESH_DATA", Map.of("target", "environment_list")));
                commandSet.add(new StreamResponseDto.CommandDto(
                        "REFRESH_DATA", Map.of("target", "rule_list")));
                commandSet.add(new StreamResponseDto.CommandDto(
                        "REFRESH_DATA", Map.of("target", "spec_list")));
            }
            case "manage_rule" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "rule_list")));
            case "manage_spec" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "spec_list")));
            case "manage_environment" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "environment_list")));
            case "add_template", "delete_template" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "template_list")));
            case "verify_model", "verify_model_async", "simulate_model_async",
                    "cancel_verify_task", "cancel_simulate_task",
                    "delete_trace", "delete_simulation_trace" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "run_history")));
            default -> {
            }
        }
    }

    private String toolExecutionNotice(ToolLoopResult result, boolean preferChinese) {
        if (result == null || !result.hadToolCalls()) {
            return "";
        }
        List<String> notices = new ArrayList<>();
        if (result.failedToolCalls() > 0) {
            notices.add(preferChinese
                    ? "工具执行状态：" + result.successfulToolCalls() + " 个步骤返回了可用结果，"
                        + result.failedToolCalls() + " 个步骤失败。失败步骤未被视为已完成。"
                    : "Tool status: " + result.successfulToolCalls() + " step(s) returned a usable result; "
                        + result.failedToolCalls() + " step(s) failed. Failed steps were not treated as completed.");
        }
        if (result.resultUnavailableToolCalls() > 0) {
            String mutationNotice;
            if (preferChinese) {
                mutationNotice = result.uncertainMutationCalls() > 0
                        ? "其中 " + result.uncertainMutationCalls()
                            + " 个步骤可能已经修改了已保存状态；系统已请求刷新受影响数据。重试前请检查当前状态。"
                        : "这些未返回明细的步骤没有报告任何写入。";
                notices.add("工具执行状态：" + result.resultUnavailableToolCalls()
                        + " 个步骤没有返回可用的结果明细，因此未计为成功。" + mutationNotice);
            } else {
                mutationNotice = result.uncertainMutationCalls() > 0
                        ? " " + result.uncertainMutationCalls() + " step(s) may already have changed saved state; affected data was requested to refresh. Inspect current state before retrying."
                        : " No mutation was reported for those unavailable results.";
                notices.add("Tool status: " + result.resultUnavailableToolCalls()
                        + " step(s) returned no usable result details and were not counted as successful."
                        + mutationNotice);
            }
        }
        if (result.confirmationPending()) {
            notices.add(preferChinese
                    ? "提示：当前只是未写入的影响预览或备选方案，尚未应用；请明确确认后再继续。"
                    : "A no-write preview or proposed alternative still requires explicit confirmation. "
                        + "The pending action was not applied.");
        }
        return notices.isEmpty() ? "" : String.join(" ", notices) + "\n\n";
    }

    private String maxRoundsFallback(ToolLoopResult result, boolean preferChinese) {
        if (preferChinese) {
            return "助手已达到 " + MAX_TOOL_ROUNDS + " 轮规划上限：已获得 "
                    + result.successfulToolCalls() + " 个可用工具结果、"
                    + result.failedToolCalls() + " 个失败步骤和 "
                    + result.resultUnavailableToolCalls() + " 个结果未确认步骤。后续步骤未再尝试。"
                    + "请求可能只完成了一部分；继续前请检查刷新后的当前状态。";
        }
        return "The assistant reached its " + MAX_TOOL_ROUNDS + "-round planning limit after "
                + result.successfulToolCalls() + " usable tool result(s) and "
                + result.failedToolCalls() + " failed tool step(s), with "
                + result.resultUnavailableToolCalls() + " unconfirmed result(s). No further steps were attempted. "
                + "Some requested work may therefore be incomplete; review the refreshed current state "
                + "before continuing.";
    }

    private String missingFinalResponseFallback(ToolLoopResult result, boolean preferChinese) {
        if (result != null && result.hadToolCalls()) {
            if (preferChinese) {
                return "工具处理已结束，但未生成最终 AI 说明。期间获得 "
                        + result.successfulToolCalls() + " 个可用结果、"
                        + result.failedToolCalls() + " 个失败步骤和 "
                        + result.resultUnavailableToolCalls() + " 个未确认结果。"
                        + "不要假定整个请求已经完成；请检查刷新后的当前状态及上方的确认提示。";
            }
            return "Tool processing ended without a final AI explanation. It produced "
                    + result.successfulToolCalls() + " usable result(s) and "
                    + result.failedToolCalls() + " failed step(s), with "
                    + result.resultUnavailableToolCalls() + " unconfirmed result(s). Do not assume the whole request completed; "
                    + "review the refreshed current state and any confirmation notice above.";
        }
        return preferChinese
                ? "暂时无法生成回复，请重试。"
                : "I could not generate a response. Please try again.";
    }

    private void saveSimpleMsg(String sid, String role, String content) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole(role);
        po.setContent(content);
        messageRepo.saveAndFlush(po);
    }

    private boolean isUntitledSessionTitle(String title) {
        return title == null || title.isBlank() || "New Chat".equals(title)
                || title.matches("Chat \\d+");
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

    private void executeOwnedSessionWrite(Long userId, String sessionId, Runnable write) {
        transactionTemplate.executeWithoutResult(status -> {
            requireOwnedSessionForWrite(userId, sessionId);
            write.run();
        });
    }

    private void requireOwnedSessionForWrite(Long userId, String sessionId) {
        requireActiveUserForWrite(userId);
        sessionRepo.findByIdAndUserId(Objects.requireNonNull(sessionId, "sessionId must not be null"), userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
    }

    private void requireActiveUserForWrite(Long userId) {
        if (userId == null || userRepository.findByIdForUpdate(userId).isEmpty()) {
            throw UnauthorizedException.invalidToken();
        }
    }

    private record ActiveStreamRequest(
            Long userId,
            AtomicBoolean stopRequested,
            AtomicReference<SseEmitter> emitter) {

        private ActiveStreamRequest(Long userId) {
            this(userId, new AtomicBoolean(false), new AtomicReference<>());
        }
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

    private boolean requiresUserConfirmation(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return false;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            return root.isObject() && root.path("requiresUserConfirmation").asBoolean(false);
        } catch (Exception ignore) {
            return false;
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

    private String errorMessageFor(Exception e, boolean preferChinese) {
        if (e instanceof ServiceUnavailableException) {
            return preferChinese
                    ? "AI 服务暂时不可用，请检查模型服务地址后重试。"
                    : "AI service is temporarily unavailable. Please check the model endpoint and try again.";
        }
        if (e instanceof ResourceNotFoundException) {
            return preferChinese
                    ? "会话不存在或已无权访问。"
                    : "Chat session was not found or is no longer accessible.";
        }
        return preferChinese
                ? "系统异常，请稍后重试。"
                : "System error, please try again later.";
    }

    private boolean prefersChinese(String content) {
        return content != null && content.codePoints().anyMatch(codePoint ->
                Character.UnicodeScript.of(codePoint) == Character.UnicodeScript.HAN);
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

    private enum ToolExecutionOutcome {
        USABLE,
        FAILED,
        RESULT_UNAVAILABLE
    }

    private record ToolLoopResult(boolean hadToolCalls,
                                  boolean reachedMaxRounds,
                                  int successfulToolCalls,
                                  int failedToolCalls,
                                  int resultUnavailableToolCalls,
                                  int uncertainMutationCalls,
                                  boolean confirmationPending) {
        private static ToolLoopResult empty() {
            return new ToolLoopResult(false, false, 0, 0, 0, 0, false);
        }
    }
}
