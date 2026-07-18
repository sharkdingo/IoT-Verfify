package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.AiTaskContinuationStore;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationDecision;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationKind;
import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.AiScenarioDraftStore;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
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
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ObjectNode;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.http.MediaType;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.io.IOException;
import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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

    private static final int HISTORY_CHAR_LIMIT = 4000;
    private static final Set<String> CONTINUATION_SENSITIVE_FIELDS = Set.of(
            "impactToken", "confirmationToken", "domainImpactToken");

    private final ChatSessionRepository sessionRepo;
    private final ChatMessageRepository messageRepo;
    private final UserRepository userRepository;
    private final LlmChatService llmChatService;
    private final LlmMessageCodec messageCodec;
    private final ChatConfirmationDetector chatConfirmationDetector;
    private final AiToolManager aiToolManager;
    private final AiDestructiveActionGuard destructiveActionGuard;
    private final AiScenarioDraftStore scenarioDraftStore;
    private final AiTaskContinuationStore taskContinuationStore;
    private final ObjectMapper objectMapper;
    private final ChatMapper chatMapper;
    private final TransactionTemplate transactionTemplate;
    private final ChatExecutionConfig chatExecutionConfig;
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
        List<ChatMessagePo> allMessages = messageRepo.findBySessionIdOrderByCreatedAtAsc(sessionId);
        List<ChatMessagePo> visibleMessages = filterFrontendVisibleMessages(allMessages);
        List<ChatMessageResponseDto> response = chatMapper.toChatMessageDtoList(visibleMessages);
        attachPersistedExecutionTraces(allMessages, visibleMessages, response);
        return response;
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
            scenarioDraftStore.clearSession(sessionId);
            taskContinuationStore.clearSession(sessionId);
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
        scenarioDraftStore.clearUser(userId);
        taskContinuationStore.clearUser(userId);
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
        AiDestructiveActionGuard.PendingActionContext destructivePending = destructiveActionGuard
                .pendingContext(userId, sessionId)
                .orElse(null);
        AiScenarioDraftStore.PendingApplication scenarioPending = scenarioDraftStore
                .pendingApplication(userId, sessionId)
                .orElse(null);
        AiTaskContinuationStore.ContinuationContext continuationContext = taskContinuationStore
                .pendingContext(userId, sessionId)
                .orElse(null);
        EnumSet<ConfirmationKind> pendingKinds = EnumSet.noneOf(ConfirmationKind.class);
        if (destructivePending != null) {
            pendingKinds.add("reset_default_templates".equals(destructivePending.toolName())
                    ? ConfirmationKind.DEFAULT_TEMPLATE_RESET
                    : ConfirmationKind.DESTRUCTIVE);
        }
        if (scenarioPending != null) pendingKinds.add(ConfirmationKind.SCENE_REPLACEMENT);
        if (pendingKinds.isEmpty() && continuationContext != null
                && continuationContext.pendingToolName() != null) {
            pendingKinds.add(ConfirmationKind.CHOICE);
        }
        ConfirmationDecision confirmationDecision = chatConfirmationDetector.detect(content, pendingKinds);
        UserContextHolder.setUserId(userId);
        UserContextHolder.setChatSessionId(sessionId);
        UserContextHolder.setConfirmedProtectedActionKind(
                confirmationDecision.confirmed() && confirmationDecision.kind() != ConfirmationKind.CHOICE
                        ? confirmationDecision.kind().name()
                        : null);
        if (confirmationDecision.cancelled()) {
            clearCancelledPendingAction(userId, sessionId, confirmationDecision.kind());
        }
        boolean preferChinese = prefersChinese(content);
        StringBuilder finalAnswer = new StringBuilder();
        List<StreamResponseDto.ProgressDto> executionTrace = new ArrayList<>();
        long executionStartedNanos = System.nanoTime();
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
            if (!sendSseProgress(emitter, "CONTEXT_READY", null, null,
                    null, null, null, executionTrace)) {
                isDisconnect.set(true);
                return;
            }

            List<ChatMessagePo> historyPO = getSmartHistory(sessionId, HISTORY_CHAR_LIMIT);
            List<LlmMessage> messages = new ArrayList<>();
            messages.add(buildToolPlanningSystemPrompt());
            messages.addAll(llmChatService.toMessages(historyPO));
            LlmMessage pendingTaskContext = buildPendingTaskSystemPrompt(
                    destructivePending,
                    scenarioPending,
                    continuationContext,
                    confirmationDecision,
                    content);
            if (pendingTaskContext != null) {
                messages.add(pendingTaskContext);
                if (confirmationDecision.confirmed() && continuationContext != null && !sendSseProgress(
                        emitter,
                        "TASK_RESUMED",
                        null,
                        null,
                        null,
                        null,
                        compactProgressDetail(continuationContext.originalObjective()),
                        executionTrace)) {
                    isDisconnect.set(true);
                    return;
                }
            }

            List<LlmToolSpec> availableTools = aiToolManager.getAllToolDefinitions();
            List<LlmToolSpec> tools = availableTools == null ? List.of() : availableTools;
            log.debug("Starting model-driven planning with the complete {}-tool catalog", tools.size());
            loopResult = executeToolLoop(
                    userId, sessionId, messages, tools, commandSet, emitter, isDisconnect,
                    preferChinese, executionTrace);

            if (loopResult.confirmationPending()) {
                taskContinuationStore.savePendingStep(
                        userId,
                        sessionId,
                        continuationContext == null ? content : continuationContext.originalObjective(),
                        content,
                        loopResult.pendingToolName(),
                        sanitizePendingResultForContinuation(loopResult.pendingToolResult()));
            } else if (shouldPreservePendingTask(
                    userId,
                    sessionId,
                    destructivePending != null || scenarioPending != null,
                    continuationContext,
                    confirmationDecision,
                    loopResult)) {
                taskContinuationStore.rememberUserMessage(userId, sessionId, content);
            } else {
                taskContinuationStore.clear(userId, sessionId);
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

            String guardNotice = executionGuardNotice(loopResult, preferChinese);
            if (!guardNotice.isBlank() && sendSseChunk(emitter, guardNotice)) {
                finalAnswer.append(guardNotice);
            }

            int replyStart = finalAnswer.length();
            if (!sendSseProgress(emitter, "WRITING_RESPONSE", null, null,
                    null, loopResult, null, executionTrace)) {
                isDisconnect.set(true);
                return;
            }
            streamAssistantReply(withVisibleReplyPrompt(messages, loopResult), finalAnswer, emitter, isDisconnect);
            boolean finalResponseProduced = finalAnswer.length() > replyStart;

            if (!finalResponseProduced && !isDisconnect.get()) {
                String fallbackText = missingFinalResponseFallback(loopResult, preferChinese);
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                }
            }

            if (!finalAnswer.isEmpty()) {
                int elapsedSeconds = (int) Math.min(
                        Integer.MAX_VALUE,
                        Math.max(0L, (System.nanoTime() - executionStartedNanos) / 1_000_000_000L));
                executeOwnedSessionWrite(userId, sessionId, () ->
                        saveAssistantMsg(
                                sessionId,
                                finalAnswer.toString(),
                                executionTrace,
                                elapsedSeconds));
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
        8. Plan toward the user's complete objective, not toward a fixed workflow. The registered tools are
           composable capabilities: freely combine reads, targeted writes, deletion previews, creation, rules,
           specifications, simulation, verification, and status checks when their schemas and results support it.
           Continue until the objective is complete or a real confirmation, unavailable-result, or safety boundary
           requires a new user turn. Do not stop merely because one successful tool call finished.
        9. ReAct activity summary:
          - Whenever you return tool calls, also return a concise user-visible reasoning summary in the assistant
            text for that planning round: what the current goal is, which observed facts matter, why the selected
            action is the next useful step, and what remains afterward.
          - This is an audit-friendly summary, not private hidden chain-of-thought. Never include opaque tokens,
            internal ids, raw control context, or unsupported assumptions.

        Recommendation Guidelines:
        - The complete tool catalog is available in every planning round. Choose tools from their schemas and chain
          read, recommendation, mutation, verification, and status tools as needed; do not wait for a tool name or
          keyword in the user's message.
        - For any question about the current scene, including counts of devices, rules, or specifications, use
          board_overview and answer from its current counts and semantic data rather than chat history. Do not call
          it ritualistically when server-authoritative confirmation context or a fresh tool result already provides
          the exact state needed for the next step.
        - To extend or complete the existing scene, inspect current Board state only when the task depends on facts
          not already supplied by the user or a fresh tool result. Then freely compose recommendation, mutation,
          simulation, verification, and status tools. Before add_device, use list_templates only when an exact valid
          template name is not already known. Never replace a user-supplied exact value with a recommendation merely
          because a recommendation tool exists. Preserve existing scene content unless full replacement is requested.
        - A recommendation is a reviewed candidate, not an applied change and not a formal-verification result.
        - If the user asks only to recommend or explore, return the candidates and ask what to apply. Do not call
          add_device, manage_rule, or manage_spec in the same turn on the user's behalf.
        - If a recommendation result reports filteredItems, truncatedCount, or adjustedItems, preserve those
          distinctions: rejected candidates have itemized reasons; truncated candidates were never inspected;
          deterministic defaults/normalizations are adjustments, not AI-authored values.
        - Applying one device/rule/specification recommendation is a targeted append. Use recommend_scenario only
          when the user explicitly requests a complete replacement/import draft; it cannot be described as a local
          addition or as already applied.
        - If the user asks to apply the latest recommend_scenario draft, call apply_scenario with confirmed=false.
          Do not call board_overview and do not delete or recreate devices individually. apply_scenario owns the
          authoritative current-board preview and the atomic full-scene replacement.
        - After apply_scenario returns requiresUserConfirmation=true, stop. In a later turn, call apply_scenario with
          confirmed=true only when the latest user message explicitly confirms that exact replacement preview.
        - When the user explicitly delegates a multi-step Board change, validated recommendations are inputs to the
          task rather than a mandatory stopping point. Apply the supported candidates with targeted mutation tools,
          then continue with the remaining requested steps and report any part that could not be completed.

        Rule Recommendation Guidelines:
        - Use recommend_rules when the user asks for suggestions or has not supplied enough rule logic. When the user
          supplies a complete rule and asks to save it, validate it and use manage_rule directly.
        - Analyze device capabilities (APIs, variables, modes, states) from authoritative tool results as needed.
        - Only recommend rules using APIs, variables, modes, or states that actually exist in the device templates
        - If the user only asks for suggestions, present them and ask what to apply. If the user explicitly delegates
          completing or modifying the scene, validated recommendations may be applied with targeted mutation tools
          in the same turn; report that newly created items are not formally verified.
        - Explain why each suggestion matches the user's goal and the available device capabilities; do not invent a numeric confidence score

        Destructive Action Guidelines:
        - Device, template, rule, specification, and saved-trace deletion is always a two-turn operation.
        - On the first turn, call the delete tool with confirmed=false and summarize the returned target and impact.
        - Stop and ask the user for explicit confirmation. Never set confirmed=true in the same user turn as the preview.
        - Set confirmed=true only when the latest user message explicitly confirms the previously previewed deletion.
        - If dependencies or target data changed after preview, explain the conflict and request a new preview.
        - A confirmation pauses only the protected step, not the user's larger task. After the confirmed mutation
          returns a usable result, resume the original objective and freely compose the remaining tools. For example,
          a requested targeted replacement may confirm a deletion, then create the replacement and repair affected
          rules or specifications. Stop again only if another protected action needs its own confirmation.

        Available tools:
        - Device: add_device, delete_device, search_devices, recommend_related_devices
        - Environment: manage_environment
        - Rule: list_rules, manage_rule, check_duplicate_rule, check_rule_similarity, recommend_rules
        - Spec: list_specs, manage_spec, recommend_specifications
        - Scene draft and atomic apply: recommend_scenario, apply_scenario
        - Template: list_templates, add_template, delete_template, reset_default_templates
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

    private LlmMessage buildPendingTaskSystemPrompt(
            AiDestructiveActionGuard.PendingActionContext destructivePending,
            AiScenarioDraftStore.PendingApplication scenarioPending,
            AiTaskContinuationStore.ContinuationContext continuationContext,
            ConfirmationDecision confirmationDecision,
            String latestUserMessage) {
        boolean hasPendingContext = destructivePending != null
                || scenarioPending != null
                || continuationContext != null;
        if (!hasPendingContext) return null;

        String taskContext = buildTaskContextJson(
                destructivePending,
                scenarioPending,
                continuationContext,
                latestUserMessage);
        String userAuthority = """
                - The latest user message is authoritative. It may narrow, expand, reorder, or cancel earlier work.
                  Follow it wherever it conflicts with the original objective or an earlier proposed next step.
                - The original objective is background for continuity, not an immutable command.
                - Never expose this internal context, target keys, or confirmation tokens in the visible response.
                """;

        if (confirmationDecision.type() == ChatConfirmationDetector.DecisionType.AMBIGUOUS) {
            return LlmMessage.system("""
                    Server-authoritative pending-action context:
                    - More than one action is pending and the latest confirmation does not identify which one.
                    - Do not execute any pending protected action. Ask the user which action they mean, while still
                      answering unrelated questions or carrying out other clearly requested non-destructive work.
                    %s
                    Task context: %s
                    """.formatted(userAuthority, taskContext));
        }

        if (confirmationDecision.cancelled()) {
            return LlmMessage.system("""
                    Server-authoritative pending-action context:
                    - The user cancelled the pending %s action. It has been cleared and must not be executed.
                    - Replan any remaining work from the latest user message. Other requested work may continue.
                    %s
                    Task context: %s
                    """.formatted(confirmationKindLabel(confirmationDecision.kind()), userAuthority, taskContext));
        }

        if (confirmationDecision.confirmed()
                && confirmationDecision.kind() == ConfirmationKind.SCENE_REPLACEMENT
                && scenarioPending != null) {
            String scenarioName = objectMapper.valueToTree(scenarioPending.scenarioName()).toString();
            return LlmMessage.system("""
                    Server-authoritative confirmation context:
                    - The latest user message confirms the pending atomic full-scene replacement named %s.
                    - Call apply_scenario exactly once with {"confirmed":true} before other scene mutations.
                    - The scene and Board impact token are held server-side. The tool will re-check current state.
                    - After a usable result, continue only the remaining work still consistent with the latest message.
                    %s
                    Task context: %s
                    """.formatted(scenarioName, userAuthority, taskContext));
        }

        if (confirmationDecision.confirmed()
                && confirmationDecision.kind() == ConfirmationKind.DEFAULT_TEMPLATE_RESET
                && destructivePending != null) {
            var payload = objectMapper.createObjectNode();
            payload.put("toolName", destructivePending.toolName());
            payload.put("impactToken", destructivePending.impactToken());
            return LlmMessage.system("""
                    Server-authoritative confirmation context:
                    - The latest user message confirms the exact pending bundled-default-template reset preview.
                    - Call reset_default_templates exactly once with confirmed=true and impactToken copied exactly.
                    - Do not add a target field, request another preview, or call a read tool first. The reset tool
                      will re-check the current catalog and Board impact atomically.
                    - After a usable result, continue only the remaining work still consistent with the latest message.
                    Pending action: %s
                    %s
                    Task context: %s
                    """.formatted(payload, userAuthority, taskContext));
        }

        if (confirmationDecision.confirmed()
                && confirmationDecision.kind() == ConfirmationKind.DESTRUCTIVE
                && destructivePending != null) {
            var payload = objectMapper.createObjectNode();
            payload.put("toolName", destructivePending.toolName());
            payload.put("targetKey", destructivePending.targetKey());
            payload.put("impactToken", destructivePending.impactToken());
            return LlmMessage.system("""
                    Server-authoritative confirmation context:
                    - The latest user message confirms the exact pending destructive preview below.
                    - Call the named tool exactly once with confirmed=true, the tool-specific target field set to
                      targetKey, and impactToken copied exactly. Preserve action=delete when required by its schema.
                    - Do not request another preview or call a read tool first. The mutation tool will re-check drift.
                    - After a usable result, continue only the remaining work still consistent with the latest message.
                    Pending action: %s
                    %s
                    Task context: %s
                    """.formatted(payload, userAuthority, taskContext));
        }

        if (confirmationDecision.confirmed()
                && confirmationDecision.kind() == ConfirmationKind.CHOICE) {
            return LlmMessage.system("""
                    Server-authoritative task-continuation context:
                    - The latest user message accepts or specifies the pending non-destructive choice.
                    - Use the stored pending tool result to interpret that choice, then continue the requested task.
                    - This does not authorize any destructive action; such an action still needs its own live preview.
                    %s
                    Task context: %s
                    """.formatted(userAuthority, taskContext));
        }

        return LlmMessage.system("""
                Server-authoritative pending-action context:
                - A prior preview or proposed choice remains pending, but the latest user message did not authorize it.
                - Do not execute the pending protected action. The user may ask questions, add conditions, change the
                  remaining task, or request other work without losing the preview.
                - Continue other clearly requested read-only or non-destructive work when possible. A new preview may
                  replace the old one, and a later confirmation will still be checked for drift and expiration.
                %s
                Task context: %s
                """.formatted(userAuthority, taskContext));
    }

    private String buildTaskContextJson(
            AiDestructiveActionGuard.PendingActionContext destructivePending,
            AiScenarioDraftStore.PendingApplication scenarioPending,
            AiTaskContinuationStore.ContinuationContext continuationContext,
            String latestUserMessage) {
        ObjectNode context = objectMapper.createObjectNode();
        if (continuationContext != null) {
            context.put("originalObjective", continuationContext.originalObjective());
            var updates = context.putArray("recentUserMessages");
            continuationContext.recentUserMessages().forEach(updates::add);
            if (continuationContext.pendingToolName() != null) {
                context.put("pendingToolName", continuationContext.pendingToolName());
            }
            if (continuationContext.pendingResult() != null) {
                context.put("pendingToolResult", continuationContext.pendingResult());
            }
        }
        context.put("latestUserMessage", latestUserMessage == null ? "" : latestUserMessage);
        if (destructivePending != null) {
            boolean defaultTemplateReset = "reset_default_templates".equals(destructivePending.toolName());
            context.put("pendingKind", defaultTemplateReset ? "defaultTemplateReset" : "destructive");
            context.put("pendingTool", destructivePending.toolName());
            if (!defaultTemplateReset) {
                context.put("pendingTarget", destructivePending.targetKey());
            }
        }
        if (scenarioPending != null) {
            context.put("pendingKind", destructivePending == null ? "sceneReplacement" : "multiple");
            context.put("pendingScenarioName", scenarioPending.scenarioName());
        }
        return context.toString();
    }

    private String confirmationKindLabel(ConfirmationKind kind) {
        if (kind == null) return "actions";
        return switch (kind) {
            case DESTRUCTIVE -> "destructive";
            case DEFAULT_TEMPLATE_RESET -> "default-template reset";
            case SCENE_REPLACEMENT -> "scene-replacement";
            case CHOICE -> "non-destructive choice";
        };
    }

    private void clearCancelledPendingAction(Long userId, String sessionId, ConfirmationKind kind) {
        if (kind == null || kind == ConfirmationKind.DESTRUCTIVE
                || kind == ConfirmationKind.DEFAULT_TEMPLATE_RESET) {
            destructiveActionGuard.clearSession(userId, sessionId);
        }
        if (kind == null || kind == ConfirmationKind.SCENE_REPLACEMENT) {
            scenarioDraftStore.clearPendingApplication(userId, sessionId);
        }
        if (kind == null || kind == ConfirmationKind.CHOICE) {
            taskContinuationStore.clear(userId, sessionId);
        }
    }

    private boolean shouldPreservePendingTask(
            Long userId,
            String sessionId,
            boolean hadProtectedPending,
            AiTaskContinuationStore.ContinuationContext continuationContext,
            ConfirmationDecision confirmationDecision,
            ToolLoopResult loopResult) {
        boolean protectedActionStillPending = destructiveActionGuard.pendingContext(userId, sessionId).isPresent()
                || scenarioDraftStore.pendingApplication(userId, sessionId).isPresent();
        if (protectedActionStillPending) return true;
        if (hadProtectedPending || continuationContext == null
                || continuationContext.pendingToolName() == null
                || confirmationDecision.cancelled()) {
            return false;
        }
        return !(confirmationDecision.confirmed()
                && confirmationDecision.kind() == ConfirmationKind.CHOICE
                && loopResult.successfulToolCalls() > 0);
    }

    private String sanitizePendingResultForContinuation(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) return null;
        try {
            JsonNode parsed = objectMapper.readTree(toolResult);
            removeSensitiveContinuationFields(parsed);
            return parsed.toString();
        } catch (Exception ignored) {
            return toolResult.replaceAll("\\s+", " ").trim();
        }
    }

    private void removeSensitiveContinuationFields(JsonNode node) {
        if (node == null) return;
        if (node instanceof ObjectNode object) {
            object.remove(CONTINUATION_SENSITIVE_FIELDS);
            object.elements().forEachRemaining(this::removeSensitiveContinuationFields);
            return;
        }
        if (node.isArray()) {
            node.elements().forEachRemaining(this::removeSensitiveContinuationFields);
        }
    }

    private LlmMessage buildVisibleReplySystemPrompt(boolean afterToolExecution) {
        String toolContext = afterToolExecution
                ? """
                Tool executions may already be present in the conversation history. Use those tool results
                to summarize what happened and what the user should know next.
                """
                : """
                The planning stage did not execute a tool for this response. Answer as a normal conversational
                assistant, but do not claim to have read current platform data or completed an operation without
                an authoritative tool result. If the request required current data or a platform mutation, say
                that no authoritative result was obtained and ask the user to retry or clarify the request.
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
        - For recommendation results, preserve the distinction between validated, filtered, truncated, and adjusted
          candidates. Match the level of detail to the user's request; do not force raw counters into a concise answer.
          Explain material filtering or adjustment reasons, never invent reasons for uninspected truncated candidates,
          and never describe a kept candidate as applied unless a later mutation result proves it.
        - A recommend_scenario result is an unverified full-replacement draft. State that the user can ask the
          assistant to apply it; apply_scenario will first show a separate impact preview, then atomically replace
          devices, the shared environment pool, rules, and specifications after explicit confirmation.
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
        - Never expose impactToken, confirmationToken, domainImpactToken, or other opaque authorization values, even when they appear in a tool result.
        - formulaPreview is descriptive preview text. Only checkedExpression is the expression actually sent to the model checker for that run.
        - For casual non-IoT questions, answer directly.
        - Explain verification, simulation, rules, and specifications in user-friendly language.

        %s
        """.formatted(toolContext);

        return LlmMessage.system(systemPromptContent);
    }

    private List<LlmMessage> withVisibleReplyPrompt(List<LlmMessage> messages, ToolLoopResult loopResult) {
        List<LlmMessage> finalMessages = new ArrayList<>();
        finalMessages.add(buildVisibleReplySystemPrompt(loopResult.hadToolCalls()));
        if (loopResult.stoppedForNoProgress()) {
            finalMessages.add(LlmMessage.system("Further tool calls were stopped only because consecutive rounds "
                    + "repeated the exact same calls and results. Summarize completed, failed, and unfinished work "
                    + "accurately. Do not claim that the full request completed."));
        } else if (loopResult.reachedEmergencyLimit()) {
            finalMessages.add(LlmMessage.system("The emergency runaway guard stopped further tool calls. Summarize "
                    + "completed, failed, and unfinished work accurately. Do not claim that the full request completed."));
        }
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
        return executeToolLoop(
                userId, sessionId, messages, tools, commandSet, emitter, isDisconnect, false);
    }

    private ToolLoopResult executeToolLoop(Long userId,
                                           String sessionId,
                                           List<LlmMessage> messages,
                                           List<LlmToolSpec> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter,
                                           AtomicBoolean isDisconnect,
                                           boolean preferChinese) {
        return executeToolLoop(
                userId, sessionId, messages, tools, commandSet, emitter, isDisconnect,
                preferChinese, null);
    }

    private ToolLoopResult executeToolLoop(Long userId,
                                           String sessionId,
                                           List<LlmMessage> messages,
                                           List<LlmToolSpec> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter,
                                           AtomicBoolean isDisconnect,
                                           boolean preferChinese,
                                           List<StreamResponseDto.ProgressDto> executionTrace) {
        boolean hadToolCalls = false;
        int successfulToolCalls = 0;
        int failedToolCalls = 0;
        int resultUnavailableToolCalls = 0;
        int uncertainMutationCalls = 0;
        boolean confirmationPending = false;
        String previousRoundFingerprint = null;
        int stagnantRoundCount = 0;

        for (int round = 0; round < chatExecutionConfig.getMaxToolRounds(); round++) {
            if (isDisconnect.get()) {
                log.info("Client disconnected, stopping tool loop");
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            ToolLoopResult currentResult = new ToolLoopResult(hadToolCalls, ToolLoopStopReason.COMPLETED,
                    successfulToolCalls, failedToolCalls, resultUnavailableToolCalls,
                    uncertainMutationCalls, confirmationPending);
            if (!sendSseProgress(emitter, "PLANNING", null, round + 1,
                    null, currentResult, null, executionTrace)) {
                isDisconnect.set(true);
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            LlmChatResponse response = llmChatService.chatWithTools(messages, tools);
            if (isDisconnect.get()) {
                log.info("Chat execution stopped after tool planning for session {}", sessionId);
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            if (response == null) {
                log.warn("LLM provider returned null tool-planning response");
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.PROVIDER_UNAVAILABLE, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            List<LlmToolCall> toolCalls = normalizeToolCallIds(response.toolCalls(), messages);
            if (toolCalls.isEmpty()) {
                String aiText = response.text();
                if (!aiText.isBlank()) {
                    log.debug("Tool planning completed with final text; regenerating visible answer through streaming.");
                }
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.COMPLETED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            String reasoningSummary = compactReasoningProgressDetail(response.text());
            if (reasoningSummary != null && !reasoningSummary.isBlank()
                    && !sendSseProgress(emitter, "REASONING", null, round + 1,
                    null, currentResult, reasoningSummary, executionTrace)) {
                isDisconnect.set(true);
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            hadToolCalls = true;
            executeOwnedSessionWrite(userId, sessionId, () ->
                    saveAiToolCallRequest(sessionId, toolCalls));
            messages.add(LlmMessage.assistantToolCalls(toolCalls));
            StringBuilder roundFingerprint = new StringBuilder();

            for (int toolCallIndex = 0; toolCallIndex < toolCalls.size(); toolCallIndex++) {
                LlmToolCall toolCall = toolCalls.get(toolCallIndex);
                if (isDisconnect.get()) {
                    log.info("Client disconnected, stopping remaining tool calls");
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
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
                    currentResult = new ToolLoopResult(hadToolCalls, ToolLoopStopReason.COMPLETED,
                            successfulToolCalls, failedToolCalls, resultUnavailableToolCalls,
                            uncertainMutationCalls, confirmationPending);
                    if (!sendSseProgress(emitter, "TOOL_EXECUTION", functionName, round + 1,
                            null, currentResult, null, executionTrace)) {
                        isDisconnect.set(true);
                        return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                                failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                                confirmationPending);
                    }
                    toolResult = aiToolManager.execute(functionName, argsJson);
                    if (isDisconnect.get()) {
                        log.info("Chat execution stopped after tool execution for session {}", sessionId);
                        return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
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
                roundFingerprint.append(functionName).append('\u001f')
                        .append(argsJson).append('\u001f')
                        .append(executionOutcome.name()).append('\u001f')
                        .append(toolResult).append('\u001e');

                currentResult = new ToolLoopResult(hadToolCalls, ToolLoopStopReason.COMPLETED,
                        successfulToolCalls, failedToolCalls, resultUnavailableToolCalls,
                        uncertainMutationCalls, confirmationPending);
                String progressOutcome = requiresConfirmation
                        ? "CONFIRMATION_REQUIRED" : executionOutcome.name();
                if (!sendSseProgress(emitter, "TOOL_RESULT", functionName, round + 1,
                        progressOutcome, currentResult,
                        toolProgressDetail(functionName, toolResult, preferChinese), executionTrace)) {
                    isDisconnect.set(true);
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                            confirmationPending);
                }
                if (requiresConfirmation) {
                    appendSkippedToolResults(userId, sessionId, messages, toolCalls, toolCallIndex + 1,
                            "PRIOR_CONFIRMATION_REQUIRED",
                            "Tool call was not executed because an earlier call in the same planning response "
                                    + "requires user confirmation.");
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.CONFIRMATION_REQUIRED,
                            successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls, true,
                            functionName, toolResult);
                }
                if (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE) {
                    appendSkippedToolResults(userId, sessionId, messages, toolCalls, toolCallIndex + 1,
                            "PRIOR_RESULT_UNAVAILABLE",
                            "Tool call was not executed because an earlier result in the same planning response "
                                    + "was unavailable and may require state reconciliation.");
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.RESULT_UNAVAILABLE,
                            successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls, false);
                }
            }

            String fingerprint = roundFingerprint.toString();
            if (fingerprint.equals(previousRoundFingerprint)) {
                stagnantRoundCount++;
            } else {
                previousRoundFingerprint = fingerprint;
                stagnantRoundCount = 0;
            }
            if (stagnantRoundCount >= chatExecutionConfig.getMaxStagnantRounds()) {
                log.warn("Tool call loop stopped after {} repeated no-progress round(s)", stagnantRoundCount);
                ToolLoopResult guardResult = new ToolLoopResult(hadToolCalls, ToolLoopStopReason.NO_PROGRESS,
                        successfulToolCalls, failedToolCalls, resultUnavailableToolCalls,
                        uncertainMutationCalls, confirmationPending);
                if (!sendSseProgress(emitter, "EXECUTION_GUARD", null, round + 1,
                        "NO_PROGRESS", guardResult, null, executionTrace)) {
                    isDisconnect.set(true);
                }
                return guardResult;
            }
        }

        log.warn("Tool call loop reached emergency max rounds: {}", chatExecutionConfig.getMaxToolRounds());
        ToolLoopResult guardResult = new ToolLoopResult(hadToolCalls, ToolLoopStopReason.EMERGENCY_LIMIT,
                successfulToolCalls,
                failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                confirmationPending);
        if (!sendSseProgress(emitter, "EXECUTION_GUARD", null, chatExecutionConfig.getMaxToolRounds(),
                "EMERGENCY_LIMIT", guardResult, null, executionTrace)) {
            isDisconnect.set(true);
        }
        return guardResult;
    }

    private List<LlmToolCall> normalizeToolCallIds(List<LlmToolCall> toolCalls,
                                                    List<LlmMessage> messages) {
        Set<String> usedIds = new LinkedHashSet<>();
        if (messages != null) {
            for (LlmMessage message : messages) {
                if (message == null || !message.hasToolCalls()) {
                    continue;
                }
                for (LlmToolCall existingCall : message.toolCalls()) {
                    if (existingCall != null && existingCall.id() != null && !existingCall.id().isBlank()) {
                        usedIds.add(existingCall.id().trim());
                    }
                }
            }
        }

        List<LlmToolCall> normalized = new ArrayList<>(toolCalls.size());
        for (LlmToolCall toolCall : toolCalls) {
            String id = safeString(toolCall.id()).trim();
            if (id.isBlank() || !usedIds.add(id)) {
                String reason = id.isBlank() ? "blank" : "duplicate";
                do {
                    id = "call_" + UUID.randomUUID().toString().replace("-", "");
                } while (!usedIds.add(id));
                log.warn("Replaced {} provider tool-call id with a unique internal correlation id", reason);
            }
            normalized.add(new LlmToolCall(id, toolCall.name(), toolCall.argumentsJson()));
        }
        return List.copyOf(normalized);
    }

    private void appendSkippedToolResults(Long userId,
                                          String sessionId,
                                          List<LlmMessage> messages,
                                          List<LlmToolCall> toolCalls,
                                          int startIndex,
                                          String reasonCode,
                                          String message) {
        if (toolCalls == null || startIndex >= toolCalls.size()) {
            return;
        }
        String skippedResult = objectMapper.createObjectNode()
                .put("executed", false)
                .put("skipped", true)
                .put("reasonCode", reasonCode)
                .put("message", message)
                .toString();
        for (int index = startIndex; index < toolCalls.size(); index++) {
            LlmToolCall skippedCall = toolCalls.get(index);
            if (skippedCall == null) {
                continue;
            }
            String toolCallId = safeString(skippedCall.id());
            executeOwnedSessionWrite(userId, sessionId, () ->
                    saveToolExecutionResult(sessionId, toolCallId, skippedResult));
            messages.add(LlmMessage.tool(toolCallId, skippedResult));
        }
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
        return sendSseProgress(emitter, stage, toolName, round, null, null);
    }

    private boolean sendSseProgress(SseEmitter emitter,
                                    String stage,
                                    String toolName,
                                    Integer round,
                                    String outcome,
                                    ToolLoopResult result) {
        return sendSseProgress(emitter, stage, toolName, round, outcome, result, null);
    }

    private boolean sendSseProgress(SseEmitter emitter,
                                    String stage,
                                    String toolName,
                                    Integer round,
                                    String outcome,
                                    ToolLoopResult result,
                                    String detail) {
        return sendSseProgress(emitter, stage, toolName, round, outcome, result, detail, null);
    }

    private boolean sendSseProgress(SseEmitter emitter,
                                    String stage,
                                    String toolName,
                                    Integer round,
                                    String outcome,
                                    ToolLoopResult result,
                                    String detail,
                                    List<StreamResponseDto.ProgressDto> executionTrace) {
        try {
            StreamResponseDto packet = StreamResponseDto.progress(
                    stage,
                    toolName,
                    round,
                    outcome,
                    result == null ? null : result.successfulToolCalls(),
                    result == null ? null : result.failedToolCalls(),
                    result == null ? null : result.resultUnavailableToolCalls()
                            + (result.confirmationPending() ? 1 : 0),
                    detail
            );
            emitter.send(SseEmitter.event()
                    .data(packet, MediaType.APPLICATION_JSON));
            if (executionTrace != null && packet.getProgress() != null) {
                executionTrace.add(packet.getProgress());
            }
            return true;
        } catch (IOException | IllegalStateException e) {
            log.debug("Failed to send chat progress stage {}: {}", stage, e.toString());
            return false;
        }
    }

    private String compactProgressDetail(String value) {
        return compactProgressDetail(value, 240);
    }

    private String compactProgressDetail(String value, int maxChars) {
        if (value == null) return null;
        String compact = value.replaceAll("\\s+", " ").trim();
        if (compact.length() <= maxChars) return compact;
        return compact.substring(0, Math.max(0, maxChars - 3)) + "...";
    }

    private String toolProgressDetail(String functionName, String toolResult, boolean preferChinese) {
        if (toolResult == null || toolResult.isBlank()) {
            return preferChinese ? "工具没有返回可用结果。" : "The tool returned no usable result.";
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            if (!root.isObject() || root.path("skipped").asBoolean(false)) {
                return null;
            }
            if (!root.path("error").asText("").isBlank()) {
                String errorCode = root.path("errorCode").asText("").trim();
                String code = errorCode.matches("[A-Z0-9_-]{1,64}") ? " (" + errorCode + ")" : "";
                return preferChinese
                        ? "工具未能完成该操作" + code + "，具体原因见助手回复。"
                        : "The tool could not complete the operation" + code
                        + "; see the assistant response for the specific reason.";
            }

            if ("board_overview".equals(functionName)) {
                return preferChinese
                        ? String.format("已读取画布：%d 个设备、%d 条规则、%d 条规约、%d 个共享环境变量。",
                        arraySize(root, "devices"), arraySize(root, "rules"),
                        arraySize(root, "specs"), arraySize(root, "environmentVariables"))
                        : String.format("Read the board: %d devices, %d rules, %d specifications, and %d shared environment variables.",
                        arraySize(root, "devices"), arraySize(root, "rules"),
                        arraySize(root, "specs"), arraySize(root, "environmentVariables"));
            }
            if ("add_device".equals(functionName) && "created".equals(root.path("operation").asText())) {
                JsonNode device = root.path("device");
                String label = device.path("label").asText("").trim();
                String state = device.path("state").asText("").trim();
                int environmentChanges = arraySize(root, "environmentChanges");
                return compactToolProgressDetail(preferChinese
                        ? String.format("已创建设备%s%s；环境池变化 %d 项。",
                        quotedName(label), state.isBlank() ? "" : "，初始状态为 " + state,
                        environmentChanges)
                        : String.format("Created device%s%s with %d Environment Pool change(s).",
                        quotedName(label), state.isBlank() ? "" : " in initial state " + state,
                        environmentChanges));
            }
            if ("delete_device".equals(functionName)) {
                boolean preview = "preview".equals(root.path("operation").asText());
                JsonNode device = preview ? root.path("device") : root.path("deletedDevice");
                String label = device.path("label").asText("").trim();
                if (preview) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已预览删除设备%s：将移除 %d 条规则、%d 条规约并改变 %d 个环境变量；尚未写入。",
                            quotedName(label), root.path("wouldRemoveRuleCount").asInt(0),
                            root.path("wouldRemoveSpecificationCount").asInt(0),
                            root.path("wouldChangeEnvironmentVariableCount").asInt(0))
                            : String.format("Previewed deletion of device%s: %d rule(s), %d specification(s), and %d environment variable(s) would be affected; nothing was written.",
                            quotedName(label), root.path("wouldRemoveRuleCount").asInt(0),
                            root.path("wouldRemoveSpecificationCount").asInt(0),
                            root.path("wouldChangeEnvironmentVariableCount").asInt(0)));
                }
                if ("deleted".equals(root.path("operation").asText())) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已删除设备%s，并移除 %d 条规则和 %d 条规约。",
                            quotedName(label), root.path("removedRuleCount").asInt(0),
                            root.path("removedSpecificationCount").asInt(0))
                            : String.format("Deleted device%s and removed %d rule(s) and %d specification(s).",
                            quotedName(label), root.path("removedRuleCount").asInt(0),
                            root.path("removedSpecificationCount").asInt(0)));
                }
            }
            if ("manage_rule".equals(functionName)) {
                String operation = root.path("operation").asText("").trim();
                JsonNode rule = "deleted".equals(operation) ? root.path("deletedRule") : root.path("rule");
                String description = rule.path("description").asText("").trim();
                if (!operation.isBlank()) {
                    String action = "created".equals(operation)
                            ? (preferChinese ? "已创建规则" : "Created rule")
                            : (preferChinese ? "已删除规则" : "Deleted rule");
                    return compactToolProgressDetail(description.isBlank()
                            ? action + (preferChinese ? "。" : ".")
                            : action + (preferChinese ? "：" : ": ") + description);
                }
            }
            if ("manage_spec".equals(functionName)) {
                String operation = root.path("operation").asText("").trim();
                JsonNode spec = "deleted".equals(operation)
                        ? root.path("deletedSpecification") : root.path("specification");
                String formula = spec.path("formulaPreview").asText("").trim();
                if (!operation.isBlank()) {
                    String action = "created".equals(operation)
                            ? (preferChinese ? "已创建规约" : "Created specification")
                            : (preferChinese ? "已删除规约" : "Deleted specification");
                    return compactToolProgressDetail(formula.isBlank()
                            ? action + (preferChinese ? "。" : ".")
                            : action + (preferChinese ? "：" : ": ") + formula);
                }
            }
            if ("add_template".equals(functionName) && "created".equals(root.path("operation").asText())) {
                String name = root.path("template").path("name").asText("").trim();
                return compactToolProgressDetail(preferChinese
                        ? "已创建设备模板" + quotedName(name) + "。"
                        : "Created device template" + quotedName(name) + ".");
            }
            if (Set.of("recommend_rules", "recommend_specifications", "recommend_related_devices")
                    .contains(functionName)) {
                int kept = root.path("validatedCount").asInt(root.path("count").asInt(0));
                int filtered = root.path("filteredCount").asInt(0);
                String firstReason = root.path("filteredItems").path(0).path("reason").asText("").trim();
                String summary = preferChinese
                        ? "AI 候选经后端校验后保留 " + kept + " 项，过滤 " + filtered + " 项。"
                        : "Backend validation kept " + kept + " AI candidate(s) and filtered " + filtered + ".";
                if (!firstReason.isBlank()) {
                    summary += (preferChinese ? " 首个过滤原因：" : " First filter reason: ") + firstReason;
                }
                return compactToolProgressDetail(summary);
            }
            if ("recommend_scenario".equals(functionName)) {
                JsonNode scene = root.path("scene");
                String name = root.path("scenarioName").asText("").trim();
                String summary = preferChinese
                        ? String.format("已生成场景%s：%d 个设备、%d 条规则、%d 条规约；过滤 %d 个无效候选。",
                        quotedName(name), arraySize(scene, "devices"), arraySize(scene, "rules"),
                        arraySize(scene, "specs"), root.path("filteredCount").asInt(0))
                        : String.format("Generated scenario%s with %d devices, %d rules, and %d specifications; filtered %d invalid candidate(s).",
                        quotedName(name), arraySize(scene, "devices"), arraySize(scene, "rules"),
                        arraySize(scene, "specs"), root.path("filteredCount").asInt(0));
                if (!root.path("verificationReady").asBoolean(false)) {
                    summary += preferChinese ? " 该草案目前尚不能启动验证。" : " The draft is not verification-ready yet.";
                }
                return compactToolProgressDetail(summary);
            }
            if ("apply_scenario".equals(functionName)) {
                String name = root.path("scenarioName").asText("").trim();
                boolean preview = "preview".equals(root.path("operation").asText());
                if (preview) {
                    return compactToolProgressDetail(preferChinese
                            ? String.format("已生成场景%s的全量替换预览，尚未写入，正在等待确认。", quotedName(name))
                            : String.format("Prepared a full-board replacement preview for scenario%s; nothing was written and confirmation is required.", quotedName(name)));
                }
                return compactToolProgressDetail(preferChinese
                        ? String.format("已应用场景%s：%d 个设备、%d 条规则、%d 条规约。",
                        quotedName(name), root.path("deviceCount").asInt(0),
                        root.path("ruleCount").asInt(0), root.path("specificationCount").asInt(0))
                        : String.format("Applied scenario%s with %d devices, %d rules, and %d specifications.",
                        quotedName(name), root.path("deviceCount").asInt(0),
                        root.path("ruleCount").asInt(0), root.path("specificationCount").asInt(0)));
            }
            if ("reset_default_templates".equals(functionName)) {
                if (root.path("requiresUserConfirmation").asBoolean(false)) {
                    JsonNode preview = root.path("preview");
                    return preferChinese
                            ? String.format("已预览默认模板刷新：%d 个模板变化、%d 个受影响设备，尚未写入，正在等待确认。",
                            arraySize(preview, "templateChanges"), arraySize(preview, "affectedDevices"))
                            : String.format("Previewed the default-template refresh: %d template change(s) and %d affected device(s); nothing was written and confirmation is required.",
                            arraySize(preview, "templateChanges"), arraySize(preview, "affectedDevices"));
                }
                if ("reset".equals(root.path("operation").asText())) {
                    return preferChinese
                            ? String.format("已刷新默认模板：%d 个模板变化、%d 个受影响设备、%d 个环境变量变化。",
                            root.path("templateChangeCount").asInt(0),
                            root.path("affectedDeviceCount").asInt(0),
                            root.path("environmentChangeCount").asInt(0))
                            : String.format("Refreshed default templates: %d template change(s), %d affected device(s), and %d environment-variable change(s).",
                            root.path("templateChangeCount").asInt(0),
                            root.path("affectedDeviceCount").asInt(0),
                            root.path("environmentChangeCount").asInt(0));
                }
            }
            if ("manage_environment".equals(functionName)) {
                JsonNode variable = root.path("currentVariable");
                String name = variable.path("name").asText("").trim();
                if (!name.isBlank()) {
                    return compactToolProgressDetail(preferChinese
                            ? "环境变量“" + name + "”当前值为 " + variable.path("value").asText("")
                            + "，trust=" + variable.path("trust").asText("")
                            + "，privacy=" + variable.path("privacy").asText("") + "。"
                            : "Environment variable '" + name + "' is now " + variable.path("value").asText("")
                            + " with trust=" + variable.path("trust").asText("")
                            + " and privacy=" + variable.path("privacy").asText("") + ".");
                }
            }

            String operation = root.path("operation").asText("").trim();
            if (!operation.isBlank()) {
                return compactToolProgressDetail(preferChinese
                        ? "工具操作结果：" + operation + "。"
                        : "Tool operation result: " + operation + ".");
            }
            return preferChinese ? "工具已返回结构化结果。" : "The tool returned a structured result.";
        } catch (Exception e) {
            return preferChinese ? "工具结果无法生成摘要。" : "The tool result could not be summarized.";
        }
    }

    private int arraySize(JsonNode root, String field) {
        JsonNode value = root == null ? null : root.path(field);
        return value != null && value.isArray() ? value.size() : 0;
    }

    private String quotedName(String name) {
        return name == null || name.isBlank() ? "" : " '" + name + "'";
    }

    private String compactToolProgressDetail(String value) {
        return sanitizeProgressDetail(value, 240);
    }

    private String compactReasoningProgressDetail(String value) {
        return sanitizeProgressDetail(value, 800);
    }

    private String sanitizeProgressDetail(String value, int maxChars) {
        if (value == null) return null;
        String sanitized = value
                .replaceAll("(?i)(impactToken|confirmationToken|domainImpactToken)\\s*[:=]\\s*[^,;\\s]+", "$1=[hidden]")
                .replaceAll("(?i)\\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\\b", "[internal reference]")
                .replaceAll("(?i)\\b(?:device|node|rule|spec|task|trace|simulation)[_-][a-z0-9_-]+\\b", "[internal reference]")
                .replaceAll("(?i)\\b(?:device|node|rule|spec(?:ification)?|task|trace|simulation|session|user)\\s+id\\s*[:=#]?\\s*[a-z0-9_-]+", "[internal reference]");
        return compactProgressDetail(sanitized, maxChars);
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
            case "apply_scenario" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "board_state")));
            case "reset_default_templates" ->
                    commandSet.add(new StreamResponseDto.CommandDto(
                            "REFRESH_DATA", Map.of("target", "board_state")));
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

    private String executionGuardNotice(ToolLoopResult result, boolean preferChinese) {
        if (result == null || (!result.stoppedForNoProgress() && !result.reachedEmergencyLimit())) {
            return "";
        }
        if (result.stoppedForNoProgress()) {
            return preferChinese
                    ? "检测到连续多轮完全相同的工具调用和结果，已停止重复执行；正在整理已完成、失败和未完成的步骤。\n\n"
                    : "Consecutive rounds repeated the exact same tool calls and results, so duplicate execution stopped. "
                        + "The assistant is now summarizing completed, failed, and unfinished steps.\n\n";
        }
        return preferChinese
                ? "任务触发了异常循环安全保护；此前步骤不会回滚，助手正在整理已完成、失败和未完成的内容。\n\n"
                : "The task reached the emergency runaway guard. Earlier steps were not rolled back; the assistant "
                    + "is now summarizing completed, failed, and unfinished work.\n\n";
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

    private void saveAssistantMsg(String sid,
                                  String content,
                                  List<StreamResponseDto.ProgressDto> executionTrace,
                                  Integer elapsedSeconds) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("assistant");
        po.setContent(content);
        po.setExecutionElapsedSeconds(elapsedSeconds);
        if (executionTrace != null && !executionTrace.isEmpty()) {
            try {
                po.setExecutionTraceJson(objectMapper.writeValueAsString(executionTrace));
            } catch (Exception e) {
                log.warn("Could not serialize execution trace for chat session {}: {}", sid, e.toString());
            }
        }
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
                    if (!isCompleteToolCallBlock(allMessages, assistantIndex, i)) {
                        log.warn("Dropping incomplete persisted tool-call block from chat history: "
                                + "sessionId={}, assistantMessageId={}",
                                sessionId, allMessages.get(assistantIndex).getId());
                        i = assistantIndex;
                        continue;
                    }
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

            if (isAssistantToolCallMessage(current)) {
                log.warn("Dropping persisted assistant tool-call message without adjacent results: "
                        + "sessionId={}, assistantMessageId={}", sessionId, current.getId());
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

    private boolean isCompleteToolCallBlock(List<ChatMessagePo> messages,
                                            int assistantIndex,
                                            int lastToolIndex) {
        try {
            LlmMessage assistant = messageCodec.toMessage(messages.get(assistantIndex));
            List<LlmToolCall> calls = assistant.toolCalls();
            Set<String> expectedIds = calls.stream()
                    .map(LlmToolCall::id)
                    .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
            if (expectedIds.size() != calls.size()) {
                return false;
            }

            Set<String> actualIds = new LinkedHashSet<>();
            for (int index = assistantIndex + 1; index <= lastToolIndex; index++) {
                LlmMessage toolMessage = messageCodec.toMessage(messages.get(index));
                if (toolMessage.toolCallId() == null || !actualIds.add(toolMessage.toolCallId())) {
                    return false;
                }
            }
            return actualIds.equals(expectedIds);
        } catch (Exception e) {
            log.warn("Ignoring malformed persisted tool-call block: {}", e.toString());
            return false;
        }
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

    private void attachPersistedExecutionTraces(List<ChatMessagePo> allMessages,
                                                List<ChatMessagePo> visibleMessages,
                                                List<ChatMessageResponseDto> response) {
        if (allMessages == null || visibleMessages == null || response == null
                || visibleMessages.size() != response.size()) {
            return;
        }

        List<StreamResponseDto.ProgressDto> trace = new ArrayList<>();
        Map<String, PersistedTraceCall> callsById = new LinkedHashMap<>();
        int visibleIndex = 0;
        int round = 0;
        int successful = 0;
        int failed = 0;
        int unconfirmed = 0;
        boolean hadTools = false;
        boolean preferChinese = false;
        LocalDateTime requestStartedAt = null;

        for (ChatMessagePo message : allMessages) {
            if (message == null) continue;
            boolean visible = visibleIndex < visibleMessages.size()
                    && message == visibleMessages.get(visibleIndex);

            if (visible && "user".equalsIgnoreCase(message.getRole())) {
                trace.clear();
                callsById.clear();
                round = 0;
                successful = 0;
                failed = 0;
                unconfirmed = 0;
                hadTools = false;
                preferChinese = prefersChinese(message.getContent());
                requestStartedAt = message.getCreatedAt();
                visibleIndex++;
                continue;
            }

            if (isAssistantToolCallMessage(message)) {
                try {
                    LlmMessage toolCallMessage = messageCodec.toMessage(message);
                    if (!hadTools) {
                        trace.add(progress("CONTEXT_READY", null, null, null,
                                null, null, null, null));
                    }
                    hadTools = true;
                    round++;
                    trace.add(progress("PLANNING", null, round, null,
                            successful, failed, unconfirmed, null));
                    for (LlmToolCall call : toolCallMessage.toolCalls()) {
                        callsById.put(call.id(), new PersistedTraceCall(call.name(), round));
                    }
                } catch (Exception e) {
                    log.warn("Could not reconstruct persisted tool calls for execution trace: {}", e.toString());
                }
                continue;
            }

            if (isToolMessage(message)) {
                try {
                    LlmMessage toolMessage = messageCodec.toMessage(message);
                    JsonNode root = objectMapper.readTree(toolMessage.content());
                    if (root.isObject() && root.path("skipped").asBoolean(false)) {
                        continue;
                    }
                    PersistedTraceCall call = callsById.remove(toolMessage.toolCallId());
                    if (call == null) continue;
                    trace.add(progress("TOOL_EXECUTION", call.toolName(), call.round(), null,
                            successful, failed, unconfirmed, null));

                    boolean confirmationRequired = requiresUserConfirmation(toolMessage.content());
                    ToolExecutionOutcome executionOutcome = classifyToolExecution(toolMessage.content());
                    String outcome;
                    if (confirmationRequired) {
                        unconfirmed++;
                        outcome = "CONFIRMATION_REQUIRED";
                    } else if (executionOutcome == ToolExecutionOutcome.USABLE) {
                        successful++;
                        outcome = "USABLE";
                    } else if (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE) {
                        unconfirmed++;
                        outcome = "RESULT_UNAVAILABLE";
                    } else {
                        failed++;
                        outcome = "FAILED";
                    }
                    trace.add(progress("TOOL_RESULT", call.toolName(), call.round(), outcome,
                            successful, failed, unconfirmed,
                            toolProgressDetail(call.toolName(), toolMessage.content(), preferChinese)));
                } catch (Exception e) {
                    log.warn("Could not reconstruct persisted tool result for execution trace: {}", e.toString());
                }
                continue;
            }

            if (!visible) {
                continue;
            }

            ChatMessageResponseDto dto = response.get(visibleIndex);
            if ("assistant".equalsIgnoreCase(message.getRole()) && dto != null) {
                boolean restoredPersistedTrace = false;
                if (message.getExecutionTraceJson() != null && !message.getExecutionTraceJson().isBlank()) {
                    try {
                        List<StreamResponseDto.ProgressDto> persistedTrace = objectMapper.readValue(
                                message.getExecutionTraceJson(),
                                new TypeReference<List<StreamResponseDto.ProgressDto>>() { });
                        dto.setExecutionTrace(List.copyOf(persistedTrace));
                        dto.setExecutionElapsedSeconds(message.getExecutionElapsedSeconds());
                        restoredPersistedTrace = true;
                    } catch (Exception e) {
                        log.warn("Could not read persisted execution trace for message {}: {}",
                                message.getId(), e.toString());
                    }
                }
                if (!restoredPersistedTrace && hadTools) {
                    trace.add(progress("WRITING_RESPONSE", null, null, null,
                            successful, failed, unconfirmed, null));
                    dto.setExecutionTrace(List.copyOf(trace));
                    if (requestStartedAt != null && message.getCreatedAt() != null) {
                        long elapsed = Math.max(0L, ChronoUnit.SECONDS.between(requestStartedAt, message.getCreatedAt()));
                        dto.setExecutionElapsedSeconds((int) Math.min(Integer.MAX_VALUE, elapsed));
                    }
                }
                if (restoredPersistedTrace || hadTools) {
                    trace.clear();
                    callsById.clear();
                    hadTools = false;
                }
            }
            visibleIndex++;
        }
    }

    private StreamResponseDto.ProgressDto progress(String stage,
                                                   String toolName,
                                                   Integer round,
                                                   String outcome,
                                                   Integer successful,
                                                   Integer failed,
                                                   Integer unconfirmed,
                                                   String detail) {
        return new StreamResponseDto.ProgressDto(
                stage, toolName, round, outcome, successful, failed, unconfirmed, detail);
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

    private record PersistedTraceCall(String toolName, int round) {
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

    private enum ToolLoopStopReason {
        COMPLETED,
        DISCONNECTED,
        PROVIDER_UNAVAILABLE,
        CONFIRMATION_REQUIRED,
        RESULT_UNAVAILABLE,
        NO_PROGRESS,
        EMERGENCY_LIMIT
    }

    private record ToolLoopResult(boolean hadToolCalls,
                                  ToolLoopStopReason stopReason,
                                  int successfulToolCalls,
                                  int failedToolCalls,
                                  int resultUnavailableToolCalls,
                                  int uncertainMutationCalls,
                                  boolean confirmationPending,
                                  String pendingToolName,
                                  String pendingToolResult) {
        private ToolLoopResult(boolean hadToolCalls,
                               ToolLoopStopReason stopReason,
                               int successfulToolCalls,
                               int failedToolCalls,
                               int resultUnavailableToolCalls,
                               int uncertainMutationCalls,
                               boolean confirmationPending) {
            this(hadToolCalls, stopReason, successfulToolCalls, failedToolCalls,
                    resultUnavailableToolCalls, uncertainMutationCalls, confirmationPending, null, null);
        }

        private boolean stoppedForNoProgress() {
            return stopReason == ToolLoopStopReason.NO_PROGRESS;
        }

        private boolean reachedEmergencyLimit() {
            return stopReason == ToolLoopStopReason.EMERGENCY_LIMIT;
        }

        private static ToolLoopResult empty() {
            return new ToolLoopResult(false, ToolLoopStopReason.COMPLETED, 0, 0, 0, 0, false);
        }
    }
}
