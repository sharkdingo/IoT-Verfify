package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.AiTaskContinuationStore;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationDecision;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector.ConfirmationKind;
import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmRequestControl;
import cn.edu.nju.Iot_Verify.component.ai.LlmRequestControlHolder;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.ChatExecutionStatus;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.AiScenarioDraftStore;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatHistoryPageDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatConfirmationCommandDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatPendingConfirmationDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ChatSessionBusyException;
import cn.edu.nju.Iot_Verify.exception.ChatHistoryQuotaExceededException;
import cn.edu.nju.Iot_Verify.exception.ChatAdmissionOutcomeUnknownException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
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
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Service;
import org.springframework.data.domain.PageRequest;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.io.IOException;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.function.BooleanSupplier;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@Slf4j
@Service
@RequiredArgsConstructor
public class ChatServiceImpl implements ChatService, ChatExecutionControl {
    private static final int MAX_PRE_ADMISSION_STOP_TURNS = 64;

    private static final int HISTORY_CHAR_LIMIT = 4000;
    private static final int SESSION_LOCK_STRIPES = 256;
    private static final long EXECUTION_CONTROL_POLL_NANOS = Duration.ofMillis(250).toNanos();
    private static final Object[] SESSION_LOCKS = createSessionLocks();
    private static final Set<String> CONTINUATION_SENSITIVE_FIELDS = Set.of(
            "impactToken", "confirmationToken", "domainImpactToken");
    private static final Set<String> TOOL_RESULT_CONTROL_FIELDS = Set.of(
            "error", "errorCode", "status", "requiresUserConfirmation",
            "resultAvailable", "resultStatus", "mutationMayHaveCommitted", "objectiveStatus");
    private static final Set<String> PERSISTED_PROGRESS_FIELDS = Set.of(
            "stage", "toolName", "round", "outcome", "successfulSteps",
            "failedSteps", "unconfirmedSteps", "detail");
    private static final Set<String> PERSISTED_PROGRESS_STAGES = Set.of(
            "CONTEXT_READY", "TASK_RESUMED", "PLANNING", "REASONING",
            "TOOL_EXECUTION", "TOOL_RESULT", "EXECUTION_GUARD", "WRITING_RESPONSE");
    private static final Pattern UNSUPPORTED_TOOL_EVIDENCE_CLAIM = Pattern.compile(
            "(?is)(?:\\b(?:the\\s+)?(?:tool|function|api)(?:\\s+(?:call|execution))?\\s+"
                    + "(?:result|response|output)\\s+"
                    + "(?:shows|indicates|confirms|returned|reports|succeeded|completed)\\b"
                    + "|\\baccording\\s+to\\s+(?:the\\s+)?(?:tool|function|api)"
                    + "(?:\\s+(?:call|execution))?\\s+(?:result|response|output)\\b"
                    + "|\\b(?:the\\s+)?(?:tool|function|api)(?:\\s+(?:call|execution))?\\s+"
                    + "(?:returned|reported)\\b"
                    + "|(?:工具|函数|接口)(?:调用|执行)?(?:结果|响应|输出)"
                    + "(?:显示|表明|证明|返回|确认|成功|完成)"
                    + "|(?:工具|函数|接口)(?:调用|执行)?(?:已返回|返回了|已报告))");
    private static final Pattern UNSUPPORTED_PLATFORM_MUTATION_CLAIM = Pattern.compile(
            "(?is)(?:\\b(?:I|we)(?:'ve|\\s+have)?\\s+(?:already\\s+|successfully\\s+)*"
                    + "(?:added|created|deleted|removed|renamed|updated|modified|changed|applied|ran|started|"
                    + "stopped|cancelled|canceled|verified|simulated|saved|reset|replaced|imported|completed|"
                    + "finished)\\b[^.!?。！？]{0,160}?\\b(?:devices?|rules?|specs?|specifications?|board|scene|"
                    + "simulation|verification|traces?|templates?|environment\\s+variables?|model)\\b"
                    + "|\\b(?:added|created|deleted|removed|renamed|updated|modified|changed|applied|ran|started|"
                    + "stopped|cancelled|canceled|verified|simulated|saved|reset|replaced|imported|completed|"
                    + "finished)\\s+(?:all|every|the|your|current|these|those|our)\\s+"
                    + "(?:devices?|rules?|specs?|specifications?|board|scene|simulation|verification|traces?|"
                    + "templates?|environment\\s+variables?|model)\\b"
                    + "|\\b(?:all|every|the|your|current|these|those|our)\\s+"
                    + "(?:devices?|rules?|specs?|specifications?|board|scene|traces?|templates?|"
                    + "environment\\s+variables?|model)\\s+(?:successfully\\s+)?"
                    + "(?:added|created|deleted|removed|renamed|updated|modified|changed|applied|saved|reset|"
                    + "replaced|imported)\\b"
                    + "|\\b(?:the|all|every|your|current|these|those|our)?\\s*"
                    + "(?:devices?|rules?|specs?|specifications?|board|scene|simulation|verification|traces?|"
                    + "templates?|environment\\s+variables?|model)\\b[^.!?。！？]{0,80}"
                    + "\\b(?:was|were|has\\s+been|have\\s+been|is\\s+now|are\\s+now)\\s+"
                    + "(?:successfully\\s+)?"
                    + "(?:added|created|deleted|removed|renamed|updated|modified|changed|applied|saved|reset|"
                    + "replaced|imported)\\b"
                    + "|\\b(?:the|your|current|our)?\\s*(?:simulation|verification)\\b[^.!?。！？]{0,80}"
                    + "\\b(?:was|has\\s+been|is\\s+now)\\s+(?:successfully\\s+)?"
                    + "(?:started|stopped|cancelled|canceled|verified|simulated|completed|finished)\\b"
                    + "|\\b(?:the|all|every|your|current|these|those|our)?\\s*"
                    + "(?:simulation|verification|model)\\b[^.!?。！？]{0,40}\\b"
                    + "(?:is|was|has\\s+been)\\s+(?:now\\s+)?(?:complete|completed|successful|finished)\\b"
                    + "|(?:(?:我|本助手|我们)(?:已经|已)?(?:成功)?|(?:已经|已)(?:成功)?)"
                    + "(?:添加|创建|删除|移除|重命名|更新|修改|应用|运行|启动|停止|取消|验证|模拟|保存|重置|"
                    + "替换|导入|完成)(?:了)?[^.!?。！？]{0,160}?"
                    + "(?:设备|规则|规约|画布|场景|仿真|模拟|验证|轨迹|模板|环境变量)"
                    + "|(?:全部|所有|你的|您的|当前|这些|该)?"
                    + "(?:设备|规则|规约|画布|场景|仿真|模拟|验证|轨迹|模板|环境变量)"
                    + "[^.!?。！？]{0,80}(?:已经|已)(?:成功)?(?:被)?"
                    + "(?:添加|创建|删除|移除|重命名|更新|修改|应用|保存|重置|替换|导入)"
                    + "|(?:(?:我|本助手|我们)(?:已经|已)?(?:成功)?)"
                    + "(?:更新|修改|重置|替换)(?:了)?(?:当前|你的|您的)?模型"
                    + "|(?:当前|你的|您的)模型[^.!?。！？]{0,40}(?:已经|已)(?:成功)?(?:被)?"
                    + "(?:更新|修改|重置|替换)"
                    + "|(?:当前|该)?(?:仿真|模拟|验证)[^.!?。！？]{0,80}(?:已经|已)(?:成功)?(?:被)?"
                    + "(?:运行|启动|停止|取消|验证|模拟|完成))");
    private static final Pattern NON_OPERATIONAL_PLATFORM_CONTENT = Pattern.compile(
            "(?is)(?:\\b(?:created|drafted|wrote|generated|proposed)\\b[^.!?。！？]{0,48}"
                    + "\\b(?:sample|example|illustrative|hypothetical|draft)\\s+"
                    + "(?:device|rule|spec|specification|scene|model|configuration)\\b"
                    + "|(?:创建|生成|编写|起草|提供)(?:了)?[^.!?。！？]{0,48}"
                    + "(?:示例|样例|假设|草案|参考)(?:设备|规则|规约|场景|模型|配置)"
                    + "|(?:已)?(?:删除|移除|重命名|更新|修改|取消)的"
                    + "(?:设备|规则|规约|画布|场景|轨迹|模板|环境变量|模型))");
    private static final Pattern UNSUPPORTED_PLATFORM_READ_CLAIM = Pattern.compile(
            "(?is)(?:\\b(?:your(?:\\s+current)?|the\\s+current|current)\\s+"
                    + "(?:board|scene)\\s+(?:currently\\s+)?(?:contains?|has|includes?|shows?|lists?)\\b"
                    + "|\\b(?:I|we)(?:'ve|\\s+have)?\\s+"
                    + "(?:checked|inspected|read|reviewed|examined|looked\\s+at)\\s+"
                    + "(?:your(?:\\s+current)?|the(?:\\s+current)?|current)\\s+"
                    + "(?:board|scene|devices?|rules?|specs?|specifications?|model)\\b"
                    + "|\\b(?:I|we)(?:'ve|\\s+have)?\\s+(?:(?:can|could)\\s+)?"
                    + "(?:see|saw|seen|found|observ(?:e|ed)|list(?:ed)?)\\b[^.!?。！？]{0,96}"
                    + "\\b(?:devices?|rules?|specs?|specifications?)\\b[^.!?。！？]{0,48}"
                    + "\\b(?:on|in)\\s+(?:your(?:\\s+current)?|the(?:\\s+current)?|current)\\s+"
                    + "(?:board|scene)\\b"
                    + "|\\bthere\\s+(?:is|are)\\s+[^.!?。！？]{0,80}"
                    + "\\b(?:devices?|rules?|specs?|specifications?)\\b[^.!?。！？]{0,40}"
                    + "\\b(?:on|in)\\s+(?:your(?:\\s+current)?|the\\s+current|current)\\s+"
                    + "(?:board|scene)\\b"
                    + "|(?:当前|你的|您的)(?:画布|场景)(?:中)?(?:有|包含|共有|显示)"
                    + "|(?:我|我们|本助手)(?:已经|已)?(?:查看|检查|读取|核对)(?:了)?"
                    + "(?:当前|你的|您的)(?:画布|场景|设备|规则|规约|模型))");
    private static final Pattern NON_ASSERTIVE_CLAIM_CONTEXT = Pattern.compile(
            "(?is)(?:\\b(?:whether|hypothetically)\\b|\\bif\\s+(?:the|your|this|that)\\b"
                    + "|(?:是否|假设|如果))");
    private static final Pattern HISTORICAL_CLAIM_CONTEXT = Pattern.compile(
            "(?is)(?:\\b(?:previously|historically)\\b"
                    + "|\\b(?:during|in|from)\\s+(?:the\\s+)?"
                    + "(?:previous|prior|earlier|last|historical)\\b"
                    + "|(?:在|于)?(?:上次|先前|此前|之前|过去)(?:迁移|运行|记录|会话)?(?:中|期间)?)");
    private static final Pattern CURRENT_CLAIM_CONTEXT = Pattern.compile(
            "(?is)(?:\\b(?:current|now|this\\s+turn)\\b"
                    + "|\\byour(?:\\s+current)?\\s+(?:board|scene)\\b"
                    + "|(?:当前|本轮|现在|你的画布|您的画布))");
    private static final Pattern LEADING_HISTORICAL_CLAIM_CONTEXT = Pattern.compile(
            "(?is)^\\s*(?:previously|historically"
                    + "|(?:during|in|from)\\s+(?:the\\s+)?"
                    + "(?:previous|prior|earlier|last|historical)\\b[^,，.!?。！？]{0,48}"
                    + "|(?:在|于)?(?:上次|先前|此前|之前|过去)(?:迁移|运行|记录|会话)?(?:中|期间)?)"
                    + "\\s*[,，]\\s*(?:(?:the|all|every|your|these|those|our)\\s+"
                    + "|(?:全部|所有|你的|您的|这些|该)\\s*)*$");
    private static final Pattern CLAIM_CLAUSE_BOUNDARY = Pattern.compile(
            "(?is)[,，;；:：\\n]|\\b(?:but|however|yet|then|and)\\b|(?:但是|不过|然而|然后|并且|而且|但)");
    private static final Set<String> TOOL_RESULT_OUTCOMES = Set.of(
            "USABLE", "PARTIAL", "FAILED", "RESULT_UNAVAILABLE", "CONFIRMATION_REQUIRED");
    private static final Set<String> EXECUTION_GUARD_OUTCOMES = Set.of(
            "NO_PROGRESS", "EMERGENCY_LIMIT");

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

    @Override
    @Transactional(readOnly = true)
    public List<ChatSessionResponseDto> getUserSessions(Long userId) {
        LocalDateTime now = databaseNow();
        List<ChatSessionPo> sessions = sessionRepo.findTop100ByUserIdOrderByUpdatedAtDesc(userId);
        List<ChatSessionResponseDto> response = chatMapper.toChatSessionDtoList(sessions);
        for (int index = 0; index < response.size(); index++) {
            response.get(index).setActive(hasActiveExecutionLease(sessions.get(index), now));
        }
        return response;
    }

    @Override
    @Transactional
    public ChatSessionResponseDto createSession(Long userId) {
        requireActiveUserForWrite(userId);
        if (sessionRepo.countByUserId(userId) >= RequestLimits.MAX_CHAT_SESSIONS) {
            throw new BadRequestException("At most 100 chat sessions can be stored per user. Delete an old session first.");
        }
        ChatSessionPo session = new ChatSessionPo();
        session.setId(UUID.randomUUID().toString());
        session.setUserId(userId);
        session.setTitle(null);
        LocalDateTime now = databaseNow();
        session.setCreatedAt(now);
        session.setUpdatedAt(now);
        return chatMapper.toChatSessionDto(sessionRepo.save(session));
    }

    @Override
    @Transactional(readOnly = true)
    public ChatPendingConfirmationDto getPendingConfirmation(Long userId, String sessionId) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        List<ChatConfirmationCommandDto.Kind> kinds = pendingProtectedKinds(userId, sessionId).stream()
                .map(ChatServiceImpl::toCommandKind)
                .toList();
        return ChatPendingConfirmationDto.builder()
                .sessionId(sessionId)
                .kinds(kinds)
                .build();
    }

    @Override
    @Transactional(readOnly = true)
    public List<ChatMessageResponseDto> getHistory(Long userId, String sessionId) {
        return getHistoryPage(userId, sessionId, null, RequestLimits.MAX_CHAT_HISTORY_PAGE_SIZE)
                .getMessages();
    }

    @Override
    @Transactional(readOnly = true)
    public ChatHistoryPageDto getHistoryPage(Long userId, String sessionId, Long beforeId, int limit) {
        sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        int pageSize = Math.min(RequestLimits.MAX_CHAT_HISTORY_PAGE_SIZE,
                Math.max(1, limit));
        int rawPageSize = Math.min(200, RequestLimits.MAX_CHAT_HISTORY_RAW_SCAN);
        List<ChatMessagePo> newestFirst = new ArrayList<>();
        Long cursor = beforeId;
        boolean exhausted = false;
        while (newestFirst.size() < RequestLimits.MAX_CHAT_HISTORY_RAW_SCAN) {
            int remaining = Math.min(rawPageSize,
                    RequestLimits.MAX_CHAT_HISTORY_RAW_SCAN - newestFirst.size());
            List<ChatMessagePo> chunk = cursor == null
                    ? messageRepo.findBySessionIdOrderByIdDesc(sessionId, PageRequest.of(0, remaining))
                    : messageRepo.findBySessionIdAndIdLessThanOrderByIdDesc(
                            sessionId, cursor, PageRequest.of(0, remaining));
            if (chunk == null || chunk.isEmpty()) {
                exhausted = true;
                break;
            }
            newestFirst.addAll(chunk);
            ChatMessagePo oldest = chunk.get(chunk.size() - 1);
            cursor = oldest == null ? cursor : oldest.getId();
            if (chunk.size() < remaining || oldest == null || oldest.getId() == null) {
                exhausted = true;
                break;
            }
            List<ChatMessagePo> scannedChronologically = new ArrayList<>(newestFirst);
            java.util.Collections.reverse(scannedChronologically);
            if (filterFrontendVisibleMessages(scannedChronologically).size() > pageSize) {
                break;
            }
        }

        List<ChatMessagePo> allMessages = new ArrayList<>(newestFirst);
        java.util.Collections.reverse(allMessages);
        List<ChatMessagePo> visibleMessages = filterFrontendVisibleMessages(allMessages);
        boolean hasMore = visibleMessages.size() > pageSize || !exhausted;
        int fromIndex = Math.max(0, visibleMessages.size() - pageSize);
        List<ChatMessagePo> selected = visibleMessages.subList(fromIndex, visibleMessages.size());
        List<ChatMessageResponseDto> response = chatMapper.toChatMessageDtoList(selected);
        attachPersistedExecutionTraces(selected, response);
        Long nextBeforeId = null;
        if (hasMore) {
            if (!selected.isEmpty()) {
                nextBeforeId = selected.get(0).getId();
            } else if (!allMessages.isEmpty()) {
                nextBeforeId = allMessages.get(0).getId();
            }
        }
        return ChatHistoryPageDto.builder()
                .messages(response)
                .nextBeforeId(nextBeforeId)
                .hasMore(hasMore && nextBeforeId != null)
                .build();
    }

    @Override
    @Transactional
    public void deleteSession(Long userId, String sessionId) {
        synchronized (sessionLock(sessionId)) {
            requireActiveUserForWrite(userId);
            ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
            if (hasActiveExecutionLease(session, databaseNow())) {
                throw new ChatSessionBusyException(sessionId);
            }
            messageRepo.deleteBySessionId(sessionId);
            sessionRepo.deleteById(Objects.requireNonNull(sessionId, "sessionId must not be null"));
            destructiveActionGuard.clearSession(userId, sessionId);
            scenarioDraftStore.clearSession(userId, sessionId);
            taskContinuationStore.clearSession(userId, sessionId);
        }
    }

    @Override
    public String beginStreamRequest(Long userId, String sessionId, String turnId, String content) {
        String effectiveTurnId = requireTurnId(turnId);
        String effectiveContent = requireTurnContent(content);
        synchronized (sessionLock(sessionId)) {
            AtomicReference<ActiveStreamRequest> claimed = new AtomicReference<>();
            AtomicLong confirmationStartedNanos = new AtomicLong(Long.MIN_VALUE);
            AtomicBoolean stoppedBeforeAdmission = new AtomicBoolean();
            try {
                transactionTemplate.executeWithoutResult(status -> {
                    requireActiveUserForWrite(userId);
                    ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId)
                            .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
                    if (session.getPreAdmissionStopTurnIds().remove(effectiveTurnId)) {
                        sessionRepo.saveAndFlush(session);
                        stoppedBeforeAdmission.set(true);
                        return;
                    }
                    confirmationStartedNanos.set(System.nanoTime());
                    LocalDateTime now = databaseNow();
                    if (hasActiveExecutionLease(session, now)) {
                        throw new ChatSessionBusyException(sessionId);
                    }
                    long messageCount = messageRepo.countBySessionId(sessionId);
                    long requiredTurnCapacity = requiredMessageCapacityForTurn();
                    if (messageCount + requiredTurnCapacity > chatExecutionConfig.getMaxMessagesPerSession()) {
                        throw new ChatHistoryQuotaExceededException(
                                messageCount,
                                chatExecutionConfig.getMaxMessagesPerSession(),
                                requiredTurnCapacity);
                    }
                    if (messageRepo.existsBySessionIdAndTurnId(sessionId, effectiveTurnId)) {
                        throw new ConflictException("Turn id has already been used in this chat session.");
                    }
                    String requestId = UUID.randomUUID().toString();
                    session.setActiveExecutionId(requestId);
                    session.setActiveExecutionTurnId(effectiveTurnId);
                    session.setActiveExecutionExpiresAt(now.plus(executionLeaseTtl()));
                    session.setExecutionStopRequested(false);
                    session.setExecutionUserStopRequested(false);
                    sessionRepo.saveAndFlush(session);
                    saveUserTurn(sessionId, effectiveTurnId, requestId, effectiveContent);
                    claimed.set(new ActiveStreamRequest(
                            userId, requestId, effectiveTurnId, effectiveContent,
                            confirmationStartedNanos.get()));
                });
            } catch (RuntimeException admissionFailure) {
                ActiveStreamRequest ambiguousRequest = claimed.get();
                if (ambiguousRequest == null) throw admissionFailure;
                try {
                    compensateAmbiguousAdmission(userId, sessionId, ambiguousRequest);
                } catch (RuntimeException compensationFailure) {
                    ChatAdmissionOutcomeUnknownException unknown =
                            new ChatAdmissionOutcomeUnknownException(
                                    "Could not confirm the outcome of the chat admission transaction.",
                                    admissionFailure);
                    unknown.addSuppressed(compensationFailure);
                    throw unknown;
                }
                throw new ServiceUnavailableException(
                        "Chat admission could not be committed; retry", admissionFailure);
            }
            if (stoppedBeforeAdmission.get()) {
                throw new ConflictException("This chat turn was stopped before execution began.");
            }
            ActiveStreamRequest request = claimed.get();
            if (request == null) {
                throw new IllegalStateException("Could not claim the chat execution lease.");
            }
            if (!leaseRoundTripLeavesHeartbeatWindow(
                    confirmationStartedNanos.get(), executionLeaseTtl())) {
                abortClaimedStreamRequest(userId, sessionId, request);
                throw new ServiceUnavailableException(
                        "Chat execution lease expired before the request was accepted; retry");
            }
            ActiveStreamRequest existing = activeStreamRequests.putIfAbsent(sessionId, request);
            if (existing != null) {
                abortClaimedStreamRequest(userId, sessionId, request);
                throw new ChatSessionBusyException(sessionId);
            }
            if (!leaseRoundTripLeavesHeartbeatWindow(
                    confirmationStartedNanos.get(), executionLeaseTtl())) {
                abortClaimedStreamRequest(userId, sessionId, request);
                throw new ServiceUnavailableException(
                        "Chat execution lease expired before the request was accepted; retry");
            }
            return request.requestId();
        }
    }

    @Override
    public void abortUndispatched(
            Long userId, String sessionId, String executionId, String turnId) {
        String effectiveTurnId = requireTurnId(turnId);
        if (executionId == null || executionId.isBlank()) {
            throw new IllegalArgumentException("Execution id is required to abort an undispatched chat turn.");
        }
        synchronized (sessionLock(sessionId)) {
            try {
                transactionTemplate.executeWithoutResult(status -> {
                    ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId)
                            .orElse(null);
                    if (session == null) {
                        requireAdmittedUserTurnAbsent(sessionId, effectiveTurnId, executionId);
                        return;
                    }
                    int deleted = messageRepo.deleteBySessionIdAndTurnIdAndExecutionIdAndRole(
                            sessionId, effectiveTurnId, executionId, "user");
                    if (deleted != 1) {
                        throw new IllegalStateException(
                                "The admitted user turn could not be identified uniquely for rollback.");
                    }
                    if (Objects.equals(executionId, session.getActiveExecutionId())) {
                        clearExecutionLease(session);
                        sessionRepo.saveAndFlush(session);
                    }
                });
            } finally {
                activeStreamRequests.computeIfPresent(sessionId, (ignored, request) ->
                        Objects.equals(request.userId(), userId)
                                && Objects.equals(request.requestId(), executionId)
                                && Objects.equals(request.turnId(), effectiveTurnId)
                                ? null : request);
            }
        }
    }

    private void abortClaimedStreamRequest(
            Long userId, String sessionId, ActiveStreamRequest request) {
        try {
            abortUndispatched(userId, sessionId, request.requestId(), request.turnId());
        } catch (RuntimeException rollbackFailure) {
            throw new ChatAdmissionOutcomeUnknownException(
                    "Could not confirm rollback of the persisted chat admission.", rollbackFailure);
        }
    }

    private void compensateAmbiguousAdmission(
            Long userId, String sessionId, ActiveStreamRequest request) {
        try {
            transactionTemplate.executeWithoutResult(status -> {
                ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId)
                        .orElse(null);
                if (session == null) {
                    requireAdmittedUserTurnAbsent(
                            sessionId, request.turnId(), request.requestId());
                    return;
                }
                int deleted = messageRepo.deleteBySessionIdAndTurnIdAndExecutionIdAndRole(
                        sessionId, request.turnId(), request.requestId(), "user");
                if (deleted == 0 && messageRepo.existsBySessionIdAndTurnId(
                        sessionId, request.turnId())) {
                    throw new IllegalStateException(
                            "The ambiguous admission turn belongs to a different execution.");
                }
                if (deleted > 1) {
                    throw new IllegalStateException(
                            "The ambiguous admission matched multiple user turns.");
                }
                if (Objects.equals(request.requestId(), session.getActiveExecutionId())) {
                    clearExecutionLease(session);
                    sessionRepo.saveAndFlush(session);
                }
            });
        } finally {
            activeStreamRequests.remove(sessionId, request);
        }
    }

    private void requireAdmittedUserTurnAbsent(
            String sessionId, String turnId, String executionId) {
        if (messageRepo.existsBySessionIdAndTurnIdAndExecutionIdAndRole(
                sessionId, turnId, executionId, "user")) {
            throw new IllegalStateException(
                    "The chat session disappeared while its admitted user turn still exists.");
        }
    }

    @Override
    public void endStreamRequest(Long userId, String sessionId, String executionId) {
        if (sessionId == null || executionId == null || executionId.isBlank()) return;
        activeStreamRequests.computeIfPresent(sessionId, (ignored, request) ->
                Objects.equals(request.userId(), userId)
                        && Objects.equals(request.requestId(), executionId)
                        ? null
                        : request);
        releaseExecutionLease(userId, sessionId, executionId);
    }

    @Override
    public void requestStreamStop(Long userId, String sessionId, String turnId) {
        String effectiveTurnId = turnId == null ? null : requireTurnId(turnId);
        synchronized (sessionLock(sessionId)) {
            AtomicReference<String> requestIdRef = new AtomicReference<>();
            transactionTemplate.executeWithoutResult(status -> {
                ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId)
                        .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
                if (!hasActiveExecutionLease(session, databaseNow())) {
                    if (effectiveTurnId == null
                            || Objects.equals(effectiveTurnId, session.getActiveExecutionTurnId())) {
                        requestIdRef.set(session.getActiveExecutionId());
                    }
                    clearExecutionLease(session);
                    recordPreAdmissionStopIfNeeded(session, effectiveTurnId);
                    sessionRepo.saveAndFlush(session);
                    return;
                }
                if (effectiveTurnId != null
                        && !Objects.equals(effectiveTurnId, session.getActiveExecutionTurnId())) {
                    recordPreAdmissionStopIfNeeded(session, effectiveTurnId);
                    sessionRepo.saveAndFlush(session);
                    return;
                }
                session.setExecutionStopRequested(true);
                session.setExecutionUserStopRequested(true);
                sessionRepo.saveAndFlush(session);
                requestIdRef.set(session.getActiveExecutionId());
            });
            String requestId = requestIdRef.get();
            ActiveStreamRequest request = activeStreamRequests.get(sessionId);
            if (request != null && Objects.equals(request.userId(), userId)
                    && Objects.equals(request.requestId(), requestId)) {
                stopActiveRequest(sessionId, request, true);
            }
        }
    }

    private void recordPreAdmissionStopIfNeeded(ChatSessionPo session, String turnId) {
        if (turnId == null || messageRepo.existsBySessionIdAndTurnId(session.getId(), turnId)) return;
        Set<String> stoppedTurns = session.getPreAdmissionStopTurnIds();
        if (!stoppedTurns.contains(turnId) && stoppedTurns.size() >= MAX_PRE_ADMISSION_STOP_TURNS) {
            throw new ConflictException(
                    "Too many chat turns are waiting for pre-admission stop acknowledgement.");
        }
        stoppedTurns.add(turnId);
    }

    @Override
    public void requestLocalUserExecutionStop(Long userId) {
        if (userId == null) return;
        try {
            independentTransactionTemplate().executeWithoutResult(status -> {
                List<ChatSessionPo> sessions = sessionRepo.findByUserIdForUpdate(userId);
                LocalDateTime now = databaseNow();
                for (ChatSessionPo session : sessions) {
                    if (!hasActiveExecutionLease(session, now)) continue;
                    // Account cleanup is a silent transport stop, not an explicit user cancellation.
                    session.setExecutionStopRequested(true);
                    session.setExecutionUserStopRequested(false);
                }
                sessionRepo.saveAllAndFlush(sessions);
            });
        } catch (RuntimeException e) {
            log.warn("Could not mark chat sessions stopped for deleted user {}", userId, e);
        }
        activeStreamRequests.forEach((sessionId, request) -> {
            if (!Objects.equals(request.userId(), userId)) return;
            stopActiveRequest(sessionId, request, false);
        });
        runUserCleanupStep("destructive-action confirmations", () -> destructiveActionGuard.clearUser(userId));
        runUserCleanupStep("scenario drafts", () -> scenarioDraftStore.clearUser(userId));
        runUserCleanupStep("task continuations", () -> taskContinuationStore.clearUser(userId));
    }

    private TransactionTemplate independentTransactionTemplate() {
        TransactionTemplate independent = new TransactionTemplate(
                Objects.requireNonNull(transactionTemplate.getTransactionManager(),
                        "transaction manager is required"));
        independent.setPropagationBehavior(TransactionDefinition.PROPAGATION_REQUIRES_NEW);
        return independent;
    }

    private void runUserCleanupStep(String resource, Runnable cleanup) {
        try {
            cleanup.run();
        } catch (RuntimeException e) {
            log.warn("Could not clear {} during account cleanup", resource, e);
        }
    }

    private void stopActiveRequest(String sessionId, ActiveStreamRequest request, boolean userInitiated) {
        if (userInitiated) {
            request.userStopRequested().set(true);
        }
        request.stopRequested().set(true);
        request.requestControl().cancel();
        SseEmitter emitter = request.emitter().get();
        if (emitter == null) return;
        try {
            emitter.complete();
        } catch (IllegalStateException e) {
            log.debug("Chat emitter was already complete while stopping session {}", sessionId);
        }
    }

    @Override
    @Transactional(readOnly = true)
    public ChatSessionActivityDto getSessionActivity(Long userId, String sessionId) {
        ChatSessionPo session = sessionRepo.findByIdAndUserId(sessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        return ChatSessionActivityDto.builder()
                .sessionId(sessionId)
                .active(hasActiveExecutionLease(session, databaseNow()))
                .build();
    }

    private void releaseExecutionLease(Long userId, String sessionId, String requestId) {
        transactionTemplate.executeWithoutResult(status -> {
            ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(sessionId, userId).orElse(null);
            if (session == null || !Objects.equals(session.getActiveExecutionId(), requestId)) return;
            clearExecutionLease(session);
            sessionRepo.saveAndFlush(session);
        });
    }

    private boolean hasActiveExecutionLease(ChatSessionPo session, LocalDateTime now) {
        return session != null
                && session.getActiveExecutionId() != null
                && !session.getActiveExecutionId().isBlank()
                && session.getActiveExecutionExpiresAt() != null
                && session.getActiveExecutionExpiresAt().isAfter(now);
    }

    private void clearExecutionLease(ChatSessionPo session) {
        session.setActiveExecutionId(null);
        session.setActiveExecutionTurnId(null);
        session.setActiveExecutionExpiresAt(null);
        session.setExecutionStopRequested(false);
        session.setExecutionUserStopRequested(false);
    }

    @Scheduled(fixedDelayString = "${chat.execution.lease-heartbeat-ms:10000}")
    public void maintainExecutionLeases() {
        try {
            databaseNow();
        } catch (RuntimeException e) {
            stopChatExecutionsWithExpiredConfirmation(e);
            return;
        }
        try {
            int cleared = sessionRepo.clearExpiredExecutionLeases(databaseNow());
            if (cleared > 0) {
                log.debug("Cleared {} expired chat execution lease(s)", cleared);
            }
        } catch (RuntimeException e) {
            log.warn("Could not clear expired chat execution leases: {}", e.toString());
        }
        Map<String, ActiveStreamRequest> requests = Map.copyOf(activeStreamRequests);
        ExecutionLeaseRenewalBatch renewal = ExecutionLeaseRenewalBatch.none();
        try {
            renewal = renewActiveExecutionLeases(requests);
            ExecutionLeaseRenewalBatch confirmedRenewal = renewal;
            requests.forEach((sessionId, request) -> {
                if (activeStreamRequests.get(sessionId) != request) return;
                ExecutionLeaseState state = confirmedRenewal.renewedLeases().get(sessionId);
                if (state == null || !Objects.equals(state.requestId(), request.requestId())) {
                    if (activeStreamRequests.remove(sessionId, request)) {
                        stopActiveRequest(sessionId, request, false);
                        log.warn("Stopped local chat execution after losing its lease: sessionId={}, executionId={}",
                                sessionId, request.requestId());
                    }
                    return;
                }
                request.leaseConfirmation().confirmAt(confirmedRenewal.confirmationStartedNanos());
                if (state.stopRequested()) {
                    stopActiveRequest(sessionId, request, state.userStopRequested());
                }
            });
        } catch (RuntimeException e) {
            requests.forEach((sessionId, request) -> {
                if (request.leaseConfirmation().isUnconfirmedFor(executionLeaseTtl())
                        && activeStreamRequests.remove(sessionId, request)) {
                    stopActiveRequest(sessionId, request, false);
                    log.warn("Stopped local chat execution after its lease could not be confirmed for a full TTL: "
                                    + "sessionId={}, executionId={}",
                            sessionId, request.requestId());
                } else {
                    log.warn("Could not renew chat execution lease for session {}: {}", sessionId, e.toString());
                }
            });
        }
        if (!renewal.renewedLeases().isEmpty()
                && !leaseRoundTripLeavesHeartbeatWindow(
                        renewal.confirmationStartedNanos(), executionLeaseTtl())) {
            renewal.renewedLeases().forEach((sessionId, state) -> {
                ActiveStreamRequest request = requests.get(sessionId);
                if (request != null && Objects.equals(state.requestId(), request.requestId())
                        && activeStreamRequests.remove(sessionId, request)) {
                    stopActiveRequest(sessionId, request, false);
                    log.warn("Stopped local chat execution because lease maintenance consumed its heartbeat window: "
                                    + "sessionId={}, executionId={}",
                            sessionId, request.requestId());
                }
            });
        }
    }

    private ExecutionLeaseRenewalBatch renewActiveExecutionLeases(
            Map<String, ActiveStreamRequest> requests) {
        if (requests.isEmpty()) return ExecutionLeaseRenewalBatch.none();

        Set<String> sessionIds = new LinkedHashSet<>(requests.keySet());
        long confirmationStartedNanos = System.nanoTime();
        long checkedAtNanos = confirmationStartedNanos;
        LocalDateTime checkedAt = databaseNow();
        Map<String, ExecutionLeaseState> renewedLeases = transactionTemplate.execute(status -> {
            List<ChatSessionPo> sessions = sessionRepo.findByIdInForUpdate(sessionIds);
            LocalDateTime databaseNow = databaseNow();
            long elapsedNanos = Math.max(0L, System.nanoTime() - checkedAtNanos);
            LocalDateTime monotonicNow = checkedAt.plusNanos(elapsedNanos);
            LocalDateTime effectiveNow = databaseNow.isAfter(monotonicNow) ? databaseNow : monotonicNow;
            List<ChatSessionPo> renewableSessions = new ArrayList<>();
            Map<String, ExecutionLeaseState> states = new HashMap<>();
            for (ChatSessionPo session : sessions) {
                ActiveStreamRequest request = requests.get(session.getId());
                if (request == null
                        || !Objects.equals(request.userId(), session.getUserId())
                        || !Objects.equals(request.requestId(), session.getActiveExecutionId())
                        || session.getActiveExecutionExpiresAt() == null
                        || !session.getActiveExecutionExpiresAt().isAfter(effectiveNow)) {
                    continue;
                }
                renewableSessions.add(session);
                states.put(session.getId(), new ExecutionLeaseState(
                        request.requestId(),
                        Boolean.TRUE.equals(session.getExecutionStopRequested()),
                        Boolean.TRUE.equals(session.getExecutionUserStopRequested())));
            }
            if (renewableSessions.isEmpty()) return Map.of();

            LocalDateTime renewedExpiry = effectiveNow.plus(executionLeaseTtl());
            renewableSessions.forEach(session -> session.setActiveExecutionExpiresAt(renewedExpiry));
            sessionRepo.flush();
            return Map.copyOf(states);
        });
        if (renewedLeases == null || renewedLeases.isEmpty()
                || !leaseRoundTripLeavesHeartbeatWindow(
                        confirmationStartedNanos, executionLeaseTtl())) {
            return ExecutionLeaseRenewalBatch.none();
        }
        return new ExecutionLeaseRenewalBatch(
                renewedLeases, confirmationStartedNanos);
    }

    private boolean leaseRoundTripLeavesHeartbeatWindow(long startedNanos, Duration ttl) {
        if (startedNanos == Long.MIN_VALUE || ttl == null || ttl.isZero() || ttl.isNegative()) {
            return false;
        }
        Duration heartbeat = Duration.ofMillis(chatExecutionConfig.getLeaseHeartbeatMs());
        if (heartbeat.isZero() || heartbeat.isNegative() || ttl.compareTo(heartbeat) <= 0) {
            return false;
        }
        long elapsedNanos = System.nanoTime() - startedNanos;
        return elapsedNanos >= 0 && elapsedNanos < ttl.minus(heartbeat).toNanos();
    }

    private void stopChatExecutionsWithExpiredConfirmation(RuntimeException cause) {
        activeStreamRequests.forEach((sessionId, request) -> {
            if (request.leaseConfirmation().isUnconfirmedFor(executionLeaseTtl())
                    && activeStreamRequests.remove(sessionId, request)) {
                stopActiveRequest(sessionId, request, false);
                log.warn("Stopped local chat execution after the database could not confirm its lease for a full TTL: "
                                + "sessionId={}, executionId={}",
                        sessionId, request.requestId());
            }
        });
        log.warn("Could not read database time while maintaining chat execution leases: {}", cause.toString());
    }

    private Duration executionLeaseTtl() {
        return Duration.ofMillis(chatExecutionConfig.getLeaseTtlMs());
    }

    private LocalDateTime databaseNow() {
        return Objects.requireNonNull(
                sessionRepo.currentDatabaseTime(),
                "Database current timestamp must not be null");
    }

    private Object sessionLock(String sessionId) {
        String requiredSessionId = Objects.requireNonNull(sessionId, "sessionId must not be null");
        int hash = requiredSessionId.hashCode();
        hash ^= hash >>> 16;
        return SESSION_LOCKS[hash & (SESSION_LOCK_STRIPES - 1)];
    }

    private static Object[] createSessionLocks() {
        Object[] locks = new Object[SESSION_LOCK_STRIPES];
        Arrays.setAll(locks, ignored -> new Object());
        return locks;
    }

    @Override
    public void processStreamChat(Long userId,
                                  String sessionId,
                                  String executionId,
                                  String turnId,
                                  String content,
                                  ChatConfirmationCommandDto confirmation,
                                  SseEmitter emitter) {
        if (turnId == null || turnId.isBlank()) {
            throw new BadRequestException("Turn id is required");
        }
        String effectiveTurnId = turnId.trim();
        ActiveStreamRequest activeRequest = activeStreamRequests.get(sessionId);
        if (activeRequest == null
                || !Objects.equals(activeRequest.userId(), userId)
                || !Objects.equals(activeRequest.requestId(), executionId)) {
            log.warn("Rejected chat worker without its claimed execution lease: sessionId={}, executionId={}",
                    sessionId, executionId);
            try {
                emitter.complete();
            } catch (IllegalStateException e) {
                log.debug("Chat emitter was already complete for unowned execution {}", executionId);
            }
            return;
        }
        if (!activeRequest.matches(effectiveTurnId, content)) {
            log.error("Rejected chat worker whose turn payload differs from its admitted request: "
                            + "sessionId={}, executionId={}, turnId={}",
                    sessionId, executionId, effectiveTurnId);
            try {
                emitter.completeWithError(new IllegalStateException(
                        "The dispatched chat turn does not match its persisted admission."));
            } catch (IllegalStateException e) {
                log.debug("Chat emitter was already complete for mismatched execution {}", executionId);
            }
            return;
        }
        AiDestructiveActionGuard.PendingActionContext destructivePending;
        AiScenarioDraftStore.PendingApplication scenarioPending;
        AiTaskContinuationStore.ContinuationContext continuationContext;
        ConfirmationDecision confirmationDecision;
        boolean preferChinese = prefersChinese(content);
        StringBuilder finalAnswer = new StringBuilder();
        List<StreamResponseDto.ProgressDto> executionTrace = new ArrayList<>();
        long executionStartedNanos = System.nanoTime();
        AtomicBoolean isDisconnect = activeRequest.stopRequested();
        AtomicBoolean isUserStop = activeRequest.userStopRequested();
        BooleanSupplier shouldStop = () -> synchronizeExecutionStop(
                userId, sessionId, activeRequest, isDisconnect, isUserStop, false);
        BooleanSupplier forceStopCheck = () -> synchronizeExecutionStop(
                userId, sessionId, activeRequest, isDisconnect, isUserStop, true);
        activeRequest.emitter().compareAndSet(null, emitter);
        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        ToolLoopResult loopResult = ToolLoopResult.empty();
        TerminalPersistenceState terminalPersistence = TerminalPersistenceState.NOT_ATTEMPTED;
        AtomicBoolean serverCompletion = new AtomicBoolean(false);
        emitter.onCompletion(() -> {
            if (!serverCompletion.get()) {
                isDisconnect.set(true);
                activeRequest.requestControl().cancel();
            }
        });
        emitter.onTimeout(() -> {
            isDisconnect.set(true);
            activeRequest.requestControl().cancel();
        });
        emitter.onError(ex -> {
            isDisconnect.set(true);
            activeRequest.requestControl().cancel();
        });
        try {
            UserContextHolder.setUserId(userId);
            UserContextHolder.setChatSessionId(sessionId);
            UserContextHolder.setChatExecutionId(executionId);
            LlmRequestControlHolder.set(activeRequest.requestControl());
            destructivePending = destructiveActionGuard.pendingContext(userId, sessionId).orElse(null);
            scenarioPending = scenarioDraftStore.pendingApplication(userId, sessionId).orElse(null);
            continuationContext = taskContinuationStore.pendingContext(userId, sessionId).orElse(null);
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
            confirmationDecision = resolveConfirmation(content, confirmation, pendingKinds);
            if (confirmationDecision.cancelled()) {
                clearCancelledPendingAction(userId, sessionId, confirmationDecision.kind());
            }
            UserContextHolder.setConfirmedProtectedActionKind(
                    confirmationDecision.confirmed() && confirmationDecision.kind() != ConfirmationKind.CHOICE
                            ? confirmationDecision.kind().name()
                            : null);
            executeOwnedSessionWrite(userId, sessionId, executionId,
                    () -> touchSessionTitle(sessionId, userId, content));
            if (shouldStop.getAsBoolean()) {
                return;
            }
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
                    preferChinese, executionTrace, executionId, shouldStop, forceStopCheck);

            if (forceStopCheck.getAsBoolean()) {
                return;
            }

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

            if (shouldStop.getAsBoolean()) {
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
            List<LlmMessage> visibleReplyMessages = withVisibleReplyPrompt(messages, loopResult);
            ReplyGuardOutcome replyGuardOutcome = streamGuardedAssistantReply(
                    visibleReplyMessages, finalAnswer, emitter, isDisconnect, shouldStop,
                    preferChinese, executionTrace);
            boolean finalResponseProduced = finalAnswer.length() > replyStart;

            if (!finalResponseProduced && !isDisconnect.get()) {
                String fallbackText = missingFinalResponseFallback(loopResult, preferChinese);
                if (sendSseChunk(emitter, fallbackText)) {
                    finalAnswer.append(fallbackText);
                }
            }

            if (forceStopCheck.getAsBoolean()) {
                return;
            }

            ChatExecutionStatus finalStatus = terminalStatus(loopResult, replyGuardOutcome);
            String userStoppedNotice = interruptedAuditNotice(loopResult, preferChinese, true);
            TerminalPersistenceResult persistedTerminal = persistAssistantTerminal(
                    userId,
                    sessionId,
                    executionId,
                    effectiveTurnId,
                    finalAnswer.toString(),
                    executionTrace,
                    elapsedSeconds(executionStartedNanos),
                    finalStatus,
                    userStoppedNotice);
            terminalPersistence = persistedTerminal.persisted()
                    ? TerminalPersistenceState.PERSISTED
                    : TerminalPersistenceState.FAILED;
            if (terminalPersistence == TerminalPersistenceState.FAILED) {
                serverCompletion.set(true);
                sendSseErrorMessage(
                        emitter, terminalPersistenceFailureMessage(preferChinese), isDisconnect);
                return;
            }
            ChatExecutionStatus persistedStatus = persistedTerminal.executionStatus();
            if (persistedStatus == ChatExecutionStatus.STOPPED
                    && !sendSseChunk(emitter, userStoppedNotice)) {
                isDisconnect.set(true);
                return;
            }
            if (!sendSseTerminal(emitter, effectiveTurnId, persistedStatus)) {
                isDisconnect.set(true);
                return;
            }
            serverCompletion.set(true);
            completeEmitter(emitter, isDisconnect);
        } catch (Exception e) {
            if (isDisconnect.get() || isClientDisconnect(e)) {
                isDisconnect.set(true);
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
            ChatExecutionStatus status = loopResult.hadToolCalls()
                    || executionTrace.stream().anyMatch(progress ->
                            "TOOL_EXECUTION".equals(progress.getStage())
                                    || "TOOL_RESULT".equals(progress.getStage()))
                    || !commandSet.isEmpty()
                    ? ChatExecutionStatus.PARTIAL
                    : ChatExecutionStatus.FAILED;
            String userStoppedNotice = interruptedAuditNotice(loopResult, preferChinese, true);
            TerminalPersistenceResult persistedTerminal = persistAssistantTerminal(
                    userId,
                    sessionId,
                    executionId,
                    effectiveTurnId,
                    errorMessage,
                    executionTrace,
                    elapsedSeconds(executionStartedNanos),
                    status,
                    userStoppedNotice);
            terminalPersistence = persistedTerminal.persisted()
                    ? TerminalPersistenceState.PERSISTED
                    : TerminalPersistenceState.FAILED;
            if (terminalPersistence == TerminalPersistenceState.FAILED) {
                errorMessage += terminalPersistenceFailureSuffix(preferChinese);
                serverCompletion.set(true);
                sendSseErrorMessage(emitter, errorMessage, isDisconnect);
                return;
            }
            ChatExecutionStatus persistedStatus = persistedTerminal.executionStatus();
            if (persistedStatus == ChatExecutionStatus.STOPPED) {
                if (!sendSseChunk(emitter, userStoppedNotice)) {
                    isDisconnect.set(true);
                    return;
                }
            } else if (!sendSseError(emitter, errorMessage)) {
                isDisconnect.set(true);
                return;
            }
            if (!sendSseTerminal(emitter, effectiveTurnId, persistedStatus)) {
                isDisconnect.set(true);
                return;
            }
            serverCompletion.set(true);
            completeEmitter(emitter, isDisconnect);
        } finally {
            if (terminalPersistence == TerminalPersistenceState.NOT_ATTEMPTED
                    && isDisconnect.get()) {
                try {
                    ChatExecutionStatus interruptedStatus = isUserStop.get()
                            ? ChatExecutionStatus.STOPPED
                            : ChatExecutionStatus.DISCONNECTED;
                    String userStoppedNotice = interruptedAuditNotice(loopResult, preferChinese, true);
                    TerminalPersistenceResult persistedTerminal = persistAssistantTerminal(
                            userId,
                            sessionId,
                            executionId,
                            effectiveTurnId,
                            interruptedAuditNotice(loopResult, preferChinese, isUserStop.get()),
                            executionTrace,
                            elapsedSeconds(executionStartedNanos),
                            interruptedStatus,
                            userStoppedNotice);
                    if (persistedTerminal.persisted()) {
                        ChatExecutionStatus persistedStatus = persistedTerminal.executionStatus();
                        boolean streamWritable = persistedStatus != ChatExecutionStatus.STOPPED
                                || sendSseChunk(emitter, userStoppedNotice);
                        if (streamWritable) {
                            sendSseTerminal(emitter, effectiveTurnId, persistedStatus);
                        }
                    }
                } catch (RuntimeException e) {
                    log.warn("Could not settle interrupted chat stream for session {}: {}",
                            sessionId, e.toString());
                } finally {
                    serverCompletion.set(true);
                    completeInterruptedEmitter(emitter);
                }
            }
            UserContextHolder.clear();
            LlmRequestControlHolder.clear();
        }
    }

    private ConfirmationDecision resolveConfirmation(
            String content,
            ChatConfirmationCommandDto command,
            EnumSet<ConfirmationKind> pendingKinds) {
        if (command == null) {
            return pendingKinds.size() == 1 && pendingKinds.contains(ConfirmationKind.CHOICE)
                    ? chatConfirmationDetector.detect(content, pendingKinds)
                    : ConfirmationDecision.none();
        }
        ConfirmationKind requestedKind = switch (command.getKind()) {
            case DESTRUCTIVE -> ConfirmationKind.DESTRUCTIVE;
            case DEFAULT_TEMPLATE_RESET -> ConfirmationKind.DEFAULT_TEMPLATE_RESET;
            case SCENE_REPLACEMENT -> ConfirmationKind.SCENE_REPLACEMENT;
        };
        if (!pendingKinds.contains(requestedKind)) {
            throw new BadRequestException(
                    "The selected protected action is no longer pending. Refresh the conversation before confirming.");
        }
        return command.getAction() == ChatConfirmationCommandDto.Action.CONFIRM
                ? ConfirmationDecision.confirmed(requestedKind)
                : ConfirmationDecision.cancelled(requestedKind);
    }

    private EnumSet<ConfirmationKind> pendingProtectedKinds(Long userId, String sessionId) {
        EnumSet<ConfirmationKind> kinds = EnumSet.noneOf(ConfirmationKind.class);
        destructiveActionGuard.pendingContext(userId, sessionId).ifPresent(pending ->
                kinds.add("reset_default_templates".equals(pending.toolName())
                        ? ConfirmationKind.DEFAULT_TEMPLATE_RESET
                        : ConfirmationKind.DESTRUCTIVE));
        if (scenarioDraftStore.pendingApplication(userId, sessionId).isPresent()) {
            kinds.add(ConfirmationKind.SCENE_REPLACEMENT);
        }
        return kinds;
    }

    private static ChatConfirmationCommandDto.Kind toCommandKind(ConfirmationKind kind) {
        return switch (kind) {
            case DESTRUCTIVE -> ChatConfirmationCommandDto.Kind.DESTRUCTIVE;
            case DEFAULT_TEMPLATE_RESET -> ChatConfirmationCommandDto.Kind.DEFAULT_TEMPLATE_RESET;
            case SCENE_REPLACEMENT -> ChatConfirmationCommandDto.Kind.SCENE_REPLACEMENT;
            case CHOICE -> throw new IllegalArgumentException("Non-destructive choices are not protected confirmations");
        };
    }

    private boolean synchronizeExecutionStop(Long userId,
                                             String sessionId,
                                             ActiveStreamRequest activeRequest,
                                             AtomicBoolean isDisconnect,
                                             AtomicBoolean isUserStop,
                                             boolean forcePoll) {
        if (isDisconnect.get()) return true;
        if (Thread.currentThread().isInterrupted()) {
            isDisconnect.set(true);
            activeRequest.requestControl().cancel();
            return true;
        }
        long nowNanos = System.nanoTime();
        long nextPoll = activeRequest.nextControlPollNanos().get();
        if (!forcePoll && (nowNanos < nextPoll || !activeRequest.nextControlPollNanos().compareAndSet(
                nextPoll, nowNanos + EXECUTION_CONTROL_POLL_NANOS))) {
            return isDisconnect.get();
        }
        if (forcePoll) {
            activeRequest.nextControlPollNanos().set(nowNanos + EXECUTION_CONTROL_POLL_NANOS);
        }
        try {
            ChatSessionPo session = sessionRepo.findByIdAndUserId(sessionId, userId).orElse(null);
            LocalDateTime now = databaseNow();
            boolean sameExecution = session != null
                    && Objects.equals(session.getActiveExecutionId(), activeRequest.requestId());
            if (!sameExecution) {
                isDisconnect.set(true);
                return true;
            }
            if (!hasActiveExecutionLease(session, now)) {
                log.warn("Chat execution lease expired before its heartbeat renewed it: sessionId={}, executionId={}",
                        sessionId, activeRequest.requestId());
                isDisconnect.set(true);
                return true;
            }
            if (Boolean.TRUE.equals(session.getExecutionStopRequested())) {
                if (Boolean.TRUE.equals(session.getExecutionUserStopRequested())) {
                    isUserStop.set(true);
                }
                isDisconnect.set(true);
            }
        } catch (RuntimeException e) {
            if (activeRequest.leaseConfirmation().isUnconfirmedFor(executionLeaseTtl())) {
                isDisconnect.set(true);
                activeRequest.requestControl().cancel();
                log.warn("Stopped local chat execution after its lease could not be confirmed for a full TTL: "
                                + "sessionId={}, executionId={}",
                        sessionId, activeRequest.requestId());
            } else {
                log.warn("Could not poll distributed chat execution control for session {}: {}",
                        sessionId, e.toString());
            }
        }
        return isDisconnect.get();
    }

    private String requireTurnId(String turnId) {
        if (turnId == null || turnId.isBlank()) {
            throw new BadRequestException("Turn id is required");
        }
        String effectiveTurnId = turnId.trim();
        if (effectiveTurnId.length() > 64) {
            throw new BadRequestException("Turn id must not exceed 64 characters");
        }
        return effectiveTurnId;
    }

    private String requireTurnContent(String content) {
        if (content == null || content.isBlank()) {
            throw new BadRequestException("Content is required");
        }
        if (content.length() > RequestLimits.MAX_CHAT_CONTENT_LENGTH) {
            throw new BadRequestException("Content must not exceed 10000 characters");
        }
        return content;
    }

    private String titleFromContent(String content) {
        String newTitle = content.length() > 12 ? content.substring(0, 12) + "..." : content;
        return newTitle.replace("\n", " ").trim();
    }

    private void touchSessionTitle(String sessionId, Long userId, String content) {
        sessionRepo.findByIdAndUserId(
                Objects.requireNonNull(sessionId, "sessionId must not be null"), userId).ifPresent(session -> {
            session.setUpdatedAt(databaseNow());
            if (isUntitledSessionTitle(session.getTitle())) {
                session.setTitle(titleFromContent(content));
            }
            sessionRepo.save(session);
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
                userId, sessionId, messages, tools, commandSet, emitter, isDisconnect,
                false, null, null, isDisconnect::get, isDisconnect::get);
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
                preferChinese, null, null, isDisconnect::get, isDisconnect::get);
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
        return executeToolLoop(
                userId, sessionId, messages, tools, commandSet, emitter, isDisconnect,
                preferChinese, executionTrace, null, isDisconnect::get, isDisconnect::get);
    }

    private ToolLoopResult executeToolLoop(Long userId,
                                           String sessionId,
                                           List<LlmMessage> messages,
                                           List<LlmToolSpec> tools,
                                           Set<StreamResponseDto.CommandDto> commandSet,
                                           SseEmitter emitter,
                                           AtomicBoolean isDisconnect,
                                           boolean preferChinese,
                                           List<StreamResponseDto.ProgressDto> executionTrace,
                                           String executionId,
                                           BooleanSupplier shouldStop,
                                           BooleanSupplier forceStopCheck) {
        boolean hadToolCalls = false;
        int successfulToolCalls = 0;
        int failedToolCalls = 0;
        int resultUnavailableToolCalls = 0;
        int uncertainMutationCalls = 0;
        boolean confirmationPending = false;
        boolean partialObjectiveResult = false;
        String previousRoundFingerprint = null;
        int stagnantRoundCount = 0;

        for (int round = 0; round < chatExecutionConfig.getMaxToolRounds(); round++) {
            if (forceStopCheck.getAsBoolean()) {
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
            if (forceStopCheck.getAsBoolean()) {
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
                ToolLoopStopReason stopReason = partialObjectiveResult
                        ? ToolLoopStopReason.PARTIAL_RESULT
                        : ToolLoopStopReason.COMPLETED;
                return new ToolLoopResult(hadToolCalls, stopReason, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }
            if (toolCalls.size() > chatExecutionConfig.getMaxToolCallsPerRound()) {
                log.warn("LLM requested too many tools in one round: count={}, limit={}",
                        toolCalls.size(), chatExecutionConfig.getMaxToolCallsPerRound());
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.EMERGENCY_LIMIT,
                        successfulToolCalls, failedToolCalls, resultUnavailableToolCalls,
                        uncertainMutationCalls, confirmationPending);
            }

            String reasoningSource = response.reasoningSummary().isBlank()
                    ? response.text()
                    : response.reasoningSummary();
            String reasoningSummary = compactReasoningProgressDetail(reasoningSource);
            if (reasoningSummary != null && !reasoningSummary.isBlank()
                    && !sendSseProgress(emitter, "REASONING", null, round + 1,
                    null, currentResult, reasoningSummary, executionTrace)) {
                isDisconnect.set(true);
                return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                        failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                        confirmationPending);
            }

            hadToolCalls = true;
            executeOwnedSessionWrite(userId, sessionId, executionId, () ->
                    saveAiToolCallRequest(sessionId, toolCalls));
            messages.add(LlmMessage.assistantToolCalls(toolCalls));
            StringBuilder roundFingerprint = new StringBuilder();

            for (int toolCallIndex = 0; toolCallIndex < toolCalls.size(); toolCallIndex++) {
                LlmToolCall toolCall = toolCalls.get(toolCallIndex);
                if (forceStopCheck.getAsBoolean()) {
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
                boolean stoppedAfterTool = false;
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
                    stoppedAfterTool = forceStopCheck.getAsBoolean();
                    executionOutcome = classifyToolExecution(functionName, toolResult);
                    if ("recommend_scenario".equals(functionName)) {
                        partialObjectiveResult = executionOutcome == ToolExecutionOutcome.PARTIAL;
                    }
                    if (executionOutcome == ToolExecutionOutcome.USABLE
                            || (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE
                                && mutationMayHaveCommitted(toolResult))) {
                        collectRefreshCommand(functionName, commandSet);
                    }
                }

                boolean requiresConfirmation = requiresUserConfirmation(toolResult);
                if (requiresConfirmation) {
                    confirmationPending = true;
                } else if (executionOutcome == ToolExecutionOutcome.USABLE
                        || executionOutcome == ToolExecutionOutcome.PARTIAL) {
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
                executeOwnedSessionWrite(userId, sessionId, executionId, () ->
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
                boolean progressSent = sendSseProgress(emitter, "TOOL_RESULT", functionName, round + 1,
                        progressOutcome, currentResult,
                        toolProgressDetail(functionName, toolResult, preferChinese), executionTrace);
                if (!progressSent) {
                    isDisconnect.set(true);
                }
                if (stoppedAfterTool || forceStopCheck.getAsBoolean()) {
                    log.info("Chat execution stopped after persisting tool result for session {}", sessionId);
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                            confirmationPending, requiresConfirmation ? functionName : null,
                            requiresConfirmation ? toolResult : null);
                }
                if (!progressSent) {
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.DISCONNECTED, successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls,
                            confirmationPending);
                }
                if (requiresConfirmation) {
                    appendSkippedToolResults(userId, sessionId, executionId, messages, toolCalls,
                            toolCallIndex + 1,
                            "PRIOR_CONFIRMATION_REQUIRED",
                            "Tool call was not executed because an earlier call in the same planning response "
                                    + "requires user confirmation.");
                    return new ToolLoopResult(hadToolCalls, ToolLoopStopReason.CONFIRMATION_REQUIRED,
                            successfulToolCalls,
                            failedToolCalls, resultUnavailableToolCalls, uncertainMutationCalls, true,
                            functionName, toolResult);
                }
                if (executionOutcome == ToolExecutionOutcome.RESULT_UNAVAILABLE) {
                    appendSkippedToolResults(userId, sessionId, executionId, messages, toolCalls,
                            toolCallIndex + 1,
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
                                          String executionId,
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
            executeOwnedSessionWrite(userId, sessionId, executionId, () ->
                    saveToolExecutionResult(sessionId, toolCallId, skippedResult));
            messages.add(LlmMessage.tool(toolCallId, skippedResult));
        }
    }

    private ReplyGuardOutcome streamGuardedAssistantReply(
            List<LlmMessage> messages,
            StringBuilder finalAnswer,
            SseEmitter emitter,
            AtomicBoolean isDisconnect,
            BooleanSupplier shouldStop,
            boolean preferChinese,
            List<StreamResponseDto.ProgressDto> executionTrace) {
        StringBuilder pending = new StringBuilder();
        AtomicReference<ReplyGuardOutcome> guardOutcome =
                new AtomicReference<>(ReplyGuardOutcome.NONE);
        BooleanSupplier replyShouldStop = () -> shouldStop.getAsBoolean()
                || isDisconnect.get()
                || guardOutcome.get() == ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE;
        llmChatService.streamReply(messages, delta -> {
            if (replyShouldStop.getAsBoolean() || delta == null || delta.isEmpty()) return;
            pending.append(delta);
            int boundary;
            while (guardOutcome.get() != ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE
                    && (boundary = firstReplySegmentBoundary(pending)) >= 0) {
                String segment = pending.substring(0, boundary + 1);
                pending.delete(0, boundary + 1);
                sendGuardedReplySegment(segment, finalAnswer, emitter, isDisconnect, guardOutcome,
                        preferChinese, executionTrace);
            }
        }, replyShouldStop);
        if (!replyShouldStop.getAsBoolean() && !pending.isEmpty()) {
            sendGuardedReplySegment(pending.toString(), finalAnswer, emitter, isDisconnect, guardOutcome,
                    preferChinese, executionTrace);
        }
        return guardOutcome.get();
    }

    private int firstReplySegmentBoundary(CharSequence text) {
        boolean[] literalCharacters = literalCharacterMask(text, true);
        for (int index = 0; index < text.length(); index++) {
            if (!literalCharacters[index]
                    && ".!?。！？".indexOf(text.charAt(index)) >= 0) return index;
        }
        return -1;
    }

    private void sendGuardedReplySegment(String segment,
                                         StringBuilder finalAnswer,
                                         SseEmitter emitter,
                                         AtomicBoolean isDisconnect,
                                         AtomicReference<ReplyGuardOutcome> guardOutcome,
                                         boolean preferChinese,
                                         List<StreamResponseDto.ProgressDto> executionTrace) {
        GuardedClaimReplacement replacement = containsUnsupportedPlatformClaim(segment)
                ? authoritativeClaimReplacement(preferChinese, executionTrace)
                : new GuardedClaimReplacement(segment, ReplyGuardOutcome.NONE);
        String visible = replacement.content();
        if (sendSseChunk(emitter, visible)) {
            finalAnswer.append(visible);
            guardOutcome.updateAndGet(current -> mergeReplyGuardOutcome(
                    current, replacement.outcome()));
        } else {
            log.info("SSE connection interrupted, stopping AI response");
            isDisconnect.set(true);
        }
    }

    private ReplyGuardOutcome mergeReplyGuardOutcome(
            ReplyGuardOutcome current, ReplyGuardOutcome next) {
        if (current == ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE
                || next == ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE) {
            return ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE;
        }
        if (current == ReplyGuardOutcome.REPLACED_WITH_AUTHORITATIVE_EVIDENCE
                || next == ReplyGuardOutcome.REPLACED_WITH_AUTHORITATIVE_EVIDENCE) {
            return ReplyGuardOutcome.REPLACED_WITH_AUTHORITATIVE_EVIDENCE;
        }
        return ReplyGuardOutcome.NONE;
    }

    static boolean containsUnsupportedPlatformClaim(String reply) {
        if (reply == null || reply.isBlank()) return false;
        String checkableReply = maskLiteralContent(reply);
        if (hasUnsupportedClaim(checkableReply, UNSUPPORTED_TOOL_EVIDENCE_CLAIM, false, false)) return true;
        if (hasUnsupportedClaim(checkableReply, UNSUPPORTED_PLATFORM_READ_CLAIM, false, true)) return true;
        return hasUnsupportedClaim(checkableReply, UNSUPPORTED_PLATFORM_MUTATION_CLAIM, true, false);
    }

    private static String maskLiteralContent(String text) {
        boolean[] literalCharacters = literalCharacterMask(text, false);
        char[] checkable = text.toCharArray();
        for (int index = 0; index < checkable.length; index++) {
            if (literalCharacters[index]) checkable[index] = ' ';
        }
        return new String(checkable);
    }

    private static boolean[] literalCharacterMask(CharSequence text, boolean maskUnclosedLiteral) {
        boolean[] masked = new boolean[text.length()];
        int literalStart = -1;
        char quoteEnd = 0;
        char codeDelimiter = 0;
        int codeDelimiterLength = 0;
        boolean fencedCode = false;
        for (int index = 0; index < text.length(); index++) {
            char current = text.charAt(index);
            if (codeDelimiterLength > 0) {
                if (current != codeDelimiter) {
                    masked[index] = true;
                    continue;
                }
                int runLength = delimiterRunLength(text, index, codeDelimiter);
                markLiteralRun(masked, index, runLength);
                boolean closes = fencedCode
                        ? runLength >= codeDelimiterLength
                            && isFenceDelimiterLine(text, index, runLength, true)
                        : runLength == codeDelimiterLength;
                if (closes) {
                    literalStart = -1;
                    codeDelimiter = 0;
                    codeDelimiterLength = 0;
                    fencedCode = false;
                }
                index += runLength - 1;
                continue;
            }
            if (quoteEnd != 0) {
                masked[index] = true;
                if (current == quoteEnd && !isEscaped(text, index)
                        && (quoteEnd != '\'' || isAsciiSingleQuoteClosing(text, index))) {
                    literalStart = -1;
                    quoteEnd = 0;
                }
                continue;
            }
            if (current == '`') {
                int runLength = delimiterRunLength(text, index, current);
                markLiteralRun(masked, index, runLength);
                literalStart = index;
                codeDelimiter = current;
                codeDelimiterLength = runLength;
                fencedCode = runLength >= 3 && isFenceDelimiterLine(text, index, runLength, false);
                index += runLength - 1;
                continue;
            }
            if (current == '~') {
                int runLength = delimiterRunLength(text, index, current);
                if (runLength >= 3 && isFenceDelimiterLine(text, index, runLength, false)) {
                    markLiteralRun(masked, index, runLength);
                    literalStart = index;
                    codeDelimiter = current;
                    codeDelimiterLength = runLength;
                    fencedCode = true;
                    index += runLength - 1;
                    continue;
                }
            }
            char matchingQuote = matchingQuote(current);
            if (matchingQuote != 0 && !isEscaped(text, index)
                    && (current != '\'' || isAsciiSingleQuoteOpening(text, index))) {
                masked[index] = true;
                literalStart = index;
                quoteEnd = matchingQuote;
            }
        }
        if (!maskUnclosedLiteral && literalStart >= 0) {
            Arrays.fill(masked, literalStart, masked.length, false);
        }
        return masked;
    }

    private static int delimiterRunLength(CharSequence text, int start, char delimiter) {
        int end = start;
        while (end < text.length() && text.charAt(end) == delimiter) end++;
        return end - start;
    }

    private static boolean isFenceDelimiterLine(
            CharSequence text, int delimiterStart, int delimiterLength, boolean closing) {
        int lineStart = delimiterStart;
        while (lineStart > 0
                && text.charAt(lineStart - 1) != '\n'
                && text.charAt(lineStart - 1) != '\r') {
            lineStart--;
        }
        if (delimiterStart - lineStart > 3) return false;
        for (int index = lineStart; index < delimiterStart; index++) {
            if (text.charAt(index) != ' ') return false;
        }
        if (!closing) return true;
        for (int index = delimiterStart + delimiterLength; index < text.length(); index++) {
            char current = text.charAt(index);
            if (current == '\n' || current == '\r') return true;
            if (!Character.isWhitespace(current)) return false;
        }
        return true;
    }

    private static void markLiteralRun(boolean[] masked, int start, int length) {
        for (int index = start; index < start + length; index++) masked[index] = true;
    }

    private static char matchingQuote(char opening) {
        return switch (opening) {
            case '"' -> '"';
            case '\'' -> '\'';
            case '“' -> '”';
            case '‘' -> '’';
            case '「' -> '」';
            case '『' -> '』';
            case '«' -> '»';
            case '‹' -> '›';
            default -> 0;
        };
    }

    private static boolean isAsciiSingleQuoteOpening(CharSequence text, int index) {
        if (index + 1 >= text.length() || Character.isWhitespace(text.charAt(index + 1))) {
            return false;
        }
        return index == 0 || !isWordCharacter(text.charAt(index - 1));
    }

    private static boolean isAsciiSingleQuoteClosing(CharSequence text, int index) {
        if (index == 0 || Character.isWhitespace(text.charAt(index - 1))) return false;
        return index + 1 >= text.length() || !isWordCharacter(text.charAt(index + 1));
    }

    private static boolean isWordCharacter(char value) {
        return Character.isLetterOrDigit(value) || value == '_';
    }

    private static boolean isEscaped(CharSequence text, int index) {
        int backslashes = 0;
        for (int cursor = index - 1; cursor >= 0 && text.charAt(cursor) == '\\'; cursor--) {
            backslashes++;
        }
        return backslashes % 2 == 1;
    }

    private static boolean hasUnsupportedClaim(
            String reply,
            Pattern pattern,
            boolean allowNonOperationalContent,
            boolean leadingHistoryOverridesCurrentContext) {
        Matcher matcher = pattern.matcher(reply);
        while (matcher.find()) {
            String claimClause = claimClause(reply, matcher.start(), matcher.end());
            String trimmedClause = claimClause.trim();
            boolean leadingHistoricalContext = hasLeadingHistoricalClaimContext(reply, matcher.start());
            if (trimmedClause.endsWith("?") || trimmedClause.endsWith("？")
                    || NON_ASSERTIVE_CLAIM_CONTEXT.matcher(claimClause).find()
                    || (leadingHistoryOverridesCurrentContext && leadingHistoricalContext)
                    || ((HISTORICAL_CLAIM_CONTEXT.matcher(claimClause).find()
                            || leadingHistoricalContext)
                        && !CURRENT_CLAIM_CONTEXT.matcher(claimClause).find())) continue;
            if (allowNonOperationalContent
                    && NON_OPERATIONAL_PLATFORM_CONTENT.matcher(matcher.group()).find()) continue;
            return true;
        }
        return false;
    }

    private static boolean hasLeadingHistoricalClaimContext(String reply, int claimStart) {
        int sentenceStart = 0;
        for (int index = Math.min(claimStart, reply.length()) - 1; index >= 0; index--) {
            if (".!?。！？".indexOf(reply.charAt(index)) >= 0) {
                sentenceStart = index + 1;
                break;
            }
        }
        return LEADING_HISTORICAL_CLAIM_CONTEXT
                .matcher(reply.substring(sentenceStart, Math.max(sentenceStart, claimStart)))
                .matches();
    }

    private static String claimClause(String reply, int claimStart, int claimEnd) {
        int clauseStart = 0;
        int clauseEnd = reply.length();
        Matcher boundary = CLAIM_CLAUSE_BOUNDARY.matcher(reply);
        while (boundary.find()) {
            if (boundary.end() <= claimStart) {
                clauseStart = boundary.end();
            } else if (boundary.start() >= claimEnd) {
                clauseEnd = boundary.start();
                break;
            }
        }
        return reply.substring(clauseStart, clauseEnd);
    }

    private GuardedClaimReplacement authoritativeClaimReplacement(
            boolean preferChinese, List<StreamResponseDto.ProgressDto> executionTrace) {
        List<String> authoritativeDetails = executionTrace == null ? List.of() : executionTrace.stream()
                .filter(progress -> progress != null
                        && "TOOL_RESULT".equals(progress.getStage())
                        && "USABLE".equals(progress.getOutcome())
                        && progress.getDetail() != null
                        && !progress.getDetail().isBlank())
                .map(StreamResponseDto.ProgressDto::getDetail)
                .distinct()
                .limit(4)
                .toList();
        if (!authoritativeDetails.isEmpty()) {
            return new GuardedClaimReplacement(preferChinese
                    ? "系统已用权威工具记录替换一段未经证据支持的模型说法："
                        + String.join("；", authoritativeDetails)
                    : "The system replaced an unsupported model claim with the authoritative tool record: "
                        + String.join("; ", authoritativeDetails),
                    ReplyGuardOutcome.REPLACED_WITH_AUTHORITATIVE_EVIDENCE);
        }
        return new GuardedClaimReplacement(preferChinese
                ? "系统已隐藏一段声称读取或修改当前画布的未验证回复。"
                    + "本轮没有支持该说法的完整权威工具结果；请重试，并在看到明确的成功记录前不要假定数据已经改变。"
                : "The system hid an unverified reply that claimed to read or change the current Board. "
                    + "This turn has no complete authoritative tool result supporting that claim; retry, and "
                    + "do not assume data changed until an explicit successful record is shown.",
                ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE);
    }

    private ToolExecutionOutcome classifyToolExecution(String functionName, String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return ToolExecutionOutcome.FAILED;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            if (!root.isObject() || root.isEmpty() || !hasValidToolResultControlFields(root)) {
                return ToolExecutionOutcome.FAILED;
            }
            if (root.path("requiresUserConfirmation").asBoolean(false)) {
                return ToolExecutionOutcome.FAILED;
            }
            if ((root.has("resultAvailable") && !root.path("resultAvailable").asBoolean(true))
                    || "RESULT_UNAVAILABLE".equals(root.path("resultStatus").asText())) {
                return ToolExecutionOutcome.RESULT_UNAVAILABLE;
            }
            String error = root.path("error").asText("");
            String errorCode = root.path("errorCode").asText("");
            if (!error.isBlank() || !errorCode.isBlank()
                    || (root.has("status") && root.path("status").intValue() >= 400)) {
                return ToolExecutionOutcome.FAILED;
            }
            if (!hasValidKnownToolPayload(functionName, root)) {
                return ToolExecutionOutcome.FAILED;
            }
            if ("PARTIAL".equals(root.path("objectiveStatus").asText())) {
                return ToolExecutionOutcome.PARTIAL;
            }
            boolean hasSemanticPayload = root.properties().stream()
                    .anyMatch(entry -> !TOOL_RESULT_CONTROL_FIELDS.contains(entry.getKey()));
            return hasSemanticPayload ? ToolExecutionOutcome.USABLE : ToolExecutionOutcome.FAILED;
        } catch (Exception ignore) {
            return ToolExecutionOutcome.FAILED;
        }
    }

    private boolean hasValidKnownToolPayload(String functionName, JsonNode root) {
        if (!"board_overview".equals(functionName)) return true;
        return hasArray(root, "devices")
                && hasArray(root, "rules")
                && hasArray(root, "specs")
                && hasArray(root, "edges")
                && hasArray(root, "environmentVariables");
    }

    private boolean hasArray(JsonNode root, String field) {
        return root != null && root.has(field) && root.get(field).isArray();
    }

    private boolean hasValidToolResultControlFields(JsonNode root) {
        if (!isOptionalToolResultText(root, "error")
                || !isOptionalToolResultText(root, "errorCode")
                || !isOptionalToolResultBoolean(root, "requiresUserConfirmation")
                || !isOptionalToolResultBoolean(root, "resultAvailable")
                || !isOptionalToolResultBoolean(root, "mutationMayHaveCommitted")) {
            return false;
        }
        if (root.has("status") && (!root.get("status").isIntegralNumber()
                || !root.get("status").canConvertToInt()
                || root.get("status").intValue() < 100
                || root.get("status").intValue() > 599)) {
            return false;
        }
        if (root.has("resultStatus") && (!root.get("resultStatus").isTextual()
                || !"RESULT_UNAVAILABLE".equals(root.get("resultStatus").textValue()))) {
            return false;
        }
        return !root.has("objectiveStatus")
                || (root.get("objectiveStatus").isTextual()
                    && Set.of("COMPLETE", "PARTIAL").contains(root.get("objectiveStatus").textValue()));
    }

    private boolean isOptionalToolResultText(JsonNode root, String field) {
        return !root.has(field) || root.get(field).isTextual();
    }

    private boolean isOptionalToolResultBoolean(JsonNode root, String field) {
        return !root.has(field) || root.get(field).isBoolean();
    }

    private boolean mutationMayHaveCommitted(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return false;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            JsonNode value = root != null && root.isObject()
                    ? root.get("mutationMayHaveCommitted") : null;
            return value != null && value.isBoolean() && value.booleanValue();
        } catch (Exception ignore) {
            return false;
        }
    }

    private boolean sendFrontendCommands(SseEmitter emitter, Set<StreamResponseDto.CommandDto> commandSet) {
        for (StreamResponseDto.CommandDto cmd : commandSet) {
            try {
                StreamResponseDto packet = StreamResponseDto.command(cmd);
                emitter.send(SseEmitter.event().data(packet, MediaType.APPLICATION_JSON));
                log.info("Sent frontend command: type={}, payload={}", cmd.getType(), cmd.getPayload());
            } catch (IOException | IllegalStateException e) {
                log.warn("Failed to send command", e);
                return false;
            }
        }
        return true;
    }

    private boolean sendSseTerminal(
            SseEmitter emitter, String turnId, ChatExecutionStatus executionStatus) {
        try {
            emitter.send(SseEmitter.event().data(
                    StreamResponseDto.terminal(turnId, executionStatus),
                    MediaType.APPLICATION_JSON));
            return true;
        } catch (IOException | IllegalStateException e) {
            log.debug("Failed to send chat terminal frame for turn {}: {}", turnId, e.toString());
            return false;
        }
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
        if (executionTrace != null && packet.getProgress() != null) {
            executionTrace.add(packet.getProgress());
        }
        try {
            emitter.send(SseEmitter.event()
                    .data(packet, MediaType.APPLICATION_JSON));
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
                if (!hasValidKnownToolPayload(functionName, root)) return null;
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
        if (result == null) {
            return "";
        }
        if (!result.hadToolCalls()) {
            return preferChinese
                    ? "系统状态：本轮未执行平台工具，因此回复不代表已读取当前画布数据或已完成平台操作。\n\n"
                    : "System status: no platform tool ran in this turn, so the response does not confirm current Board data or a completed platform operation.\n\n";
        }
        List<String> notices = new ArrayList<>();
        if (result.stopReason() == ToolLoopStopReason.PARTIAL_RESULT) {
            notices.add(preferChinese
                    ? "工具返回了可审阅但不完整的场景草案；缺少的核心场景部分未被视为已完成。"
                    : "The tool returned a reviewable but incomplete scene draft; missing core scene parts were not treated as completed.");
        }
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

    private void saveUserTurn(String sid, String turnId, String executionId, String content) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("user");
        po.setContent(content);
        po.setTurnId(turnId);
        po.setExecutionId(executionId);
        messageRepo.saveAndFlush(po);
    }

    private void saveAssistantMsg(String sid,
                                  String turnId,
                                  String content,
                                  List<StreamResponseDto.ProgressDto> executionTrace,
                                  Integer elapsedSeconds,
                                  ChatExecutionStatus executionStatus) {
        ChatMessagePo po = new ChatMessagePo();
        po.setSessionId(sid);
        po.setRole("assistant");
        po.setContent(content);
        po.setTurnId(turnId);
        po.setExecutionId(UserContextHolder.getChatExecutionId());
        po.setExecutionElapsedSeconds(elapsedSeconds);
        po.setExecutionStatus(executionStatus);
        if (executionStatus == ChatExecutionStatus.COMPLETED
                && !hasCompletedToolEvidence(executionTrace)) {
            throw new IllegalStateException(
                    "A completed chat terminal record requires persisted successful tool evidence");
        }
        if (executionTrace != null && !executionTrace.isEmpty()) {
            try {
                po.setExecutionTraceJson(objectMapper.writeValueAsString(executionTrace));
            } catch (Exception e) {
                throw new IllegalStateException(
                        "Could not serialize the chat execution trace for terminal persistence", e);
            }
        }
        messageRepo.saveAndFlush(po);
    }

    private TerminalPersistenceResult persistAssistantTerminal(
            Long userId,
            String sessionId,
            String executionId,
            String turnId,
            String content,
            List<StreamResponseDto.ProgressDto> executionTrace,
            Integer elapsedSeconds,
            ChatExecutionStatus executionStatus,
            String userStoppedContent) {
        AtomicReference<ChatExecutionStatus> persistedStatus = new AtomicReference<>();
        try {
            transactionTemplate.executeWithoutResult(status -> {
                ChatSessionPo session = requireOwnedSessionForWrite(userId, sessionId, executionId);
                boolean explicitlyStopped = Boolean.TRUE.equals(session.getExecutionStopRequested())
                        && Boolean.TRUE.equals(session.getExecutionUserStopRequested());
                ChatExecutionStatus authoritativeStatus = explicitlyStopped
                        ? ChatExecutionStatus.STOPPED
                        : executionStatus;
                String authoritativeContent = explicitlyStopped ? userStoppedContent : content;
                saveAssistantMsg(
                        sessionId,
                        turnId,
                        authoritativeContent,
                        executionTrace,
                        elapsedSeconds,
                        authoritativeStatus);
                persistedStatus.set(authoritativeStatus);
            });
            if (persistedStatus.get() == null) {
                throw new IllegalStateException("Terminal transaction completed without a status.");
            }
            return new TerminalPersistenceResult(true, persistedStatus.get());
        } catch (RuntimeException e) {
            log.warn("Could not persist {} chat terminal record for session {}: {}",
                    executionStatus, sessionId, e.toString());
            return new TerminalPersistenceResult(false, executionStatus);
        }
    }

    private int elapsedSeconds(long executionStartedNanos) {
        return (int) Math.min(
                Integer.MAX_VALUE,
                Math.max(0L, (System.nanoTime() - executionStartedNanos) / 1_000_000_000L));
    }

    private String terminalPersistenceFailureMessage(boolean preferChinese) {
        return preferChinese
                ? "最终回复未能写入会话历史，本轮记录不完整。请先刷新会话历史和当前画布状态，再决定是否重试。"
                : "The final response could not be saved to conversation history, so this turn is incomplete. "
                    + "Refresh the conversation history and current Board state before deciding whether to retry.";
    }

    private String terminalPersistenceFailureSuffix(boolean preferChinese) {
        return preferChinese
                ? " 最终错误记录也未能写入会话历史；请刷新会话历史和当前画布状态后再重试。"
                : " The terminal error record also could not be saved to conversation history; "
                    + "refresh the conversation history and current Board state before retrying.";
    }

    private ChatExecutionStatus terminalStatus(
            ToolLoopResult result, ReplyGuardOutcome replyGuardOutcome) {
        if (result == null) return ChatExecutionStatus.FAILED;
        if (result.confirmationPending()) return ChatExecutionStatus.AWAITING_CONFIRMATION;
        if (result.resultUnavailableToolCalls() > 0) return ChatExecutionStatus.PARTIAL;
        if (result.failedToolCalls() > 0) {
            return result.successfulToolCalls() > 0
                    ? ChatExecutionStatus.PARTIAL
                    : ChatExecutionStatus.FAILED;
        }
        if (result.stopReason() == ToolLoopStopReason.NO_PROGRESS
                || result.stopReason() == ToolLoopStopReason.EMERGENCY_LIMIT) {
            return result.hadToolCalls() ? ChatExecutionStatus.PARTIAL : ChatExecutionStatus.FAILED;
        }
        if (result.stopReason() == ToolLoopStopReason.PROVIDER_UNAVAILABLE) {
            return result.successfulToolCalls() > 0
                    ? ChatExecutionStatus.PARTIAL
                    : ChatExecutionStatus.FAILED;
        }
        if (result.stopReason() == ToolLoopStopReason.PARTIAL_RESULT) {
            return ChatExecutionStatus.PARTIAL;
        }
        ChatExecutionStatus status = result.hadToolCalls()
                ? ChatExecutionStatus.COMPLETED
                : ChatExecutionStatus.PARTIAL;
        return replyGuardOutcome == ReplyGuardOutcome.HIDDEN_WITHOUT_EVIDENCE
                && status == ChatExecutionStatus.COMPLETED
                ? ChatExecutionStatus.PARTIAL : status;
    }

    private String interruptedAuditNotice(ToolLoopResult result, boolean preferChinese, boolean userStopped) {
        String opening;
        if (preferChinese) {
            opening = userStopped ? "用户已停止本次 AI 回复。" : "连接在任务完成前中断。";
        } else {
            opening = userStopped ? "The user stopped this AI response." : "The connection ended before the task completed.";
        }
        if (result != null && result.hadToolCalls()) {
            String priorStepPrefix = userStopped
                    ? (preferChinese ? "停止前有 " : " Before stopping, ")
                    : (preferChinese ? "中断前有 " : " Before the disconnect, ");
            return preferChinese
                    ? opening + priorStepPrefix + result.successfulToolCalls()
                        + " 个步骤返回可用结果、" + result.failedToolCalls() + " 个步骤失败、"
                        + result.resultUnavailableToolCalls()
                        + " 个步骤结果未确认。已开始的写入不会因停止或断线回滚，请以刷新后的画布和运行历史为准。"
                    : opening + priorStepPrefix
                        + result.successfulToolCalls() + " step(s) returned usable results, "
                        + result.failedToolCalls() + " failed, and "
                        + result.resultUnavailableToolCalls()
                        + " had unconfirmed results. Started writes are not rolled back by a stop or disconnect; "
                        + "rely on the refreshed Board and run history.";
        }
        return preferChinese
                ? opening + "未记录到已完成的工具步骤。需要时可以重新发起请求。"
                : opening + " No completed tool step was recorded. Start the request again if it is still needed.";
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

    private void executeOwnedSessionWrite(Long userId,
                                          String sessionId,
                                          String executionId,
                                          Runnable write) {
        transactionTemplate.executeWithoutResult(status -> {
            requireOwnedSessionForWrite(userId, sessionId, executionId);
            write.run();
        });
    }

    private ChatSessionPo requireOwnedSessionForWrite(
            Long userId, String sessionId, String executionId) {
        requireActiveUserForWrite(userId);
        String requiredSessionId = Objects.requireNonNull(sessionId, "sessionId must not be null");
        if (executionId == null || executionId.isBlank()) {
            return sessionRepo.findByIdAndUserId(requiredSessionId, userId)
                    .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        }
        ChatSessionPo session = sessionRepo.findByIdAndUserIdForUpdate(requiredSessionId, userId)
                .orElseThrow(() -> ResourceNotFoundException.session(sessionId));
        LocalDateTime now = databaseNow();
        if (!Objects.equals(executionId, session.getActiveExecutionId())
                || session.getActiveExecutionExpiresAt() == null
                || !session.getActiveExecutionExpiresAt().isAfter(now)) {
            throw new ConflictException(
                    "The assistant execution no longer owns this session. No new message was committed.");
        }
        return session;
    }

    private void requireActiveUserForWrite(Long userId) {
        if (userId == null || userRepository.findByIdForUpdate(userId).isEmpty()) {
            throw UnauthorizedException.invalidToken();
        }
    }

    private long requiredMessageCapacityForTurn() {
        long perRound = 1L + chatExecutionConfig.getMaxToolCallsPerRound();
        try {
            return Math.addExact(2L, Math.multiplyExact(
                    perRound, (long) chatExecutionConfig.getMaxToolRounds()));
        } catch (ArithmeticException e) {
            return Long.MAX_VALUE;
        }
    }

    private record ActiveStreamRequest(
            Long userId,
            String requestId,
            String turnId,
            String content,
            AtomicBoolean stopRequested,
            AtomicBoolean userStopRequested,
            AtomicReference<SseEmitter> emitter,
            AtomicLong nextControlPollNanos,
            LeaseConfirmation leaseConfirmation,
            LlmRequestControl requestControl) {

        private ActiveStreamRequest(
                Long userId,
                String requestId,
                String turnId,
                String content,
                long confirmationStartedNanos) {
            this(userId, requestId, turnId, content,
                    new AtomicBoolean(false), new AtomicBoolean(false),
                    new AtomicReference<>(),
                    new AtomicLong(System.nanoTime() + EXECUTION_CONTROL_POLL_NANOS),
                    new LeaseConfirmation(confirmationStartedNanos),
                    new LlmRequestControl());
        }

        private boolean matches(String candidateTurnId, String candidateContent) {
            return Objects.equals(turnId, candidateTurnId)
                    && Objects.equals(content, candidateContent);
        }
    }

    private record ExecutionLeaseState(
            String requestId,
            boolean stopRequested,
            boolean userStopRequested) {
    }

    private record ExecutionLeaseRenewalBatch(
            Map<String, ExecutionLeaseState> renewedLeases,
            long confirmationStartedNanos) {

        private static ExecutionLeaseRenewalBatch none() {
            return new ExecutionLeaseRenewalBatch(Map.of(), Long.MIN_VALUE);
        }
    }

    private List<ChatMessagePo> getSmartHistory(String sessionId, int limitCharCount) {
        List<ChatMessagePo> allMessages = new ArrayList<>(messageRepo.findTop80BySessionIdOrderByIdDesc(sessionId));
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

    private void attachPersistedExecutionTraces(List<ChatMessagePo> visibleMessages,
                                                 List<ChatMessageResponseDto> response) {
        if (visibleMessages == null || response == null
                || visibleMessages.size() != response.size()) {
            return;
        }

        for (int visibleIndex = 0; visibleIndex < visibleMessages.size(); visibleIndex++) {
            ChatMessagePo message = visibleMessages.get(visibleIndex);
            ChatMessageResponseDto dto = response.get(visibleIndex);
            if ("assistant".equalsIgnoreCase(message.getRole()) && dto != null) {
                List<StreamResponseDto.ProgressDto> persistedTrace = readPersistedExecutionTrace(message);
                if (persistedTrace != null) {
                    dto.setExecutionTrace(persistedTrace);
                    dto.setExecutionElapsedSeconds(message.getExecutionElapsedSeconds());
                }
                if (message.getExecutionStatus() == ChatExecutionStatus.COMPLETED
                        && !hasCompletedToolEvidence(persistedTrace)) {
                    dto.setExecutionStatus(null);
                    log.warn("Cleared unproven COMPLETED status for chat message {} because its persisted "
                            + "execution trace is missing, malformed, unpaired, or has no successful tool result",
                            message.getId());
                }
            }
        }
    }

    private List<StreamResponseDto.ProgressDto> readPersistedExecutionTrace(ChatMessagePo message) {
        String traceJson = message.getExecutionTraceJson();
        if (traceJson == null || traceJson.isBlank()) {
            return null;
        }
        try {
            JsonNode root = objectMapper.readTree(traceJson);
            if (!root.isArray() || root.isEmpty()) {
                throw new IllegalStateException("execution trace shape is invalid");
            }
            for (JsonNode progress : root) {
                if (!isValidPersistedProgress(progress)) {
                    throw new IllegalStateException("execution trace shape is invalid");
                }
            }
            List<StreamResponseDto.ProgressDto> trace = objectMapper.convertValue(
                    root, new TypeReference<List<StreamResponseDto.ProgressDto>>() { });
            return List.copyOf(trace);
        } catch (Exception e) {
            log.warn("Could not read persisted execution trace for message {}: {}",
                    message.getId(), e.toString());
            return null;
        }
    }

    private boolean isValidPersistedProgress(JsonNode progress) {
        if (progress == null || !progress.isObject()
                || progress.properties().stream()
                    .anyMatch(entry -> !PERSISTED_PROGRESS_FIELDS.contains(entry.getKey()))) {
            return false;
        }
        JsonNode stage = progress.get("stage");
        if (stage == null || !stage.isTextual() || !PERSISTED_PROGRESS_STAGES.contains(stage.textValue())
                || !isOptionalProgressText(progress, "toolName")
                || !isOptionalProgressText(progress, "detail")
                || !isOptionalProgressCounter(progress, "round")
                || !isOptionalProgressCounter(progress, "successfulSteps")
                || !isOptionalProgressCounter(progress, "failedSteps")
                || !isOptionalProgressCounter(progress, "unconfirmedSteps")) {
            return false;
        }
        JsonNode outcome = progress.get("outcome");
        if ("TOOL_RESULT".equals(stage.textValue())) {
            return outcome != null && outcome.isTextual()
                    && TOOL_RESULT_OUTCOMES.contains(outcome.textValue());
        }
        if ("EXECUTION_GUARD".equals(stage.textValue())) {
            return outcome != null && outcome.isTextual()
                    && EXECUTION_GUARD_OUTCOMES.contains(outcome.textValue());
        }
        return outcome == null || outcome.isNull();
    }

    private boolean isOptionalProgressText(JsonNode progress, String field) {
        JsonNode value = progress.get(field);
        return value == null || value.isNull() || value.isTextual();
    }

    private boolean isOptionalProgressCounter(JsonNode progress, String field) {
        JsonNode value = progress.get(field);
        return value == null || value.isNull()
                || (value.isIntegralNumber() && value.canConvertToInt() && value.intValue() >= 0);
    }

    private boolean hasCompletedToolEvidence(List<StreamResponseDto.ProgressDto> trace) {
        if (trace == null || trace.isEmpty()) {
            return false;
        }
        boolean hasUsableResult = false;
        StreamResponseDto.ProgressDto pendingExecution = null;
        Set<String> unresolvedPartialTools = new LinkedHashSet<>();
        for (StreamResponseDto.ProgressDto progress : trace) {
            if (progress == null) {
                return false;
            }
            if ("EXECUTION_GUARD".equals(progress.getStage())) {
                return false;
            }
            if ("TOOL_EXECUTION".equals(progress.getStage())) {
                if (pendingExecution != null
                        || progress.getToolName() == null || progress.getToolName().isBlank()
                        || progress.getRound() == null || progress.getRound() < 1) {
                    return false;
                }
                pendingExecution = progress;
                continue;
            }
            if ("TOOL_RESULT".equals(progress.getStage())) {
                if (pendingExecution == null
                        || !Objects.equals(pendingExecution.getToolName(), progress.getToolName())
                        || !Objects.equals(pendingExecution.getRound(), progress.getRound())) {
                    return false;
                }
                String toolName = pendingExecution.getToolName();
                pendingExecution = null;
                if ("USABLE".equals(progress.getOutcome())) {
                    unresolvedPartialTools.remove(toolName);
                    hasUsableResult = true;
                } else if ("PARTIAL".equals(progress.getOutcome())) {
                    unresolvedPartialTools.add(toolName);
                } else {
                    return false;
                }
            }
        }
        return hasUsableResult && pendingExecution == null && unresolvedPartialTools.isEmpty();
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

    private void sendSseErrorMessage(
            SseEmitter emitter, String msg, AtomicBoolean isDisconnect) {
        if (sendSseError(emitter, msg)) {
            completeEmitter(emitter, isDisconnect);
            return;
        }
        isDisconnect.set(true);
        try {
            emitter.completeWithError(new IllegalStateException(msg));
        } catch (IllegalStateException e) {
            log.debug("SSE emitter was already unusable while reporting a terminal error: {}", e.getMessage());
        }
    }

    private boolean sendSseError(SseEmitter emitter, String message) {
        try {
            emitter.send(SseEmitter.event()
                    .data(StreamResponseDto.error(message), MediaType.APPLICATION_JSON));
            return true;
        } catch (IOException | IllegalStateException e) {
            return false;
        }
    }

    private boolean requiresUserConfirmation(String toolResult) {
        if (toolResult == null || toolResult.isBlank()) {
            return false;
        }
        try {
            JsonNode root = objectMapper.readTree(toolResult);
            JsonNode value = root != null && root.isObject()
                    ? root.get("requiresUserConfirmation") : null;
            return value != null && value.isBoolean() && value.booleanValue();
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

    private void completeInterruptedEmitter(SseEmitter emitter) {
        try {
            emitter.complete();
        } catch (IllegalStateException e) {
            log.debug("SSE emitter was already unusable during interrupted completion: {}", e.getMessage());
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
        PARTIAL,
        FAILED,
        RESULT_UNAVAILABLE
    }

    private enum ReplyGuardOutcome {
        NONE,
        REPLACED_WITH_AUTHORITATIVE_EVIDENCE,
        HIDDEN_WITHOUT_EVIDENCE
    }

    private record GuardedClaimReplacement(String content, ReplyGuardOutcome outcome) {
    }

    private enum TerminalPersistenceState {
        NOT_ATTEMPTED,
        PERSISTED,
        FAILED
    }

    private record TerminalPersistenceResult(
            boolean persisted,
            ChatExecutionStatus executionStatus) {
    }

    private enum ToolLoopStopReason {
        COMPLETED,
        DISCONNECTED,
        PROVIDER_UNAVAILABLE,
        CONFIRMATION_REQUIRED,
        RESULT_UNAVAILABLE,
        PARTIAL_RESULT,
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
