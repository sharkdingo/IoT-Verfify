package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.AiTaskContinuationStore;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.AiScenarioDraftStore;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatHistoryPageDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ChatSessionBusyException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Captor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.transaction.TransactionStatus;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.data.domain.Pageable;

import java.lang.reflect.Method;
import java.time.LocalDateTime;
import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Optional;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.lenient;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ChatServiceImplHistoryWindowTest {

    @Mock
    private ChatSessionRepository sessionRepo;
    @Mock
    private ChatMessageRepository messageRepo;
    @Mock
    private UserRepository userRepository;
    @Mock
    private LlmChatService llmChatService;
    @Mock
    private AiToolManager aiToolManager;
    @Mock
    private AiDestructiveActionGuard destructiveActionGuard;
    @Mock
    private AiScenarioDraftStore scenarioDraftStore;
    @Mock
    private AiTaskContinuationStore taskContinuationStore;
    @Mock
    private ChatMapper chatMapper;
    @Mock
    private TransactionTemplate transactionTemplate;
    @Captor
    private ArgumentCaptor<List<ChatMessagePo>> chatMessageListCaptor;

    private ChatServiceImpl service;

    @BeforeEach
    void setUp() {
        lenient().doAnswer(invocation -> {
            Consumer<TransactionStatus> action = invocation.getArgument(0);
            action.accept(org.mockito.Mockito.mock(TransactionStatus.class));
            return null;
        }).when(transactionTemplate).executeWithoutResult(org.mockito.ArgumentMatchers.any());
        lenient().when(userRepository.findByIdForUpdate(1L))
                .thenReturn(Optional.of(UserPo.builder().id(1L).build()));
        lenient().when(sessionRepo.currentDatabaseTime()).thenAnswer(invocation -> LocalDateTime.now());
        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                userRepository,
                llmChatService,
                new LlmMessageCodec(new ObjectMapper()),
                new ChatConfirmationDetector(
                        org.mockito.Mockito.mock(cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService.class),
                        new ObjectMapper()),
                aiToolManager,
                destructiveActionGuard,
                scenarioDraftStore,
                taskContinuationStore,
                new ObjectMapper(),
                chatMapper,
                transactionTemplate,
                new ChatExecutionConfig()
        );
    }

    @SuppressWarnings("unchecked")
    @Test
    void getSmartHistory_shouldUseRecentWindowQuery() throws Exception {
        ChatMessagePo newest = new ChatMessagePo();
        newest.setRole("assistant");
        newest.setContent("reply");

        ChatMessagePo older = new ChatMessagePo();
        older.setRole("user");
        older.setContent("hello");

        // Repository returns DESC window.
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1"))
                .thenReturn(List.of(newest, older));

        Method method = ChatServiceImpl.class.getDeclaredMethod("getSmartHistory", String.class, int.class);
        method.setAccessible(true);

        List<ChatMessagePo> history = (List<ChatMessagePo>) method.invoke(service, "s1", 4000);

        assertEquals(2, history.size());
        verify(messageRepo).findTop80BySessionIdOrderByCreatedAtDesc("s1");
        verify(messageRepo, never()).findBySessionIdOrderByCreatedAtAsc("s1");
    }

    @SuppressWarnings("unchecked")
    @Test
    void getSmartHistory_shouldDropOrphanToolMessagesAtWindowBoundary() throws Exception {
        ChatMessagePo newestAssistant = new ChatMessagePo();
        newestAssistant.setRole("assistant");
        newestAssistant.setContent("final reply");

        ChatMessagePo orphanTool = new ChatMessagePo();
        orphanTool.setRole("tool");
        orphanTool.setContent("{\"type\":\"tool_result\",\"toolCallId\":\"tc_1\",\"result\":\"ok\"}");

        ChatMessagePo olderUser = new ChatMessagePo();
        olderUser.setRole("user");
        olderUser.setContent("hello");

        // Repository returns DESC window. The matching assistant tool_call is outside this window.
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s2"))
                .thenReturn(List.of(newestAssistant, orphanTool, olderUser));

        Method method = ChatServiceImpl.class.getDeclaredMethod("getSmartHistory", String.class, int.class);
        method.setAccessible(true);

        List<ChatMessagePo> history = (List<ChatMessagePo>) method.invoke(service, "s2", 4000);

        assertEquals(2, history.size());
        assertTrue(history.stream().noneMatch(m -> "tool".equalsIgnoreCase(m.getRole())));
    }

    @SuppressWarnings("unchecked")
    @Test
    void getSmartHistory_shouldDropIncompletePersistedToolCallBlock() throws Exception {
        ChatMessagePo finalReply = new ChatMessagePo();
        finalReply.setRole("assistant");
        finalReply.setContent("The previous response could not be completed.");

        ChatMessagePo oneOfTwoResults = new ChatMessagePo();
        oneOfTwoResults.setRole("tool");
        oneOfTwoResults.setContent("{\"type\":\"tool_result\",\"toolCallId\":\"tc_1\",\"result\":\"ok\"}");

        ChatMessagePo incompleteCalls = new ChatMessagePo();
        incompleteCalls.setRole("assistant");
        incompleteCalls.setContent("{\"type\":\"tool_calls\",\"toolCalls\":["
                + "{\"id\":\"tc_1\",\"function\":{\"name\":\"board_overview\",\"arguments\":\"{}\"}},"
                + "{\"id\":\"tc_2\",\"function\":{\"name\":\"list_specs\",\"arguments\":\"{}\"}}]}");

        ChatMessagePo user = new ChatMessagePo();
        user.setRole("user");
        user.setContent("inspect the board");

        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("incomplete"))
                .thenReturn(List.of(finalReply, oneOfTwoResults, incompleteCalls, user));

        Method method = ChatServiceImpl.class.getDeclaredMethod("getSmartHistory", String.class, int.class);
        method.setAccessible(true);
        List<ChatMessagePo> history = (List<ChatMessagePo>) method.invoke(service, "incomplete", 4000);

        assertEquals(2, history.size());
        assertEquals("user", history.get(0).getRole());
        assertEquals("assistant", history.get(1).getRole());
        assertTrue(history.stream().noneMatch(m -> "tool".equalsIgnoreCase(m.getRole())));
    }

    @SuppressWarnings("unchecked")
    @Test
    void getSmartHistory_shouldDropAssistantToolCallWithoutAnyResult() throws Exception {
        ChatMessagePo incompleteCalls = new ChatMessagePo();
        incompleteCalls.setRole("assistant");
        incompleteCalls.setContent("{\"type\":\"tool_calls\",\"toolCalls\":["
                + "{\"id\":\"tc_1\",\"function\":{\"name\":\"board_overview\",\"arguments\":\"{}\"}}]}");

        ChatMessagePo user = new ChatMessagePo();
        user.setRole("user");
        user.setContent("inspect the board");

        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("missing-results"))
                .thenReturn(List.of(incompleteCalls, user));

        Method method = ChatServiceImpl.class.getDeclaredMethod("getSmartHistory", String.class, int.class);
        method.setAccessible(true);
        List<ChatMessagePo> history = (List<ChatMessagePo>) method.invoke(service, "missing-results", 4000);

        assertEquals(1, history.size());
        assertEquals("user", history.get(0).getRole());
    }

    @SuppressWarnings("unchecked")
    @Test
    void getSmartHistory_shouldKeepLatestMessageEvenWhenOverCharLimit() throws Exception {
        ChatMessagePo oversizedUser = new ChatMessagePo();
        oversizedUser.setRole("user");
        oversizedUser.setContent("x".repeat(4500));

        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s3"))
                .thenReturn(List.of(oversizedUser));

        Method method = ChatServiceImpl.class.getDeclaredMethod("getSmartHistory", String.class, int.class);
        method.setAccessible(true);

        List<ChatMessagePo> history = (List<ChatMessagePo>) method.invoke(service, "s3", 4000);

        assertEquals(1, history.size());
        assertEquals("user", history.get(0).getRole());
        assertEquals(4500, history.get(0).getContent().length());
    }

    @Test
    void getHistory_shouldHideInternalToolMessagesFromFrontend() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s4");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("s4", 1L)).thenReturn(Optional.of(session));

        ChatMessagePo userMsg = new ChatMessagePo();
        userMsg.setRole("user");
        userMsg.setContent("turn on the light");

        ChatMessagePo assistantToolCall = new ChatMessagePo();
        assistantToolCall.setRole("assistant");
        assistantToolCall.setContent("{\"type\":\"tool_calls\",\"toolCalls\":[]}");

        ChatMessagePo toolResult = new ChatMessagePo();
        toolResult.setRole("tool");
        toolResult.setContent("{\"type\":\"tool_result\",\"toolCallId\":\"tc_1\",\"result\":\"ok\"}");

        ChatMessagePo assistantFallback = new ChatMessagePo();
        assistantFallback.setRole("assistant");
        assistantFallback.setContent("Calling tool...");

        ChatMessagePo assistantReply = new ChatMessagePo();
        assistantReply.setRole("assistant");
        assistantReply.setContent("Done. The light is on.");

        stubHistoryPage("s4", List.of(
                userMsg, assistantToolCall, toolResult, assistantFallback, assistantReply));
        when(chatMapper.toChatMessageDtoList(anyList()))
                .thenReturn(List.of(new ChatMessageResponseDto(), new ChatMessageResponseDto()));

        List<ChatMessageResponseDto> history = service.getHistory(1L, "s4");

        assertEquals(2, history.size());
        verify(chatMapper).toChatMessageDtoList(chatMessageListCaptor.capture());
        List<ChatMessagePo> visible = chatMessageListCaptor.getValue();
        assertEquals(2, visible.size());
        assertEquals("user", visible.get(0).getRole());
        assertEquals("assistant", visible.get(1).getRole());
        assertTrue(visible.stream().noneMatch(m -> "tool".equalsIgnoreCase(m.getRole())));
    }

    @Test
    void getHistory_shouldKeepNormalAssistantMessageCallingToolWhenNotAdjacentToToolBlock() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s5");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("s5", 1L)).thenReturn(Optional.of(session));

        ChatMessagePo userMsg = new ChatMessagePo();
        userMsg.setRole("user");
        userMsg.setContent("say exactly Calling tool...");

        ChatMessagePo assistantLiteral = new ChatMessagePo();
        assistantLiteral.setRole("assistant");
        assistantLiteral.setContent("Calling tool...");

        ChatMessagePo assistantReply = new ChatMessagePo();
        assistantReply.setRole("assistant");
        assistantReply.setContent("Done.");

        stubHistoryPage("s5", List.of(userMsg, assistantLiteral, assistantReply));
        when(chatMapper.toChatMessageDtoList(anyList()))
                .thenReturn(List.of(new ChatMessageResponseDto(), new ChatMessageResponseDto(), new ChatMessageResponseDto()));

        List<ChatMessageResponseDto> history = service.getHistory(1L, "s5");

        assertEquals(3, history.size());
        verify(chatMapper).toChatMessageDtoList(chatMessageListCaptor.capture());
        List<ChatMessagePo> visible = chatMessageListCaptor.getValue();
        assertEquals(3, visible.size());
        assertEquals("assistant", visible.get(1).getRole());
        assertEquals("Calling tool...", visible.get(1).getContent());
    }

    @Test
    void getHistory_shouldAttachConcretePersistedExecutionTraceToAssistantReply() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("trace-history");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("trace-history", 1L)).thenReturn(Optional.of(session));

        ObjectMapper mapper = new ObjectMapper();
        LlmMessageCodec codec = new LlmMessageCodec(mapper);
        LocalDateTime started = LocalDateTime.of(2026, 7, 18, 10, 0, 0);

        ChatMessagePo userMsg = new ChatMessagePo();
        userMsg.setRole("user");
        userMsg.setContent("检查当前画布");
        userMsg.setCreatedAt(started);

        ChatMessagePo assistantToolCall = new ChatMessagePo();
        assistantToolCall.setRole("assistant");
        assistantToolCall.setContent(codec.serializeToolCalls(List.of(
                new LlmToolCall("tc_1", "board_overview", "{}"))));

        ChatMessagePo toolResult = new ChatMessagePo();
        toolResult.setRole("tool");
        toolResult.setContent(codec.serializeToolResult("tc_1", """
                {"devices":[{},{}],"rules":[{}],"specs":[{}],"environmentVariables":[{}]}
                """));

        ChatMessagePo assistantReply = new ChatMessagePo();
        assistantReply.setRole("assistant");
        assistantReply.setContent("画布包含两个设备。");
        assistantReply.setCreatedAt(started.plusSeconds(12));

        stubHistoryPage("trace-history", List.of(userMsg, assistantToolCall, toolResult, assistantReply));
        ChatMessageResponseDto userDto = new ChatMessageResponseDto();
        userDto.setRole("user");
        ChatMessageResponseDto assistantDto = new ChatMessageResponseDto();
        assistantDto.setRole("assistant");
        when(chatMapper.toChatMessageDtoList(anyList())).thenReturn(List.of(userDto, assistantDto));

        List<ChatMessageResponseDto> history = service.getHistory(1L, "trace-history");

        assertEquals(2, history.size());
        assertEquals(12, assistantDto.getExecutionElapsedSeconds());
        assertEquals(List.of("CONTEXT_READY", "PLANNING", "TOOL_EXECUTION", "TOOL_RESULT", "WRITING_RESPONSE"),
                assistantDto.getExecutionTrace().stream().map(progress -> progress.getStage()).toList());
        assertEquals("已读取画布：2 个设备、1 条规则、1 条规约、1 个共享环境变量。",
                assistantDto.getExecutionTrace().get(3).getDetail());
    }

    @Test
    void getHistory_shouldRestoreExactTraceMetadataWithoutToolCallReconstruction() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("exact-trace-history");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("exact-trace-history", 1L)).thenReturn(Optional.of(session));

        ChatMessagePo userMsg = new ChatMessagePo();
        userMsg.setRole("user");
        userMsg.setContent("continue");

        List<StreamResponseDto.ProgressDto> persisted = List.of(
                new StreamResponseDto.ProgressDto(
                        "CONTEXT_READY", null, null, null, null, null, null, null),
                new StreamResponseDto.ProgressDto(
                        "TASK_RESUMED", null, null, null, null, null, null, "resume objective"),
                new StreamResponseDto.ProgressDto(
                        "EXECUTION_GUARD", null, 2, "NO_PROGRESS", 1, 0, 0, null));
        ChatMessagePo assistantReply = new ChatMessagePo();
        assistantReply.setId(42L);
        assistantReply.setRole("assistant");
        assistantReply.setContent("Stopped after no progress.");
        assistantReply.setExecutionTraceJson(new ObjectMapper().writeValueAsString(persisted));
        assistantReply.setExecutionElapsedSeconds(43);

        stubHistoryPage("exact-trace-history", List.of(userMsg, assistantReply));
        ChatMessageResponseDto userDto = new ChatMessageResponseDto();
        userDto.setRole("user");
        ChatMessageResponseDto assistantDto = new ChatMessageResponseDto();
        assistantDto.setRole("assistant");
        when(chatMapper.toChatMessageDtoList(anyList())).thenReturn(List.of(userDto, assistantDto));

        service.getHistory(1L, "exact-trace-history");

        assertEquals(43, assistantDto.getExecutionElapsedSeconds());
        assertEquals(List.of("CONTEXT_READY", "TASK_RESUMED", "EXECUTION_GUARD"),
                assistantDto.getExecutionTrace().stream().map(StreamResponseDto.ProgressDto::getStage).toList());
        assertEquals("NO_PROGRESS", assistantDto.getExecutionTrace().get(2).getOutcome());
    }

    @Test
    void sessionListExposesTheSameAuthoritativeLeaseActivityUsedByPolling() {
        ChatSessionPo live = new ChatSessionPo();
        live.setId("live-session");
        live.setActiveExecutionId("live-execution");
        live.setActiveExecutionExpiresAt(LocalDateTime.now().plusMinutes(1));
        ChatSessionPo expired = new ChatSessionPo();
        expired.setId("expired-session");
        expired.setActiveExecutionId("expired-execution");
        expired.setActiveExecutionExpiresAt(LocalDateTime.now().minusSeconds(1));
        ChatSessionResponseDto liveDto = new ChatSessionResponseDto();
        ChatSessionResponseDto expiredDto = new ChatSessionResponseDto();
        when(sessionRepo.findTop100ByUserIdOrderByUpdatedAtDesc(1L)).thenReturn(List.of(live, expired));
        when(chatMapper.toChatSessionDtoList(List.of(live, expired)))
                .thenReturn(List.of(liveDto, expiredDto));

        List<ChatSessionResponseDto> result = service.getUserSessions(1L);

        assertTrue(result.get(0).isActive());
        assertFalse(result.get(1).isActive());
    }

    @Test
    void historyPageReturnsNewestVisibleMessagesWithAnOlderCursor() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("paged-history");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("paged-history", 1L)).thenReturn(Optional.of(session));
        ChatMessagePo oldest = visibleMessage(1L, "user", "oldest");
        ChatMessagePo middle = visibleMessage(2L, "assistant", "middle");
        ChatMessagePo newest = visibleMessage(3L, "user", "newest");
        when(messageRepo.findBySessionIdOrderByIdDesc(eq("paged-history"), any(Pageable.class)))
                .thenReturn(List.of(newest, middle, oldest));
        when(chatMapper.toChatMessageDtoList(anyList()))
                .thenReturn(List.of(new ChatMessageResponseDto(), new ChatMessageResponseDto()));

        ChatHistoryPageDto page = service.getHistoryPage(1L, "paged-history", null, 2);

        assertEquals(2, page.getMessages().size());
        assertTrue(page.isHasMore());
        assertEquals(2L, page.getNextBeforeId());
        verify(chatMapper).toChatMessageDtoList(chatMessageListCaptor.capture());
        assertEquals(List.of("middle", "newest"), chatMessageListCaptor.getValue().stream()
                .map(ChatMessagePo::getContent).toList());
    }

    @Test
    void createSessionRejectsAnUnboundedCatalog() {
        when(sessionRepo.countByUserId(1L)).thenReturn(100L);

        assertThrows(cn.edu.nju.Iot_Verify.exception.BadRequestException.class,
                () -> service.createSession(1L));
        verify(sessionRepo, never()).save(org.mockito.ArgumentMatchers.any());
    }

    private ChatMessagePo visibleMessage(Long id, String role, String content) {
        ChatMessagePo message = new ChatMessagePo();
        message.setId(id);
        message.setRole(role);
        message.setContent(content);
        return message;
    }

    private void stubHistoryPage(String sessionId, List<ChatMessagePo> chronological) {
        long id = 1L;
        for (ChatMessagePo message : chronological) {
            if (message.getId() == null) message.setId(id);
            id = Math.max(id + 1, message.getId() + 1);
        }
        List<ChatMessagePo> newestFirst = new ArrayList<>(chronological);
        Collections.reverse(newestFirst);
        when(messageRepo.findBySessionIdOrderByIdDesc(eq(sessionId), any(Pageable.class)))
                .thenReturn(newestFirst);
    }

    @Test
    void activeStream_shouldBlockConcurrentStreamAndSessionDeletionUntilServerFinishes() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("busy-session");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("busy-session", 1L)).thenReturn(Optional.of(session));
        when(sessionRepo.findByIdAndUserIdForUpdate("busy-session", 1L)).thenReturn(Optional.of(session));

        String executionId = service.beginStreamRequest(1L, "busy-session");

        assertTrue(service.getSessionActivity(1L, "busy-session").isActive());
        assertThrows(ChatSessionBusyException.class,
                () -> service.beginStreamRequest(1L, "busy-session"));
        assertThrows(ChatSessionBusyException.class,
                () -> service.deleteSession(1L, "busy-session"));
        verify(messageRepo, never()).deleteBySessionId("busy-session");

        service.endStreamRequest(1L, "busy-session", executionId);

        assertFalse(service.getSessionActivity(1L, "busy-session").isActive());
        service.deleteSession(1L, "busy-session");
        verify(messageRepo).deleteBySessionId("busy-session");
        verify(sessionRepo).deleteById("busy-session");
        verify(destructiveActionGuard).clearSession(1L, "busy-session");
    }
}
