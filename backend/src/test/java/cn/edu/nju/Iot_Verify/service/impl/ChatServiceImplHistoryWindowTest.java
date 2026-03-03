package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Captor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.transaction.support.TransactionTemplate;

import java.lang.reflect.Method;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ChatServiceImplHistoryWindowTest {

    @Mock
    private ChatSessionRepository sessionRepo;
    @Mock
    private ChatMessageRepository messageRepo;
    @Mock
    private ArkAiClient arkAiClient;
    @Mock
    private AiToolManager aiToolManager;
    @Mock
    private ChatMapper chatMapper;
    @Mock
    private TransactionTemplate transactionTemplate;
    @Captor
    private ArgumentCaptor<List<ChatMessagePo>> chatMessageListCaptor;

    private ChatServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                arkAiClient,
                aiToolManager,
                new ObjectMapper(),
                chatMapper,
                transactionTemplate
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

        when(messageRepo.findBySessionIdOrderByCreatedAtAsc("s4"))
                .thenReturn(List.of(userMsg, assistantToolCall, toolResult, assistantFallback, assistantReply));
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

        when(messageRepo.findBySessionIdOrderByCreatedAtAsc("s5"))
                .thenReturn(List.of(userMsg, assistantLiteral, assistantReply));
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
}
