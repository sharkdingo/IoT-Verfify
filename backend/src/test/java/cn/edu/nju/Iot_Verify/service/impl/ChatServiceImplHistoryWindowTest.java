package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.lang.reflect.Method;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
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

    private ChatServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                arkAiClient,
                aiToolManager,
                new ObjectMapper(),
                chatMapper
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
}
