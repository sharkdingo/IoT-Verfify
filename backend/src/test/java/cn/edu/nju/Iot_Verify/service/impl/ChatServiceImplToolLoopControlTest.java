package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionChoice;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionResult;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunctionCall;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import com.volcengine.ark.runtime.model.completion.chat.ChatToolCall;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.lang.NonNull;
import org.springframework.transaction.TransactionStatus;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ChatServiceImplToolLoopControlTest {

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
    private TransactionTemplate transactionTemplate;

    private ChatServiceImpl service;
    private Method executeToolLoopMethod;
    private Method jsonErrorMethod;

    @BeforeEach
    void setUp() throws Exception {
        transactionTemplate = new TransactionTemplate() {
            @Override
            public void executeWithoutResult(@NonNull Consumer<TransactionStatus> action) {
                action.accept(mock(TransactionStatus.class));
            }
        };

        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                arkAiClient,
                aiToolManager,
                new ObjectMapper(),
                chatMapper,
                transactionTemplate
        );
        executeToolLoopMethod = ChatServiceImpl.class.getDeclaredMethod(
                "executeToolLoop",
                String.class,
                List.class,
                List.class,
                Set.class,
                SseEmitter.class,
                AtomicBoolean.class
        );
        executeToolLoopMethod.setAccessible(true);

        jsonErrorMethod = ChatServiceImpl.class.getDeclaredMethod(
                "jsonError",
                String.class,
                String.class,
                int.class
        );
        jsonErrorMethod.setAccessible(true);
    }

    @Test
    void executeToolLoop_whenDisconnected_shouldSkipIntentCall() throws Exception {
        invokeToolLoop(new AtomicBoolean(true), new LinkedHashSet<>());

        verify(arkAiClient, never()).checkIntent(anyList(), anyList());
        verify(aiToolManager, never()).execute(org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString());
    }

    @Test
    void executeToolLoop_whenToolReturnsError_shouldNotCollectRefreshCommand() throws Exception {
        when(arkAiClient.checkIntent(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_rule", "{}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("{\"error\":\"failed\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertTrue(commandSet.isEmpty());
    }

    @Test
    void executeToolLoop_whenToolSucceeds_shouldCollectRefreshCommand() throws Exception {
        when(arkAiClient.checkIntent(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_rule", "{}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("{\"message\":\"ok\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertEquals(1, commandSet.size());
        StreamResponseDto.CommandDto cmd = commandSet.iterator().next();
        assertEquals("REFRESH_DATA", cmd.getType());
        assertEquals("rule_list", cmd.getPayload().get("target"));
    }

    @Test
    void executeToolLoop_whenToolReturnsNonJson_shouldNotCollectRefreshCommand() throws Exception {
        when(arkAiClient.checkIntent(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_rule", "{}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("Rule added successfully.");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertTrue(commandSet.isEmpty());
    }

    @Test
    void executeToolLoop_shouldNotEmitInternalProgressChunk() throws Exception {
        when(arkAiClient.checkIntent(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_rule", "{}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("{\"message\":\"ok\"}");

        SseEmitter emitter = mock(SseEmitter.class);

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet, emitter);

        verify(aiToolManager).execute("manage_rule", "{}");
        assertEquals(1, commandSet.size());
    }

    @Test
    void executeToolLoop_whenFunctionNameMissing_shouldPersistStructuredErrorAndSkipToolExecution() throws Exception {
        when(arkAiClient.checkIntent(anyList(), anyList()))
                .thenReturn(toolCallResult("   ", "{}"))
                .thenReturn(textResult("done"));

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        verify(aiToolManager, never()).execute(org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString());
        assertTrue(commandSet.isEmpty());

        List<ChatMessagePo> persistedMessages = org.mockito.Mockito.mockingDetails(messageRepo).getInvocations().stream()
                .filter(invocation -> invocation.getMethod().getName().equals("saveAndFlush"))
                .map(invocation -> invocation.getArgument(0, ChatMessagePo.class))
                .filter(Objects::nonNull)
                .toList();
        assertEquals(2, persistedMessages.size());
        ChatMessagePo toolMsg = Objects.requireNonNull(persistedMessages.stream()
                .filter(m -> "tool".equalsIgnoreCase(m.getRole()))
                .findFirst()
                .orElseThrow());

        ObjectMapper mapper = new ObjectMapper();
        JsonNode persisted = mapper.readTree(toolMsg.getContent());
        JsonNode result = mapper.readTree(persisted.path("result").asText());
        assertEquals("Invalid tool call: missing function name.", result.path("error").asText());
        assertEquals("VALIDATION_ERROR", result.path("errorCode").asText());
        assertEquals(400, result.path("status").asInt());
    }

    @Test
    void jsonError_shouldReturnStructuredErrorJson() throws Exception {
        String result = (String) jsonErrorMethod.invoke(
                service,
                "Invalid tool call: missing function name.",
                "VALIDATION_ERROR",
                400
        );

        JsonNode json = new ObjectMapper().readTree(result);
        assertEquals("Invalid tool call: missing function name.", json.path("error").asText());
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    private Object invokeToolLoop(AtomicBoolean disconnected, Set<StreamResponseDto.CommandDto> commandSet) throws Exception {
        return invokeToolLoop(disconnected, commandSet, mock(SseEmitter.class));
    }

    private Object invokeToolLoop(AtomicBoolean disconnected,
                                  Set<StreamResponseDto.CommandDto> commandSet,
                                  SseEmitter emitter) throws Exception {
        return executeToolLoopMethod.invoke(
                service,
                "s1",
                new ArrayList<ChatMessage>(),
                new ArrayList<ChatTool>(),
                commandSet,
                emitter,
                disconnected
        );
    }

    private ChatCompletionResult toolCallResult(String functionName, String argsJson) {
        ChatToolCall call = new ChatToolCall();
        call.setId("tc_1");
        call.setType("function");
        call.setFunction(new ChatFunctionCall(functionName, argsJson));

        ChatMessage message = ChatMessage.builder()
                .role(ChatMessageRole.ASSISTANT)
                .content("")
                .toolCalls(List.of(call))
                .build();

        ChatCompletionChoice choice = new ChatCompletionChoice();
        choice.setMessage(message);

        ChatCompletionResult result = new ChatCompletionResult();
        result.setChoices(List.of(choice));
        return result;
    }

    private ChatCompletionResult textResult(String text) {
        ChatMessage message = ChatMessage.builder()
                .role(ChatMessageRole.ASSISTANT)
                .content(text)
                .build();

        ChatCompletionChoice choice = new ChatCompletionChoice();
        choice.setMessage(message);

        ChatCompletionResult result = new ChatCompletionResult();
        result.setChoices(List.of(choice));
        return result;
    }

}
