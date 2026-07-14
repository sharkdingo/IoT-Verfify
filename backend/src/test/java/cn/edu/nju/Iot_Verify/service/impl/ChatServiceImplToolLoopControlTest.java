package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.ChatIntentRouter;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
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
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ChatServiceImplToolLoopControlTest {

    @Mock
    private ChatSessionRepository sessionRepo;
    @Mock
    private ChatMessageRepository messageRepo;
    @Mock
    private LlmChatService llmChatService;
    @Mock
    private AiToolManager aiToolManager;
    @Mock
    private ChatMapper chatMapper;
    private LlmMessageCodec messageCodec;
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

        messageCodec = new LlmMessageCodec(new ObjectMapper());
        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                llmChatService,
                messageCodec,
                new ChatIntentRouter(),
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

        verify(llmChatService, never()).chatWithTools(anyList(), anyList());
        verify(aiToolManager, never()).execute(org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString());
    }

    @Test
    void assistantPrompts_requireRecommendationAccountingAndIncompleteModelDisclosure() throws Exception {
        Method planningMethod = ChatServiceImpl.class.getDeclaredMethod("buildToolPlanningSystemPrompt");
        planningMethod.setAccessible(true);
        Method visibleMethod = ChatServiceImpl.class.getDeclaredMethod(
                "buildVisibleReplySystemPrompt", boolean.class);
        visibleMethod.setAccessible(true);

        String planning = ((LlmMessage) planningMethod.invoke(service)).content();
        String visible = ((LlmMessage) visibleMethod.invoke(service, true)).content();

        assertTrue(planning.contains("truncated candidates were never inspected"));
        assertTrue(planning.contains("Do not call"));
        assertTrue(planning.contains("add_device, manage_rule, or manage_spec"));
        assertTrue(visible.contains("report rawCandidateCount"));
        assertTrue(visible.contains("SATISFIED with modelComplete=false"));
        assertTrue(visible.contains("one possible formal-model trajectory"));
        assertTrue(visible.contains("A verified suggestion still is not applied"));
    }

    @Test
    void executeToolLoop_whenToolReturnsError_shouldNotCollectRefreshCommand() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
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
        when(llmChatService.chatWithTools(anyList(), anyList()))
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
    void executeToolLoop_whenMutationResultIsUnavailable_shouldRefreshStopAndNotCountSuccess() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_rule", "{}"));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("{\"resultStatus\":\"RESULT_UNAVAILABLE\",\"resultAvailable\":false,"
                        + "\"mutationMayHaveCommitted\":true,\"message\":\"Refresh before retrying.\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        Object loopResult = invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertEquals(1, commandSet.size());
        assertEquals("rule_list", commandSet.iterator().next().getPayload().get("target"));
        assertEquals(0, recordInt(loopResult, "successfulToolCalls"));
        assertEquals(1, recordInt(loopResult, "resultUnavailableToolCalls"));
        assertEquals(1, recordInt(loopResult, "uncertainMutationCalls"));
        verify(llmChatService).chatWithTools(anyList(), anyList());
    }

    @Test
    void executeToolLoop_whenReadOnlyResultIsUnavailable_shouldStopWithoutRefresh() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("list_rules", "{}"));
        when(aiToolManager.execute("list_rules", "{}"))
                .thenReturn("{\"resultStatus\":\"RESULT_UNAVAILABLE\",\"resultAvailable\":false,"
                        + "\"mutationMayHaveCommitted\":false}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        Object loopResult = invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertTrue(commandSet.isEmpty());
        assertEquals(0, recordInt(loopResult, "successfulToolCalls"));
        assertEquals(1, recordInt(loopResult, "resultUnavailableToolCalls"));
        assertEquals(0, recordInt(loopResult, "uncertainMutationCalls"));
        verify(llmChatService).chatWithTools(anyList(), anyList());
    }

    @Test
    void executeToolLoop_whenDeletionNeedsConfirmation_shouldStopWithoutRefreshOrSecondPlanningRound() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("delete_device", "{\"id\":\"light_1\",\"confirmed\":false}"));
        when(aiToolManager.execute("delete_device", "{\"id\":\"light_1\",\"confirmed\":false}"))
                .thenReturn("{\"operation\":\"preview\",\"requiresUserConfirmation\":true,\"message\":\"No changes were made.\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertTrue(commandSet.isEmpty());
        verify(llmChatService).chatWithTools(anyList(), anyList());
        verify(aiToolManager).execute("delete_device", "{\"id\":\"light_1\",\"confirmed\":false}");
    }

    @Test
    void executeToolLoop_whenAddDeviceOffersAlternativeName_shouldNotAcceptItForTheUser() throws Exception {
        String args = "{\"templateName\":\"Light\",\"label\":\"Hall Light\"}";
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("add_device", args));
        when(aiToolManager.execute("add_device", args))
                .thenReturn("{\"error\":\"Display name is already in use. No device was created.\","
                        + "\"errorCode\":\"DEVICE_LABEL_CONFLICT\",\"operation\":\"notCreated\","
                        + "\"suggestedLabel\":\"Hall Light_1\",\"requiresUserConfirmation\":true}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        Object loopResult = invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertTrue(commandSet.isEmpty());
        assertTrue(recordBoolean(loopResult, "confirmationPending"));
        assertEquals(0, recordInt(loopResult, "successfulToolCalls"));
        verify(llmChatService).chatWithTools(anyList(), anyList());
        verify(aiToolManager).execute("add_device", args);
    }

    @Test
    void executeToolLoop_whenDeleteDeviceSucceeds_shouldRefreshDependentBoardLists() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("delete_device", "{\"identifier\":\"light_1\"}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("delete_device", "{\"identifier\":\"light_1\"}"))
                .thenReturn("{\"message\":\"ok\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        List<String> targets = commandSet.stream()
                .map(cmd -> String.valueOf(cmd.getPayload().get("target")))
                .toList();
        assertEquals(List.of("device_list", "environment_list", "rule_list", "spec_list"), targets);
    }

    @Test
    void executeToolLoop_whenAddDeviceSucceeds_shouldRefreshDeviceAndEnvironmentLists() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("add_device", "{\"templateName\":\"Sensor\"}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("add_device", "{\"templateName\":\"Sensor\"}"))
                .thenReturn("{\"message\":\"ok\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        List<String> targets = commandSet.stream()
                .map(cmd -> String.valueOf(cmd.getPayload().get("target")))
                .toList();
        assertEquals(List.of("device_list", "environment_list"), targets);
    }

    @Test
    void executeToolLoop_whenEnvironmentToolSucceeds_shouldRefreshEnvironmentList() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("manage_environment", "{\"action\":\"set\",\"name\":\"temperature\",\"value\":\"21\"}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("manage_environment", "{\"action\":\"set\",\"name\":\"temperature\",\"value\":\"21\"}"))
                .thenReturn("{\"message\":\"ok\",\"changesApplied\":true}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        StreamResponseDto.CommandDto command = commandSet.iterator().next();
        assertEquals("environment_list", command.getPayload().get("target"));
    }

    @Test
    void executeToolLoop_whenRunHistoryChanges_shouldRefreshRunHistory() throws Exception {
        for (String toolName : List.of(
                "verify_model", "verify_model_async", "simulate_model_async",
                "cancel_verify_task", "cancel_simulate_task",
                "delete_trace", "delete_simulation_trace")) {
            org.mockito.Mockito.reset(llmChatService, aiToolManager, messageRepo);
            when(llmChatService.chatWithTools(anyList(), anyList()))
                    .thenReturn(toolCallResult(toolName, "{}"))
                    .thenReturn(textResult("done"));
            when(aiToolManager.execute(toolName, "{}"))
                    .thenReturn("{\"message\":\"ok\"}");

            Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
            invokeToolLoop(new AtomicBoolean(false), commandSet);

            assertEquals(1, commandSet.size(), toolName);
            StreamResponseDto.CommandDto command = commandSet.iterator().next();
            assertEquals("run_history", command.getPayload().get("target"), toolName);
        }
    }

    @Test
    void executeToolLoop_whenToolReturnsNonJson_shouldNotCollectRefreshCommand() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
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
        when(llmChatService.chatWithTools(anyList(), anyList()))
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
        when(llmChatService.chatWithTools(anyList(), anyList()))
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

    @Test
    void processStreamChat_whenStreamingProviderFails_shouldSendSseErrorFrame() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        doThrow(ServiceUnavailableException.aiService(new RuntimeException("Invalid UTF-8 middle byte 0xe3")))
                .when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "hello", emitter);

        verify(emitter).send(any(SseEmitter.SseEventBuilder.class));
        verify(emitter).complete();
        verify(messageRepo, never()).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null && "assistant".equalsIgnoreCase(msg.getRole())));
    }

    @Test
    void processStreamChat_whenSessionMissing_shouldSendSseErrorFrame() throws Exception {
        when(sessionRepo.findByIdAndUserId("missing", 1L)).thenReturn(Optional.empty());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "missing", "hello", emitter);

        verify(emitter).send(any(SseEmitter.SseEventBuilder.class));
        verify(emitter).complete();
        verifyNoInteractions(aiToolManager);
    }

    @Test
    void processStreamChat_whenToolIntentDetected_shouldStreamVisibleFinalAnswerAfterPlanning() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        when(aiToolManager.getAllToolDefinitions()).thenReturn(List.of());
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("list_rules", "{}"))
                .thenReturn(textResult("planning done"));
        when(aiToolManager.execute("list_rules", "{}")).thenReturn("{\"rules\":[]}");
        AtomicReference<List<LlmMessage>> streamedMessages = new AtomicReference<>();
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            List<LlmMessage> messages = invocation.getArgument(0, List.class);
            streamedMessages.set(messages);
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("stream ");
            onDelta.accept("final");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "please list rules", emitter);

        verify(llmChatService).streamReply(anyList(), any(), any());
        verify(emitter, org.mockito.Mockito.times(2)).send(any(SseEmitter.SseEventBuilder.class));
        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null
                        && "assistant".equalsIgnoreCase(msg.getRole())
                        && "stream final".equals(msg.getContent())));
        String systemPrompt = streamedMessages.get().get(0).content();
        assertTrue(systemPrompt.contains("Tool executions may already be present"));
        assertTrue(systemPrompt.contains("Do not emit tool-call JSON"));
        assertTrue(systemPrompt.contains("resultAvailable=false"));
        assertTrue(systemPrompt.contains("Do not expose device node ids"));
        assertTrue(systemPrompt.contains("verificationStatus=NOT_VERIFIED"));
        assertTrue(systemPrompt.contains("Reply in the language used by the user's latest message"));
        assertFalse(systemPrompt.contains("Available tools:"));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenChineseDeletionPreview_shouldLocalizeSafetyNotice() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        String arguments = "{\"id\":\"air_conditioner\",\"confirmed\":false}";
        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        when(aiToolManager.getAllToolDefinitions()).thenReturn(List.of());
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("delete_device", arguments));
        when(aiToolManager.execute("delete_device", arguments))
                .thenReturn("{\"operation\":\"preview\",\"requiresUserConfirmation\":true}");
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("尚未删除，请确认是否继续。");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "删除设备 Air Conditioner", emitter);

        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null
                        && "assistant".equalsIgnoreCase(msg.getRole())
                        && msg.getContent() != null
                        && msg.getContent().startsWith("提示：当前只是未写入的影响预览或备选方案")
                        && msg.getContent().contains("尚未删除，请确认是否继续。")
                        && !msg.getContent().contains("A no-write preview")));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenNoToolIntent_shouldSkipToolPlanningAndStreamReply() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        AtomicReference<List<LlmMessage>> streamedMessages = new AtomicReference<>();
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            List<LlmMessage> messages = invocation.getArgument(0, List.class);
            streamedMessages.set(messages);
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("ok");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "hello", emitter);

        verify(aiToolManager, never()).getAllToolDefinitions();
        verify(llmChatService, never()).chatWithTools(anyList(), anyList());
        verify(llmChatService).streamReply(anyList(), any(), any());
        String systemPrompt = streamedMessages.get().get(0).content();
        assertTrue(systemPrompt.contains("No tools are available for this response"));
        assertTrue(systemPrompt.contains("Do not emit tool-call JSON"));
        assertFalse(systemPrompt.contains("Available tools:"));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenToolLoopReachesLimit_reportsPartialExecutionWithoutClaimingCompletion() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        when(aiToolManager.getAllToolDefinitions()).thenReturn(List.of());
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("list_rules", "{}"));
        when(aiToolManager.execute("list_rules", "{}")).thenReturn("{\"rules\":[]}");

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "please list rules", emitter);

        verify(llmChatService, never()).streamReply(anyList(), any(), any());
        verify(aiToolManager, org.mockito.Mockito.times(5)).execute("list_rules", "{}");
        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null
                        && "assistant".equalsIgnoreCase(msg.getRole())
                        && msg.getContent() != null
                        && msg.getContent().contains("reached its 5-round planning limit")
                        && msg.getContent().contains("Some requested work may therefore be incomplete")
                        && !msg.getContent().contains("operation completed")));
        verify(emitter).complete();
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
                new ArrayList<LlmMessage>(),
                new ArrayList<LlmToolSpec>(),
                commandSet,
                emitter,
                disconnected
        );
    }

    private LlmChatResponse toolCallResult(String functionName, String argsJson) {
        return LlmChatResponse.ofToolCalls(List.of(new LlmToolCall("tc_1", functionName, argsJson)));
    }

    private LlmChatResponse textResult(String text) {
        return LlmChatResponse.ofText(text);
    }

    private int recordInt(Object record, String accessor) throws Exception {
        Method method = record.getClass().getDeclaredMethod(accessor);
        method.setAccessible(true);
        return (Integer) method.invoke(record);
    }

    private boolean recordBoolean(Object record, String accessor) throws Exception {
        Method method = record.getClass().getDeclaredMethod(accessor);
        method.setAccessible(true);
        return (Boolean) method.invoke(record);
    }

}
