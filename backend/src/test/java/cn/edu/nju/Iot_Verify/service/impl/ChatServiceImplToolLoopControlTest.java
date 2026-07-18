package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.ai.AiTaskContinuationStore;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.AiScenarioDraftStore;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
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
import java.time.Instant;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.lenient;
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
    private LlmMessageCodec messageCodec;
    private TransactionTemplate transactionTemplate;
    private ChatExecutionConfig chatExecutionConfig;

    private ChatServiceImpl service;
    private Method executeToolLoopMethod;
    private Method executeToolLoopWithTraceMethod;
    private Method jsonErrorMethod;
    private Method toolProgressDetailMethod;

    @BeforeEach
    void setUp() throws Exception {
        transactionTemplate = new TransactionTemplate() {
            @Override
            public void executeWithoutResult(@NonNull Consumer<TransactionStatus> action) {
                action.accept(mock(TransactionStatus.class));
            }
        };

        messageCodec = new LlmMessageCodec(new ObjectMapper());
        chatExecutionConfig = new ChatExecutionConfig();
        lenient().when(userRepository.findByIdForUpdate(1L))
                .thenReturn(Optional.of(UserPo.builder().id(1L).build()));
        ChatSessionPo defaultSession = new ChatSessionPo();
        defaultSession.setId("s1");
        defaultSession.setUserId(1L);
        lenient().when(sessionRepo.findByIdAndUserId("s1", 1L))
                .thenReturn(Optional.of(defaultSession));
        service = new ChatServiceImpl(
                sessionRepo,
                messageRepo,
                userRepository,
                llmChatService,
                messageCodec,
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
                chatExecutionConfig
        );
        executeToolLoopMethod = ChatServiceImpl.class.getDeclaredMethod(
                "executeToolLoop",
                Long.class,
                String.class,
                List.class,
                List.class,
                Set.class,
                SseEmitter.class,
                AtomicBoolean.class
        );
        executeToolLoopMethod.setAccessible(true);
        executeToolLoopWithTraceMethod = ChatServiceImpl.class.getDeclaredMethod(
                "executeToolLoop",
                Long.class,
                String.class,
                List.class,
                List.class,
                Set.class,
                SseEmitter.class,
                AtomicBoolean.class,
                boolean.class,
                List.class
        );
        executeToolLoopWithTraceMethod.setAccessible(true);

        jsonErrorMethod = ChatServiceImpl.class.getDeclaredMethod(
                "jsonError",
                String.class,
                String.class,
                int.class
        );
        jsonErrorMethod.setAccessible(true);
        toolProgressDetailMethod = ChatServiceImpl.class.getDeclaredMethod(
                "toolProgressDetail", String.class, String.class, boolean.class);
        toolProgressDetailMethod.setAccessible(true);
    }

    @Test
    void executeToolLoop_whenDisconnected_shouldSkipIntentCall() throws Exception {
        invokeToolLoop(new AtomicBoolean(true), new LinkedHashSet<>());

        verify(llmChatService, never()).chatWithTools(anyList(), anyList());
        verify(aiToolManager, never()).execute(org.mockito.ArgumentMatchers.anyString(), org.mockito.ArgumentMatchers.anyString());
    }

    @Test
    void toolProgressDetail_shouldNotExposeRawInternalIdentifiersFromErrors() throws Exception {
        String detail = (String) toolProgressDetailMethod.invoke(
                service,
                "manage_rule",
                "{\"error\":\"Rule rule-17 for user id 42 was not found\",\"errorCode\":\"NOT_FOUND\"}",
                false);

        assertTrue(detail.contains("NOT_FOUND"));
        assertFalse(detail.contains("rule-17"));
        assertFalse(detail.contains("42"));
    }

    @Test
    void toolProgressDetail_shouldSummarizeCommonMutationFromStructuredFields() throws Exception {
        String detail = (String) toolProgressDetailMethod.invoke(
                service,
                "add_device",
                "{\"operation\":\"created\",\"device\":{\"id\":\"device-17\",\"label\":\"Hall Light\",\"state\":\"off\"},\"environmentChanges\":[{}]}",
                false);

        assertTrue(detail.contains("Hall Light"));
        assertTrue(detail.contains("initial state off"));
        assertTrue(detail.contains("1 Environment Pool change"));
        assertFalse(detail.contains("device-17"));
    }

    @Test
    void executeToolLoop_shouldEmitSanitizedReactReasoningBeforeTheToolAction() throws Exception {
        LlmToolCall call = new LlmToolCall("tc_1", "board_overview", "{}");
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(LlmChatResponse.ofTextAndToolCalls(
                        "Inspect device_17 and impactToken=secret before choosing the next action.",
                        List.of(call)))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("board_overview", "{}"))
                .thenReturn("{\"devices\":[],\"rules\":[],\"specs\":[],\"environmentVariables\":[]}");
        List<StreamResponseDto.ProgressDto> trace = new ArrayList<>();

        executeToolLoopWithTraceMethod.invoke(
                service,
                1L,
                "s1",
                new ArrayList<LlmMessage>(),
                new ArrayList<LlmToolSpec>(),
                new LinkedHashSet<StreamResponseDto.CommandDto>(),
                mock(SseEmitter.class),
                new AtomicBoolean(false),
                false,
                trace);

        int reasoningIndex = java.util.stream.IntStream.range(0, trace.size())
                .filter(index -> "REASONING".equals(trace.get(index).getStage()))
                .findFirst()
                .orElseThrow();
        int executionIndex = java.util.stream.IntStream.range(0, trace.size())
                .filter(index -> "TOOL_EXECUTION".equals(trace.get(index).getStage()))
                .findFirst()
                .orElseThrow();
        assertTrue(reasoningIndex < executionIndex);
        assertTrue(trace.get(reasoningIndex).getDetail().contains("[internal reference]"));
        assertTrue(trace.get(reasoningIndex).getDetail().contains("impactToken=[hidden]"));
        assertFalse(trace.get(reasoningIndex).getDetail().contains("device_17"));
        assertFalse(trace.get(reasoningIndex).getDetail().contains("secret"));
    }

    @Test
    void reactReasoning_shouldKeepMoreContextThanCompactToolResults() throws Exception {
        String reasoning = "Goal and evidence. " + "remaining context ".repeat(30);
        LlmToolCall call = new LlmToolCall("tc_long", "board_overview", "{}");
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(LlmChatResponse.ofTextAndToolCalls(reasoning, List.of(call)))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("board_overview", "{}"))
                .thenReturn("{\"devices\":[],\"rules\":[],\"specs\":[],\"environmentVariables\":[]}");
        List<StreamResponseDto.ProgressDto> trace = new ArrayList<>();

        executeToolLoopWithTraceMethod.invoke(
                service,
                1L,
                "s1",
                new ArrayList<LlmMessage>(),
                new ArrayList<LlmToolSpec>(),
                new LinkedHashSet<StreamResponseDto.CommandDto>(),
                mock(SseEmitter.class),
                new AtomicBoolean(false),
                false,
                trace);

        String detail = trace.stream()
                .filter(progress -> "REASONING".equals(progress.getStage()))
                .findFirst()
                .orElseThrow()
                .getDetail();
        assertTrue(detail.length() > 240);
        assertTrue(detail.length() <= 800);
    }

    @Test
    void taskContinuation_shouldRemoveNestedConfirmationTokens() throws Exception {
        Method method = ChatServiceImpl.class.getDeclaredMethod(
                "sanitizePendingResultForContinuation", String.class);
        method.setAccessible(true);

        String sanitized = (String) method.invoke(service, """
                {
                  "requiresUserConfirmation": true,
                  "preview": {
                    "impactToken": "nested-secret",
                    "items": [{"confirmationToken": "array-secret", "name": "Light"}]
                  },
                  "domainImpactToken": "root-secret"
                }
                """);

        JsonNode json = new ObjectMapper().readTree(sanitized);
        assertFalse(json.has("domainImpactToken"));
        assertFalse(json.path("preview").has("impactToken"));
        assertFalse(json.path("preview").path("items").get(0).has("confirmationToken"));
        assertEquals("Light", json.path("preview").path("items").get(0).path("name").asText());
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
        assertTrue(planning.contains("complete tool catalog"));
        assertTrue(planning.contains("inspect current Board state only when"));
        assertTrue(planning.contains("use list_templates only when"));
        assertTrue(planning.contains("use manage_rule directly"));
        assertTrue(planning.contains("ReAct activity summary"));
        assertTrue(planning.contains("audit-friendly summary, not private hidden chain-of-thought"));
        assertTrue(planning.contains("Use recommend_scenario only"));
        assertTrue(planning.contains("call apply_scenario with confirmed=false"));
        assertTrue(planning.contains("do not delete or recreate devices individually"));
        assertTrue(planning.contains("Do not call"));
        assertTrue(planning.contains("add_device, manage_rule, or manage_spec"));
        assertTrue(visible.contains("Match the level of detail to the user's request"));
        assertTrue(visible.contains("SATISFIED with modelComplete=false"));
        assertTrue(visible.contains("one possible formal-model trajectory"));
        assertTrue(visible.contains("A verified suggestion still is not applied"));
        assertTrue(visible.contains("Never expose impactToken"));
    }

    @Test
    void pendingConfirmationPrompt_restoresDestructiveTokenOutsideHistoryWindow() throws Exception {
        Method method = ChatServiceImpl.class.getDeclaredMethod(
                "buildPendingTaskSystemPrompt",
                AiDestructiveActionGuard.PendingActionContext.class,
                AiScenarioDraftStore.PendingApplication.class,
                AiTaskContinuationStore.ContinuationContext.class,
                ChatConfirmationDetector.ConfirmationDecision.class,
                String.class);
        method.setAccessible(true);

        LlmMessage context = (LlmMessage) method.invoke(
                service,
                new AiDestructiveActionGuard.PendingActionContext(
                        "delete_device", "alarm_1", "server-token"),
                null,
                new AiTaskContinuationStore.ContinuationContext(
                        "Replace the hall alarm and verify the repaired scene",
                        List.of("Keep the existing rules"),
                        "delete_device",
                        "{\"operation\":\"preview\"}",
                        Instant.parse("2026-07-17T12:00:00Z")),
                ChatConfirmationDetector.ConfirmationDecision.confirmed(
                        ChatConfirmationDetector.ConfirmationKind.DESTRUCTIVE),
                "Confirm deletion, but do not create another alarm");

        assertTrue(context.content().contains("delete_device"));
        assertTrue(context.content().contains("alarm_1"));
        assertTrue(context.content().contains("server-token"));
        assertTrue(context.content().contains("Do not request another preview"));
        assertTrue(context.content().contains("Replace the hall alarm"));
        assertTrue(context.content().contains("latest user message is authoritative"));
        assertTrue(context.content().contains("do not create another alarm"));
    }

    @Test
    void pendingConfirmationPrompt_usesResetSchemaWithoutInventingTargetArgument() throws Exception {
        Method method = ChatServiceImpl.class.getDeclaredMethod(
                "buildPendingTaskSystemPrompt",
                AiDestructiveActionGuard.PendingActionContext.class,
                AiScenarioDraftStore.PendingApplication.class,
                AiTaskContinuationStore.ContinuationContext.class,
                ChatConfirmationDetector.ConfirmationDecision.class,
                String.class);
        method.setAccessible(true);

        LlmMessage context = (LlmMessage) method.invoke(
                service,
                new AiDestructiveActionGuard.PendingActionContext(
                        "reset_default_templates", "bundled-default-template-catalog", "reset-token"),
                null,
                null,
                ChatConfirmationDetector.ConfirmationDecision.confirmed(
                        ChatConfirmationDetector.ConfirmationKind.DEFAULT_TEMPLATE_RESET),
                "Confirm refreshing the bundled default templates");

        assertTrue(context.content().contains("reset_default_templates exactly once"));
        assertTrue(context.content().contains("confirmed=true"));
        assertTrue(context.content().contains("reset-token"));
        assertTrue(context.content().contains("Do not add a target field"));
        assertFalse(context.content().contains("bundled-default-template-catalog"));
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
    void executeToolLoop_whenScenarioApplySucceeds_shouldRefreshWholeBoard() throws Exception {
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(toolCallResult("apply_scenario", "{\"confirmed\":true}"))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute("apply_scenario", "{\"confirmed\":true}"))
                .thenReturn("{\"operation\":\"replaced\",\"message\":\"ok\"}");

        Set<StreamResponseDto.CommandDto> commandSet = new LinkedHashSet<>();
        invokeToolLoop(new AtomicBoolean(false), commandSet);

        assertEquals(1, commandSet.size());
        assertEquals("board_state", commandSet.iterator().next().getPayload().get("target"));
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
    void executeToolLoop_whenOneOfSeveralCallsNeedsConfirmation_shouldRecordRemainingCallsAsSkipped() throws Exception {
        List<LlmToolCall> plannedCalls = List.of(
                new LlmToolCall("tc_preview", "delete_device",
                        "{\"id\":\"light_1\",\"confirmed\":false}"),
                new LlmToolCall("tc_later", "manage_spec", "{\"action\":\"add\"}"));
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(LlmChatResponse.ofToolCalls(plannedCalls));
        when(aiToolManager.execute("delete_device", "{\"id\":\"light_1\",\"confirmed\":false}"))
                .thenReturn("{\"operation\":\"preview\",\"requiresUserConfirmation\":true}");

        List<LlmMessage> messages = new ArrayList<>();
        Object loopResult = invokeToolLoop(
                new AtomicBoolean(false), new LinkedHashSet<>(), mock(SseEmitter.class), messages);

        verify(aiToolManager, never()).execute("manage_spec", "{\"action\":\"add\"}");
        assertTrue(recordBoolean(loopResult, "confirmationPending"));
        assertEquals(3, messages.size());
        assertEquals("tc_preview", messages.get(1).toolCallId());
        assertEquals("tc_later", messages.get(2).toolCallId());
        JsonNode skipped = new ObjectMapper().readTree(messages.get(2).content());
        assertTrue(skipped.path("skipped").asBoolean());
        assertFalse(skipped.path("executed").asBoolean(true));
        assertEquals("PRIOR_CONFIRMATION_REQUIRED", skipped.path("reasonCode").asText());
    }

    @Test
    void executeToolLoop_whenOneOfSeveralResultsIsUnavailable_shouldRecordRemainingCallsAsSkipped() throws Exception {
        List<LlmToolCall> plannedCalls = List.of(
                new LlmToolCall("tc_unavailable", "manage_rule", "{}"),
                new LlmToolCall("tc_later", "manage_spec", "{\"action\":\"add\"}"));
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(LlmChatResponse.ofToolCalls(plannedCalls));
        when(aiToolManager.execute("manage_rule", "{}"))
                .thenReturn("{\"resultStatus\":\"RESULT_UNAVAILABLE\",\"resultAvailable\":false,"
                        + "\"mutationMayHaveCommitted\":true}");

        List<LlmMessage> messages = new ArrayList<>();
        invokeToolLoop(new AtomicBoolean(false), new LinkedHashSet<>(), mock(SseEmitter.class), messages);

        verify(aiToolManager, never()).execute("manage_spec", "{\"action\":\"add\"}");
        assertEquals(3, messages.size());
        JsonNode skipped = new ObjectMapper().readTree(messages.get(2).content());
        assertEquals("PRIOR_RESULT_UNAVAILABLE", skipped.path("reasonCode").asText());
    }

    @Test
    void executeToolLoop_repairsBlankDuplicateAndReusedProviderToolCallIds() throws Exception {
        List<LlmToolCall> plannedCalls = List.of(
                new LlmToolCall("", "list_rules", "{}"),
                new LlmToolCall("already_used", "list_specs", "{}"),
                new LlmToolCall("already_used", "board_overview", "{}"));
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(LlmChatResponse.ofToolCalls(plannedCalls))
                .thenReturn(textResult("done"));
        when(aiToolManager.execute(anyString(), anyString())).thenReturn("{\"count\":0}");

        List<LlmMessage> messages = new ArrayList<>(List.of(
                LlmMessage.assistantToolCalls(List.of(
                        new LlmToolCall("already_used", "list_templates", "{}"))),
                LlmMessage.tool("already_used", "{\"count\":45}")));
        invokeToolLoop(new AtomicBoolean(false), new LinkedHashSet<>(), mock(SseEmitter.class), messages);

        List<String> assistantIds = messages.get(2).toolCalls().stream().map(LlmToolCall::id).toList();
        List<String> resultIds = messages.subList(3, 6).stream().map(LlmMessage::toolCallId).toList();
        assertEquals(3, new LinkedHashSet<>(assistantIds).size());
        assertTrue(assistantIds.stream().noneMatch(String::isBlank));
        assertFalse(assistantIds.contains("already_used"));
        assertEquals(assistantIds, resultIds);
        verify(aiToolManager).execute("list_rules", "{}");
        verify(aiToolManager).execute("list_specs", "{}");
        verify(aiToolManager).execute("board_overview", "{}");
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
    void requestLocalUserExecutionStop_whenRequestIsQueued_preventsChatWorkFromStarting() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        SseEmitter emitter = mock(SseEmitter.class);

        service.beginStreamRequest(1L, "s1");
        service.requestLocalUserExecutionStop(1L);
        service.processStreamChat(1L, "s1", "hello", emitter);

        verify(emitter).complete();
        verify(messageRepo, never()).saveAndFlush(any());
        verifyNoInteractions(llmChatService, aiToolManager);
        verify(destructiveActionGuard).clearUser(1L);
        service.endStreamRequest(1L, "s1");
    }

    @Test
    void processStreamChat_whenAccountDisappearsBeforeAssistantWrite_doesNotPersistLateMessage() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");
        UserPo user = UserPo.builder().id(1L).build();
        when(userRepository.findByIdForUpdate(1L))
                .thenReturn(Optional.of(user), Optional.empty());
        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("late answer");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());
        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "hello", emitter);

        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null && "user".equals(msg.getRole())));
        verify(messageRepo, never()).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null && "assistant".equals(msg.getRole())));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenAccountStopArrivesDuringToolPlanning_doesNotExecutePlannedTool() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");
        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        when(aiToolManager.getAllToolDefinitions()).thenReturn(List.of());
        when(llmChatService.chatWithTools(anyList(), anyList())).thenAnswer(invocation -> {
            service.requestLocalUserExecutionStop(1L);
            return toolCallResult("list_rules", "{}");
        });
        SseEmitter emitter = mock(SseEmitter.class);

        service.beginStreamRequest(1L, "s1");
        service.processStreamChat(1L, "s1", "please list rules", emitter);

        verify(aiToolManager, never()).execute(any(), any());
        verify(messageRepo, never()).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null && ("assistant".equals(msg.getRole()) || "tool".equals(msg.getRole()))));
        verify(emitter).complete();
        service.endStreamRequest(1L, "s1");
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

        verify(emitter, org.mockito.Mockito.atLeastOnce()).send(any(SseEmitter.SseEventBuilder.class));
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
        verify(emitter, org.mockito.Mockito.atLeast(2)).send(any(SseEmitter.SseEventBuilder.class));
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
    void processStreamChat_alwaysOffersCompleteCatalogAndLetsModelUseNoTool() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        List<LlmToolSpec> completeCatalog = List.of(
                toolSpec("board_overview"),
                toolSpec("recommend_scenario"),
                toolSpec("add_device"),
                toolSpec("manage_rule"),
                toolSpec("manage_spec"));
        when(aiToolManager.getAllToolDefinitions()).thenReturn(completeCatalog);
        AtomicReference<List<LlmToolSpec>> plannedTools = new AtomicReference<>();
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            List<LlmToolSpec> tools = invocation.getArgument(1, List.class);
            plannedTools.set(tools);
            return textResult("No tool is needed.");
        }).when(llmChatService).chatWithTools(anyList(), anyList());
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

        verify(destructiveActionGuard, never()).clearSession(1L, "s1");
        assertEquals(completeCatalog, plannedTools.get());
        verify(aiToolManager).getAllToolDefinitions();
        verify(llmChatService).chatWithTools(anyList(), eq(completeCatalog));
        verify(llmChatService).streamReply(anyList(), any(), any());
        String systemPrompt = streamedMessages.get().get(0).content();
        assertTrue(systemPrompt.contains("planning stage did not execute a tool"));
        assertTrue(systemPrompt.contains("do not claim to have read current platform data"));
        assertTrue(systemPrompt.contains("Do not emit tool-call JSON"));
        assertFalse(systemPrompt.contains("Available tools:"));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenMoreThanFiveRoundsMakeProgress_continuesAndStreamsFinalReply() throws Exception {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("s1");
        session.setUserId(1L);
        session.setTitle("New Chat");

        when(sessionRepo.findByIdAndUserId("s1", 1L)).thenReturn(Optional.of(session));
        when(messageRepo.findTop80BySessionIdOrderByCreatedAtDesc("s1")).thenReturn(List.of());
        when(aiToolManager.getAllToolDefinitions()).thenReturn(List.of());
        when(llmChatService.chatWithTools(anyList(), anyList()))
                .thenReturn(
                        toolCallResult("list_rules", "{\"page\":1}"),
                        toolCallResult("list_rules", "{\"page\":2}"),
                        toolCallResult("list_rules", "{\"page\":3}"),
                        toolCallResult("list_rules", "{\"page\":4}"),
                        toolCallResult("list_rules", "{\"page\":5}"),
                        toolCallResult("list_rules", "{\"page\":6}"),
                        textResult("planning complete")
                );
        when(aiToolManager.execute(eq("list_rules"), anyString())).thenReturn("{\"rules\":[]}");
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("All requested rule pages were checked.");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "please list rules across all pages", emitter);

        verify(aiToolManager, org.mockito.Mockito.times(6)).execute(eq("list_rules"), anyString());
        verify(llmChatService).streamReply(anyList(), any(), any());
        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null
                        && "assistant".equalsIgnoreCase(msg.getRole())
                        && msg.getContent() != null
                        && msg.getContent().contains("All requested rule pages were checked.")
                        && !msg.getContent().contains("planning limit")));
        verify(emitter).complete();
    }

    @Test
    void processStreamChat_whenConsecutiveRoundsRepeatExactly_stopsDuplicatesAndStillExplains() throws Exception {
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
        org.mockito.Mockito.doAnswer(invocation -> {
            @SuppressWarnings("unchecked")
            Consumer<String> onDelta = invocation.getArgument(1, Consumer.class);
            onDelta.accept("No rules were found; repeated reads were stopped.");
            return null;
        }).when(llmChatService).streamReply(anyList(), any(), any());

        SseEmitter emitter = mock(SseEmitter.class);

        service.processStreamChat(1L, "s1", "please list rules", emitter);

        verify(aiToolManager, org.mockito.Mockito.times(3)).execute("list_rules", "{}");
        verify(llmChatService).streamReply(anyList(), any(), any());
        verify(messageRepo).saveAndFlush(org.mockito.ArgumentMatchers.argThat(
                msg -> msg != null
                        && "assistant".equalsIgnoreCase(msg.getRole())
                        && msg.getContent() != null
                        && msg.getContent().contains("repeated the exact same tool calls and results")
                        && msg.getContent().contains("No rules were found; repeated reads were stopped.")
                        && !msg.getContent().contains("5-round planning limit")));
        verify(emitter).complete();
    }

    private Object invokeToolLoop(AtomicBoolean disconnected, Set<StreamResponseDto.CommandDto> commandSet) throws Exception {
        return invokeToolLoop(disconnected, commandSet, mock(SseEmitter.class));
    }

    private Object invokeToolLoop(AtomicBoolean disconnected,
                                  Set<StreamResponseDto.CommandDto> commandSet,
                                  SseEmitter emitter) throws Exception {
        return invokeToolLoop(disconnected, commandSet, emitter, new ArrayList<>());
    }

    private Object invokeToolLoop(AtomicBoolean disconnected,
                                  Set<StreamResponseDto.CommandDto> commandSet,
                                  SseEmitter emitter,
                                  List<LlmMessage> messages) throws Exception {
        return executeToolLoopMethod.invoke(
                service,
                1L,
                "s1",
                messages,
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

    private LlmToolSpec toolSpec(String name) {
        return LlmToolSpec.of(name, name,
                new FunctionParameterSchema("object", Map.of(), List.of()));
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
