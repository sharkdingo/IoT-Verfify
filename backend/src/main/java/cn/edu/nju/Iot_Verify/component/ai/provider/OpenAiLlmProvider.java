package cn.edu.nju.Iot_Verify.component.ai.provider;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.LlmRequestControl;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.configure.LlmConfig;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.openai.client.OpenAIClient;
import com.openai.client.okhttp.OpenAIOkHttpClient;
import com.openai.core.JsonValue;
import com.openai.errors.OpenAIServiceException;
import com.openai.core.http.StreamResponse;
import com.openai.models.FunctionDefinition;
import com.openai.models.FunctionParameters;
import com.openai.models.chat.completions.ChatCompletion;
import com.openai.models.chat.completions.ChatCompletionAssistantMessageParam;
import com.openai.models.chat.completions.ChatCompletionChunk;
import com.openai.models.chat.completions.ChatCompletionCreateParams;
import com.openai.models.chat.completions.ChatCompletionFunctionTool;
import com.openai.models.chat.completions.ChatCompletionMessage;
import com.openai.models.chat.completions.ChatCompletionMessageFunctionToolCall;
import com.openai.models.chat.completions.ChatCompletionMessageParam;
import com.openai.models.chat.completions.ChatCompletionMessageToolCall;
import com.openai.models.chat.completions.ChatCompletionSystemMessageParam;
import com.openai.models.chat.completions.ChatCompletionToolMessageParam;
import com.openai.models.chat.completions.ChatCompletionUserMessageParam;
import jakarta.annotation.PostConstruct;
import jakarta.annotation.PreDestroy;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BooleanSupplier;
import java.util.function.Consumer;
import java.util.stream.Stream;
import java.util.concurrent.CancellationException;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;

/**
 * OpenAI-compatible {@link LlmProvider} implementation and the sole anti-corruption layer
 * between the application and the {@code com.openai:openai-java} SDK. All SDK imports live
 * here; the rest of the codebase sees only {@code component.ai.model} types.
 *
 * <p>Works against any endpoint speaking the OpenAI chat-completions protocol (official API,
 * gateways, relays) via {@code llm.base-url}.
 *
 * <p>Registered only when {@code llm.provider=openai} (the default), leaving room for
 * additional providers without touching this class.
 */
@Slf4j
@Component
@org.springframework.boot.autoconfigure.condition.ConditionalOnProperty(
        prefix = "llm", name = "provider", havingValue = "openai", matchIfMissing = true)
public class OpenAiLlmProvider implements LlmProvider {

    private static final int MAX_REASONING_SUMMARY_CHARS = 2000;
    private static final List<String> SAFE_REASONING_SUMMARY_FIELDS = List.of(
            "reasoning_summary",
            "reasoningSummary",
            "reasoning_summary_content",
            "analysis_summary",
            "analysisSummary");

    private final LlmConfig config;
    private OpenAIClient client;

    public OpenAiLlmProvider(LlmConfig config) {
        this.config = config;
    }

    @PostConstruct
    public void init() {
        this.client = OpenAIOkHttpClient.builder()
                .apiKey(config.getApiKey())
                .baseUrl(config.getBaseUrl())
                .putHeader("Accept-Charset", "utf-8")
                .timeout(Duration.ofMinutes(config.getTimeoutMinutes()))
                .build();
        log.info("OpenAiLlmProvider initialized: model={}", config.getModel());
    }

    @PreDestroy
    public void destroy() {
        if (client != null) {
            try {
                client.close();
                log.info("OpenAiLlmProvider client closed");
            } catch (Exception e) {
                log.warn("Error closing OpenAI client: exception={}", e.getClass().getName());
            }
        }
    }

    // ── LlmProvider ──────────────────────────────────────────────────────

    @Override
    public LlmChatResponse chat(LlmChatRequest request) {
        ChatCompletionCreateParams params = toParams(request, false);
        try {
            return parseResponse(client.chat().completions().create(params));
        } catch (Exception e) {
            logProviderError("OpenAI chat completion failed", e);
            throw ServiceUnavailableException.aiService(e);
        }
    }

    @Override
    public LlmChatResponse chat(LlmChatRequest request, LlmRequestControl control) {
        if (control.isCancellationRequested()) return LlmChatResponse.empty();
        ChatCompletionCreateParams params = toParams(request, false);
        CompletableFuture<ChatCompletion> future;
        try {
            future = client.async().chat().completions().create(params);
        } catch (Exception e) {
            if (control.isCancellationRequested()) return LlmChatResponse.empty();
            logProviderError("OpenAI chat completion failed", e);
            throw ServiceUnavailableException.aiService(e);
        }
        AutoCloseable cancellation = () -> future.cancel(true);
        control.attach(cancellation);
        try {
            return parseResponse(future.get());
        } catch (CancellationException e) {
            if (control.isCancellationRequested()) return LlmChatResponse.empty();
            throw e;
        } catch (InterruptedException e) {
            future.cancel(true);
            Thread.currentThread().interrupt();
            return LlmChatResponse.empty();
        } catch (ExecutionException e) {
            if (control.isCancellationRequested()) return LlmChatResponse.empty();
            Throwable cause = e.getCause() == null ? e : e.getCause();
            Exception providerFailure = cause instanceof Exception exception
                    ? exception
                    : new RuntimeException(cause);
            logProviderError("OpenAI chat completion failed", providerFailure);
            throw ServiceUnavailableException.aiService(providerFailure);
        } catch (Exception e) {
            if (control.isCancellationRequested()) return LlmChatResponse.empty();
            logProviderError("OpenAI chat completion failed", e);
            throw ServiceUnavailableException.aiService(e);
        } finally {
            control.detach(cancellation);
        }
    }

    @Override
    public void streamChat(LlmChatRequest request, Consumer<String> onDelta, BooleanSupplier shouldStop) {
        streamChat(request, onDelta, shouldStop, new LlmRequestControl());
    }

    @Override
    public void streamChat(LlmChatRequest request,
                           Consumer<String> onDelta,
                           BooleanSupplier shouldStop,
                           LlmRequestControl control) {
        if (control.isCancellationRequested()) return;
        ChatCompletionCreateParams params = toParams(request, true);
        StreamResponse<ChatCompletionChunk> stream = null;
        AutoCloseable cancellation = null;
        try {
            stream = client.chat().completions().createStreaming(params);
            cancellation = stream::close;
            control.attach(cancellation);
            Stream<ChatCompletionChunk> chunks = stream.stream();
            for (ChatCompletionChunk chunk : (Iterable<ChatCompletionChunk>) chunks::iterator) {
                if (shouldStop.getAsBoolean() || control.isCancellationRequested()) {
                    break;
                }
                if (chunk.choices().isEmpty()) {
                    continue;
                }
                chunk.choices().get(0).delta().content()
                        .filter(delta -> !delta.isEmpty())
                        .ifPresent(onDelta);
            }
        } catch (Exception e) {
            if (shouldStop.getAsBoolean() || control.isCancellationRequested()) {
                log.info("OpenAI streaming chat stopped after cancellation: exception={}",
                        e.getClass().getName());
                return;
            }
            logProviderError("OpenAI streaming chat error", e);
            throw ServiceUnavailableException.aiService(e);
        } finally {
            control.detach(cancellation);
            if (stream != null) stream.close();
        }
    }

    // ── domain → SDK ─────────────────────────────────────────────────────

    private ChatCompletionCreateParams toParams(LlmChatRequest request, boolean streaming) {
        String model = (request.model() != null && !request.model().isBlank())
                ? request.model() : config.getModel();

        ChatCompletionCreateParams.Builder builder = ChatCompletionCreateParams.builder()
                .model(model);

        for (LlmMessage msg : request.messages()) {
            builder.addMessage(toMessageParam(msg));
        }

        if (!streaming && request.hasTools()) {
            for (LlmToolSpec spec : request.tools()) {
                builder.addTool(toFunctionTool(spec));
            }
        }
        if (request.temperature() != null) {
            builder.temperature(request.temperature());
        }
        if (request.maxTokens() != null) {
            builder.maxCompletionTokens(request.maxTokens().longValue());
        }
        return builder.build();
    }

    private ChatCompletionMessageParam toMessageParam(LlmMessage msg) {
        return switch (msg.role()) {
            case SYSTEM -> ChatCompletionMessageParam.ofSystem(
                    ChatCompletionSystemMessageParam.builder().content(msg.content()).build());
            case USER -> ChatCompletionMessageParam.ofUser(
                    ChatCompletionUserMessageParam.builder().content(msg.content()).build());
            case TOOL -> ChatCompletionMessageParam.ofTool(
                    ChatCompletionToolMessageParam.builder()
                            .toolCallId(msg.toolCallId() == null ? "" : msg.toolCallId())
                            .content(msg.content())
                            .build());
            case ASSISTANT -> ChatCompletionMessageParam.ofAssistant(toAssistantParam(msg));
        };
    }

    private ChatCompletionAssistantMessageParam toAssistantParam(LlmMessage msg) {
        ChatCompletionAssistantMessageParam.Builder builder = ChatCompletionAssistantMessageParam.builder();
        if (msg.hasToolCalls()) {
            for (LlmToolCall call : msg.toolCalls()) {
                builder.addToolCall(ChatCompletionMessageFunctionToolCall.builder()
                        .id(call.id())
                        .function(ChatCompletionMessageFunctionToolCall.Function.builder()
                                .name(call.name())
                                .arguments(call.argumentsJson())
                                .build())
                        .build());
            }
            // OpenAI requires assistant tool-call messages to omit/empty content.
        } else {
            builder.content(msg.content());
        }
        return builder.build();
    }

    private ChatCompletionFunctionTool toFunctionTool(LlmToolSpec spec) {
        FunctionParameters.Builder parametersBuilder = FunctionParameters.builder();
        toJsonSchemaObject(spec.parameters()).forEach((key, value) ->
                parametersBuilder.putAdditionalProperty(key, JsonValue.from(value)));
        FunctionParameters parameters = parametersBuilder.build();

        FunctionDefinition definition = FunctionDefinition.builder()
                .name(spec.name())
                .description(spec.description() == null ? "" : spec.description())
                .parameters(parameters)
                .build();

        return ChatCompletionFunctionTool.builder().function(definition).build();
    }

    private Map<String, Object> toJsonSchemaObject(FunctionParameterSchema schema) {
        Map<String, Object> json = new LinkedHashMap<>();
        json.put("type", schema.type);
        json.put("properties", normalizeJsonSchemaValue(schema.properties));
        json.put("required", normalizeJsonSchemaValue(schema.required));
        json.put("additionalProperties", schema.additionalProperties);
        return json;
    }

    private Object normalizeJsonSchemaValue(Object value) {
        if (value instanceof FunctionParameterSchema nestedSchema) {
            return toJsonSchemaObject(nestedSchema);
        }
        if (value instanceof Map<?, ?> map) {
            Map<String, Object> normalized = new LinkedHashMap<>();
            map.forEach((key, nestedValue) -> normalized.put(
                    String.valueOf(key), normalizeJsonSchemaValue(nestedValue)));
            return normalized;
        }
        if (value instanceof List<?> list) {
            return list.stream().map(this::normalizeJsonSchemaValue).toList();
        }
        return value;
    }

    // ── SDK → domain ─────────────────────────────────────────────────────

    private LlmChatResponse parseResponse(ChatCompletion completion) {
        if (completion.choices().isEmpty()) {
            return LlmChatResponse.empty();
        }
        ChatCompletionMessage message = completion.choices().get(0).message();

        List<LlmToolCall> toolCalls = message.toolCalls()
                .map(this::toDomainToolCalls)
                .orElseGet(List::of);
        String reasoningSummary = safeReasoningSummary(message);
        if (!toolCalls.isEmpty()) {
            return new LlmChatResponse(
                    message.content().orElse(""), toolCalls, reasoningSummary);
        }
        return new LlmChatResponse(message.content().orElse(""), List.of(), reasoningSummary);
    }

    private String safeReasoningSummary(ChatCompletionMessage message) {
        Map<String, JsonValue> additional = message._additionalProperties();
        for (String field : SAFE_REASONING_SUMMARY_FIELDS) {
            JsonValue value = additional.get(field);
            if (value == null) continue;
            try {
                com.fasterxml.jackson.databind.JsonNode node = value.convert(
                        com.fasterxml.jackson.databind.JsonNode.class);
                String summary = summaryText(node);
                if (summary != null) return summary;
            } catch (RuntimeException e) {
                log.debug("Ignoring unreadable safe reasoning summary field {}", field);
            }
        }
        // Deliberately ignore reasoning_content and analysis: compatible endpoints commonly
        // use those names for private chain-of-thought rather than a user-safe summary.
        return "";
    }

    private String summaryText(com.fasterxml.jackson.databind.JsonNode node) {
        if (node == null || node.isNull()) return null;
        String value = null;
        if (node.isTextual()) {
            value = node.asText();
        } else if (node.isObject()) {
            for (String key : List.of("summary", "text", "content")) {
                if (node.path(key).isTextual()) {
                    value = node.path(key).asText();
                    break;
                }
            }
        }
        if (value == null || value.isBlank()) return null;
        String normalized = value.trim();
        return normalized.length() <= MAX_REASONING_SUMMARY_CHARS
                ? normalized
                : normalized.substring(0, MAX_REASONING_SUMMARY_CHARS);
    }

    private List<LlmToolCall> toDomainToolCalls(List<ChatCompletionMessageToolCall> sdkCalls) {
        List<LlmToolCall> result = new ArrayList<>();
        for (ChatCompletionMessageToolCall call : sdkCalls) {
            if (!call.isFunction()) {
                continue; // custom tools are not used by this application
            }
            ChatCompletionMessageFunctionToolCall fn = call.asFunction();
            result.add(new LlmToolCall(fn.id(), fn.function().name(), fn.function().arguments()));
        }
        return result;
    }

    private void logProviderError(String message, Exception e) {
        if (e instanceof OpenAIServiceException serviceException) {
            log.error("{}: status={}, exception={}",
                    message,
                    serviceException.statusCode(),
                    e.getClass().getSimpleName());
            return;
        }
        log.error("{}: exception={}", message, e.getClass().getName());
    }
}
