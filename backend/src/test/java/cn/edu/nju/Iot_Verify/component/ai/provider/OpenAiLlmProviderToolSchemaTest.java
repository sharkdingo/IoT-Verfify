package cn.edu.nju.Iot_Verify.component.ai.provider;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.configure.LlmConfig;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.openai.client.OpenAIClient;
import com.openai.models.FunctionParameters;
import com.openai.models.chat.completions.ChatCompletion;
import com.openai.models.chat.completions.ChatCompletionCreateParams;
import com.openai.models.chat.completions.ChatCompletionTool;
import com.openai.services.blocking.ChatService;
import com.openai.services.blocking.chat.ChatCompletionService;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.springframework.test.util.ReflectionTestUtils;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class OpenAiLlmProviderToolSchemaTest {

    @Test
    void chatForwardsRootAndNestedAdditionalPropertiesWithoutLosingConstraints() {
        FunctionParameterSchema nestedClosed = new FunctionParameterSchema(
                "object",
                Map.of("id", Map.of("type", "integer", "minimum", 1)),
                List.of("id"));
        FunctionParameterSchema nestedOpen = new FunctionParameterSchema(
                "object",
                Map.of("label", Map.of("type", "string", "maxLength", 40)),
                List.of());
        nestedOpen.additionalProperties = true;
        FunctionParameterSchema closedRoot = new FunctionParameterSchema(
                "object",
                Map.of(
                        "closed", nestedClosed,
                        "open", nestedOpen,
                        "entries", Map.of(
                                "type", "array",
                                "items", nestedClosed,
                                "minItems", 1)),
                List.of("closed", "entries"));
        FunctionParameterSchema openRoot = new FunctionParameterSchema(
                "object", Map.of(), List.of());
        openRoot.additionalProperties = true;

        ChatCompletionService completions = mock(ChatCompletionService.class);
        OpenAiLlmProvider provider = providerWith(completions);
        provider.chat(LlmChatRequest.builder()
                .messages(List.of(LlmMessage.user("use a tool")))
                .tools(List.of(
                        LlmToolSpec.of("closed_tool", "closed", closedRoot),
                        LlmToolSpec.of("open_tool", "open", openRoot)))
                .build());

        ArgumentCaptor<ChatCompletionCreateParams> captor = ArgumentCaptor.forClass(
                ChatCompletionCreateParams.class);
        verify(completions).create(captor.capture());
        List<ChatCompletionTool> tools = captor.getValue().tools().orElseThrow();

        FunctionParameters closedParameters = tools.get(0).asFunction().function()
                .parameters().orElseThrow();
        assertFalse(closedParameters._additionalProperties()
                .get("additionalProperties").convert(Boolean.class));
        JsonNode required = closedParameters._additionalProperties()
                .get("required").convert(JsonNode.class);
        assertEquals(List.of("closed", "entries"), List.of(
                required.get(0).asText(), required.get(1).asText()));

        JsonNode properties = closedParameters._additionalProperties()
                .get("properties").convert(JsonNode.class);
        assertEquals("object", properties.path("closed").path("type").asText());
        assertFalse(properties.path("closed").path("additionalProperties").asBoolean(true));
        assertEquals(1, properties.path("closed").path("properties")
                .path("id").path("minimum").asInt());
        assertEquals("id", properties.path("closed").path("required").get(0).asText());
        assertTrue(properties.path("open").path("additionalProperties").asBoolean(false));
        assertEquals(40, properties.path("open").path("properties")
                .path("label").path("maxLength").asInt());
        assertFalse(properties.path("entries").path("items")
                .path("additionalProperties").asBoolean(true));
        assertEquals(1, properties.path("entries").path("minItems").asInt());

        FunctionParameters openParameters = tools.get(1).asFunction().function()
                .parameters().orElseThrow();
        assertTrue(openParameters._additionalProperties()
                .get("additionalProperties").convert(Boolean.class));
    }

    private OpenAiLlmProvider providerWith(ChatCompletionService completions) {
        OpenAIClient client = mock(OpenAIClient.class);
        ChatService chatService = mock(ChatService.class);
        ChatCompletion completion = mock(ChatCompletion.class);
        when(client.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.create(any(ChatCompletionCreateParams.class))).thenReturn(completion);
        when(completion.choices()).thenReturn(List.of());

        LlmConfig config = new LlmConfig();
        config.setModel("mock-model");
        OpenAiLlmProvider provider = new OpenAiLlmProvider(config);
        ReflectionTestUtils.setField(provider, "client", client);
        return provider;
    }
}
