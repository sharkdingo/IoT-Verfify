package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.provider.LlmProvider;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.util.List;

/**
 * Facade for one-shot (system + user) prompt completions that return text.
 *
 * <p>Template Method for the identical "build system+user request → call model → read text"
 * pattern the recommend/duplicate-check AI tools all repeated against the raw SDK. Those tools
 * now depend only on this facade and the domain model, not on any LLM client or SDK.
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class PromptCompletionService {

    private final LlmProvider llmProvider;

    /**
     * Run a single system+user completion and return the assistant text.
     *
     * @param systemPrompt system role content
     * @param userPrompt   user role content
     * @param temperature  sampling temperature
     * @param maxTokens    max completion tokens
     * @return the assistant's text content, or empty string if the model returned nothing
     */
    public String complete(String systemPrompt, String userPrompt, double temperature, int maxTokens) {
        LlmChatRequest request = LlmChatRequest.builder()
                .messages(List.of(
                        LlmMessage.system(systemPrompt),
                        LlmMessage.user(userPrompt)))
                .temperature(temperature)
                .maxTokens(maxTokens)
                .build();

        LlmChatResponse response = llmProvider.chat(request);
        return response.text();
    }
}
