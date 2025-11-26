package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.ChatRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.service.ArkService;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

/**
 * 封装豆包（火山方舟 Ark）的调用逻辑
 */
@Service
public class ArkAiChatService {

    private final ArkService arkService;

    /**
     * 这里使用 Endpoint ID / Model ID
     * 登录火山方舟控制台，找到 doubao-seed-1-6-251015 对应的 ep-xxxxxx
     */
    @Value("${ark.model-id}")
    private String modelId;

    public ArkAiChatService(
            @Value("${ark.api-key}") String apiKey,
            @Value("${ark.base-url:https://ark.cn-beijing.volces.com/api/v3}") String baseUrl
    ) {
        this.arkService = ArkService.builder()
                .apiKey(apiKey)
                .baseUrl(baseUrl)
                .build();
    }

    /**
     * 流式对话：
     * @param request   前端传来的 ChatRequest
     * @param onDelta   每生成一段内容就回调一次（只给出新增内容）
     */
    public void streamChat(ChatRequest request, Consumer<String> onDelta) {
        List<ChatMessage> messages = new ArrayList<>();

        // System Prompt：你可以根据项目改成更详细的说明
        messages.add(ChatMessage.builder()
                .role(ChatMessageRole.SYSTEM)
                .content("你是一名擅长物联网设备、形式化验证和代码调试的 AI 助手，回答要尽量简洁清晰。")
                .build());

        // 历史记录 -> messages
        if (request.getHistory() != null) {
            for (ChatRequest.ChatHistoryItem item : request.getHistory()) {
                if (item == null || item.getContent() == null) continue;

                ChatMessageRole role =
                        "assistant".equalsIgnoreCase(item.getRole())
                                ? ChatMessageRole.ASSISTANT
                                : ChatMessageRole.USER;

                messages.add(ChatMessage.builder()
                        .role(role)
                        .content(item.getContent())
                        .build());
            }
        }

        // 当前这轮提问
        if (request.getQuery() != null && !request.getQuery().isEmpty()) {
            messages.add(ChatMessage.builder()
                    .role(ChatMessageRole.USER)
                    .content(request.getQuery())
                    .build());
        }

        ChatCompletionRequest chatCompletionRequest = ChatCompletionRequest.builder()
                .model(modelId)
                .messages(messages)
                .stream(true)
                .build();

        // 调用豆包流式接口，并把生成的内容一块一块回调出去
        arkService.streamChatCompletion(chatCompletionRequest)
                .doOnError(Throwable::printStackTrace)
                .blockingForEach(choice -> {
                    if (choice.getChoices() == null || choice.getChoices().isEmpty()) return;
                    String content = choice.getChoices().get(0).getMessage().getContent().toString();
                    if (content != null && !content.isEmpty()) {
                        onDelta.accept(content);
                    }
                });
    }
}
