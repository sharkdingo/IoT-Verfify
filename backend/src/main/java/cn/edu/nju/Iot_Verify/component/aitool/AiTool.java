package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;

/**
 * AI 工具策略接口
 * 定义所有工具必须具备的能力：自我描述 + 执行逻辑
 */
public interface AiTool {
    /**
     * 获取工具名称 (例如 "add_device")
     * 作为策略的唯一标识 Key
     */
    String getName();

    /**
     * 获取工具定义 (用于发送给 AI 进行意图识别)。返回与厂商无关的 {@link LlmToolSpec}。
     */
    LlmToolSpec getDefinition();

    /**
     * 执行工具逻辑
     * @param argsJson AI 传回来的参数 JSON 字符串
     * @return 执行结果描述，用于回传给 AI 或显示给用户
     */
    String execute(String argsJson);
}
