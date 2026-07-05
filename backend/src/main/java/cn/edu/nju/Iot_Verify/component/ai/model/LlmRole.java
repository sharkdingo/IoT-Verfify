package cn.edu.nju.Iot_Verify.component.ai.model;

/**
 * Provider-agnostic chat role.
 *
 * <p>Part of the internal LLM domain model. Business code (ChatServiceImpl, AI tools)
 * depends only on these types, never on a vendor SDK. {@code LlmProvider} adapters
 * translate to/from their SDK's own role representation.
 */
public enum LlmRole {
    SYSTEM,
    USER,
    ASSISTANT,
    TOOL
}
