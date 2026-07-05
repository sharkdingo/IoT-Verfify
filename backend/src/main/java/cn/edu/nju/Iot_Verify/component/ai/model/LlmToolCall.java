package cn.edu.nju.Iot_Verify.component.ai.model;

/**
 * A single tool/function call requested by the model, in provider-agnostic form.
 *
 * @param id           provider-assigned tool-call id (echoed back on the TOOL result message)
 * @param name         function name the model wants to invoke
 * @param argumentsJson raw JSON arguments string produced by the model (may be empty, never null)
 */
public record LlmToolCall(String id, String name, String argumentsJson) {

    public LlmToolCall {
        id = id == null ? "" : id;
        name = name == null ? "" : name;
        argumentsJson = (argumentsJson == null || argumentsJson.isBlank()) ? "{}" : argumentsJson;
    }
}
