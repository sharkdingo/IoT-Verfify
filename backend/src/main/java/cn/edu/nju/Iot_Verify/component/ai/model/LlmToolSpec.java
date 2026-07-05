package cn.edu.nju.Iot_Verify.component.ai.model;

import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;

/**
 * Provider-agnostic tool/function declaration returned by {@code AiTool.getDefinition()}.
 * Replaces the vendor SDK's {@code ChatTool}/{@code ChatFunction} pair so tools never
 * import an SDK type.
 *
 * <p>{@code parameters} reuses {@link FunctionParameterSchema} (a plain JSON-Schema POJO:
 * type/properties/required); the {@code LlmProvider} adapter serializes it into whatever
 * shape the underlying SDK expects.
 *
 * @param name        function name (snake_case, the dispatch key)
 * @param description human-readable description sent to the model
 * @param parameters  JSON-Schema parameter definition
 */
public record LlmToolSpec(String name, String description, FunctionParameterSchema parameters) {

    public static LlmToolSpec of(String name, String description, FunctionParameterSchema parameters) {
        return new LlmToolSpec(name, description, parameters);
    }
}
