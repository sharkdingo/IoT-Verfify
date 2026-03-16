package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;

import java.util.List;
import java.util.Map;

/**
 * AI Tool 公共基类。
 *
 * <p>提取 29 个 Tool 共享的鉴权检查和辅助方法，消除样板代码。
 *
 * <h3>基类职责（有限）</h3>
 * <ul>
 *   <li>{@link #execute(String)} — 仅做 userId 鉴权，不做 JSON 解析，不做兜底 catch-all</li>
 *   <li>{@link #parseArgs(String)} — 可选 JSON 解析工具方法，子类按需调用</li>
 *   <li>errorJson / successJson / safeList / trimToNull — 共用辅助方法</li>
 * </ul>
 */
@Slf4j
public abstract class AbstractAiTool implements AiTool {

    protected final ObjectMapper objectMapper;

    protected AbstractAiTool(ObjectMapper objectMapper) {
        this.objectMapper = objectMapper;
    }

    @Override
    public final String execute(String argsJson) {
        Long userId = UserContextHolder.getUserId();
        if (userId == null) {
            return errorJson("User not logged in", "UNAUTHORIZED", 401);
        }
        return doExecute(userId, argsJson);
    }

    /**
     * 子类实现业务逻辑。
     *
     * @implSpec 实现类必须：
     * <ol>
     *   <li>需要解析参数时调用 {@link #parseArgs(String)} 而非自行 readTree；</li>
     *   <li>包含完整的 try-catch 链并返回 {@link #errorJson}，以保留每个 Tool 特有的错误文案（契约不变）；</li>
     *   <li>catch-all 中使用 Tool 专属文案（如 "Failed to query verification task."），
     *       不得省略——否则异常会穿透到 {@link AiToolManager} 并返回通用 TOOL_EXECUTION_ERROR。</li>
     * </ol>
     *
     * @param userId  已通过鉴权的用户 ID（非 null）
     * @param argsJson 原始 JSON 参数字符串
     * @return JSON 格式的执行结果
     */
    protected abstract String doExecute(Long userId, String argsJson);

    // ── JSON 解析工具方法（子类按需调用，非强制）──────────────────────

    /**
     * 解析 argsJson 为 JsonNode。26 个需要参数的 Tool 在 doExecute() 开头调用。
     * 3 个无参 Tool（BoardOverviewTool、ListTracesTool、ListSimulationTracesTool）不调用，
     * 行为与改造前完全一致。
     *
     * @return 解析后的 JsonNode
     * @throws ArgParseException 包装了 errorJson 返回值，调用方应直接 catch 并 return
     */
    protected final JsonNode parseArgs(String argsJson) throws ArgParseException {
        try {
            return objectMapper.readTree(
                    argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
        } catch (Exception e) {
            throw new ArgParseException(
                    errorJson("Invalid JSON arguments.", "VALIDATION_ERROR", 400));
        }
    }

    /**
     * 仅用于 {@link #parseArgs} 的控制流异常，不是业务异常。
     */
    protected static final class ArgParseException extends Exception {
        private final String errorResponse;

        ArgParseException(String errorResponse) {
            this.errorResponse = errorResponse;
        }

        public String getErrorResponse() {
            return errorResponse;
        }
    }

    // ── 共用 helper ─────────────────────────────────────────────────

    protected final String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }

    protected final String errorJson(String message, String errorCode, int status,
                                     Map<String, Object> extras) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status, extras);
    }

    protected final String successJson(Map<String, Object> body, String fallbackMessage) {
        return AiToolResponseHelper.success(objectMapper, body, fallbackMessage);
    }

    protected final String successJson(String fallbackMessage) {
        return AiToolResponseHelper.success(objectMapper, fallbackMessage);
    }

    protected final <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }

    protected final String trimToNull(String value) {
        if (value == null) return null;
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
