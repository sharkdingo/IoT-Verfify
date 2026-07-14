package cn.edu.nju.Iot_Verify.component.aitool;

import com.fasterxml.jackson.databind.ObjectMapper;

import java.util.LinkedHashMap;
import java.util.Map;

public final class AiToolResponseHelper {

    private static final String SUCCESS_FALLBACK_WARNING =
            "Response serialization failed after the operation reached its response stage.";
    private static final String SUCCESS_FALLBACK_MESSAGE =
            "Result details are unavailable. A mutation may already have been committed; "
                    + "refresh current state before retrying. Do not infer a verification or "
                    + "simulation conclusion from this response.";
    private static final String READ_ONLY_FALLBACK_MESSAGE =
            "Result details are unavailable because response serialization failed. "
                    + "No mutation was requested by this operation; retrying will not duplicate a change.";

    private AiToolResponseHelper() {
    }

    public static String error(ObjectMapper objectMapper, String message, String errorCode, int status) {
        return error(objectMapper, message, errorCode, status, Map.of());
    }

    public static String error(ObjectMapper objectMapper,
                               String message,
                               String errorCode,
                               int status,
                               Map<String, Object> extras) {
        try {
            Map<String, Object> body = new LinkedHashMap<>();
            body.put("error", message);
            body.put("errorCode", errorCode);
            body.put("status", status);
            if (extras != null && !extras.isEmpty()) {
                body.putAll(extras);
            }
            return objectMapper.writeValueAsString(body);
        } catch (Exception ex) {
            return "{\"error\":\"" + escapeJson(message)
                    + "\",\"errorCode\":\"" + escapeJson(errorCode)
                    + "\",\"status\":" + status + "}";
        }
    }

    public static String success(ObjectMapper objectMapper,
                                 Map<String, Object> body,
                                 String fallbackMessage) {
        return success(objectMapper, body, fallbackMessage, true);
    }

    public static String success(ObjectMapper objectMapper,
                                 Map<String, Object> body,
                                 String fallbackMessage,
                                 boolean mutationMayHaveCommitted) {
        try {
            return objectMapper.writeValueAsString(body);
        } catch (Exception ex) {
            return "{\"resultStatus\":\"RESULT_UNAVAILABLE\","
                    + "\"resultAvailable\":false,\"mutationMayHaveCommitted\":"
                    + mutationMayHaveCommitted + ","
                    + "\"message\":\"" + escapeJson(mutationMayHaveCommitted
                    ? SUCCESS_FALLBACK_MESSAGE : READ_ONLY_FALLBACK_MESSAGE)
                    + "\",\"warning\":\"" + escapeJson(SUCCESS_FALLBACK_WARNING) + "\"}";
        }
    }

    public static String success(ObjectMapper objectMapper, String fallbackMessage) {
        return success(objectMapper, Map.of("message", defaultSuccessMessage(fallbackMessage)), fallbackMessage);
    }

    private static String defaultSuccessMessage(String fallbackMessage) {
        if (fallbackMessage == null || fallbackMessage.isBlank()) {
            return "Operation completed successfully.";
        }
        return fallbackMessage;
    }

    private static String escapeJson(String value) {
        if (value == null) {
            return "";
        }
        StringBuilder escaped = new StringBuilder(value.length() + 16);
        for (char ch : value.toCharArray()) {
            switch (ch) {
                case '"' -> escaped.append("\\\"");
                case '\\' -> escaped.append("\\\\");
                case '\b' -> escaped.append("\\b");
                case '\f' -> escaped.append("\\f");
                case '\n' -> escaped.append("\\n");
                case '\r' -> escaped.append("\\r");
                case '\t' -> escaped.append("\\t");
                default -> {
                    if (ch < 0x20) {
                        escaped.append(String.format("\\u%04x", (int) ch));
                    } else {
                        escaped.append(ch);
                    }
                }
            }
        }
        return escaped.toString();
    }
}
