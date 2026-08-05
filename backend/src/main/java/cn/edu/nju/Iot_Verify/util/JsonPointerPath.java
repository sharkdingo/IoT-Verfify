package cn.edu.nju.Iot_Verify.util;

import com.fasterxml.jackson.databind.JsonMappingException;

import java.util.List;

/**
 * Renders a Jackson binding failure's location as a dotted field path, e.g. {@code devices[2].templateName}.
 *
 * <p>This loop was written three times: {@code BoardBatchRequestParser.formatPath} and
 * {@code ModelRequestParser.formatPath} were byte-identical, and {@code GlobalExceptionHandler.jsonPath} was the
 * same loop differing only in what it returns for an empty path. All three exist to tell a user *which field* of
 * their request was rejected, so a change to that format — adding a separator, or handling a new reference kind —
 * had to be made in three places or the same rejection would read differently depending on which layer caught it.
 */
public final class JsonPointerPath {

    private JsonPointerPath() {
    }

    /**
     * The path, or {@code emptyFallback} when the failure carries no field references.
     *
     * <p>The two parsers pass {@code "request"} (the message names a field, so it needs something to name when
     * the failure is the whole body); the exception handler passes {@code ""} because its caller distinguishes
     * "no path" itself.
     */
    public static String of(List<JsonMappingException.Reference> references, String emptyFallback) {
        StringBuilder path = new StringBuilder();
        if (references != null) {
            for (JsonMappingException.Reference reference : references) {
                if (reference.getFieldName() != null) {
                    if (!path.isEmpty()) {
                        path.append('.');
                    }
                    path.append(reference.getFieldName());
                } else if (reference.getIndex() >= 0) {
                    path.append('[').append(reference.getIndex()).append(']');
                }
            }
        }
        return path.isEmpty() ? emptyFallback : path.toString();
    }

    /** The path of a mapping exception, or {@code "request"} when it carries no field references. */
    public static String of(JsonMappingException exception) {
        return of(exception == null ? null : exception.getPath(), "request");
    }
}
