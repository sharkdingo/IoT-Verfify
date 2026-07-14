package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;

public final class JsonUtils {

    private static final ObjectMapper MAPPER = new ObjectMapper();

    static {
        MAPPER.registerModule(new JavaTimeModule());
        MAPPER.configure(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES, true);
    }

    private JsonUtils() {
    }

    public static String toJson(Object obj) {
        if (obj == null) {
            return null;
        }
        try {
            return MAPPER.writeValueAsString(obj);
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonSerializationFailed(e);
        }
    }

    public static String toJsonOrEmpty(Object obj) {
        return obj == null ? "[]" : toJson(obj);
    }

    public static <T> T fromJson(String json, Class<T> clazz) {
        if (json == null || json.isBlank()) {
            return null;
        }
        try {
            return MAPPER.readValue(json, clazz);
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonDeserializationFailed(e);
        }
    }

    public static <T> T fromJson(String json, TypeReference<T> typeRef) {
        if (json == null || json.isBlank()) {
            return null;
        }
        try {
            return MAPPER.readValue(json, typeRef);
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonDeserializationFailed(e);
        }
    }

    public static <T> T fromJsonOrDefault(String json, TypeReference<T> typeRef, T defaultValue) {
        if (json == null || json.isBlank()) {
            return defaultValue;
        }
        try {
            return MAPPER.readValue(json, typeRef);
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonDeserializationFailed(e);
        }
    }

    public static List<String> fromJsonToStringList(String json) {
        if (json == null || json.isBlank()) {
            return Collections.emptyList();
        }
        try {
            return MAPPER.readValue(json, new TypeReference<List<String>>() {});
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonDeserializationFailed(e);
        }
    }
    
    /**
     * 将 JSON 字符串转换为指定类型的 List
     * @param json JSON 字符串
     * @param clazz 元素类型
     * @param <T> 元素类型
     * @return converted list; malformed non-blank JSON fails closed
     */
    public static <T> List<T> fromJsonList(String json, Class<T> clazz) {
        if (json == null || json.isBlank()) {
            return Collections.emptyList();
        }
        try {
            return MAPPER.readValue(json, MAPPER.getTypeFactory()
                    .constructCollectionType(List.class, clazz));
        } catch (JsonProcessingException e) {
            throw InternalServerException.jsonDeserializationFailed(e);
        }
    }

    /** Adds record-level context without allowing a mapper to replace damaged semantic data. */
    public static <T> T readPersisted(String recordType, Object recordId, String field, Supplier<T> reader) {
        try {
            return reader.get();
        } catch (PersistedDataIntegrityException e) {
            throw e;
        } catch (RuntimeException e) {
            throw new PersistedDataIntegrityException(recordType, recordId, field, e);
        }
    }

    public static <T> T readPersistedRequired(
            String recordType, Object recordId, String field, Supplier<T> reader) {
        T value = readPersisted(recordType, recordId, field, reader);
        if (value == null) {
            throw new PersistedDataIntegrityException(recordType, recordId, field, "value is missing");
        }
        return value;
    }

    /** A persisted JSON column is present only when it contains a nonblank, non-null JSON value. */
    public static <T> T readPersistedJsonOptional(
            String recordType, Object recordId, String field, String json, Supplier<T> reader) {
        if (json == null) return null;
        return readPersistedJsonRequired(recordType, recordId, field, json, reader);
    }

    /** Rejects SQL null, blank text, JSON null, malformed JSON, and unsupported fields. */
    public static <T> T readPersistedJsonRequired(
            String recordType, Object recordId, String field, String json, Supplier<T> reader) {
        if (json == null || json.isBlank()) {
            throw new PersistedDataIntegrityException(recordType, recordId, field, "JSON value is missing");
        }
        return readPersistedRequired(recordType, recordId, field, reader);
    }
}
