package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Collections;
import java.util.List;

public final class JsonUtils {

    private static final Logger log = LoggerFactory.getLogger(JsonUtils.class);
    private static final ObjectMapper MAPPER = new ObjectMapper();

    static {
        MAPPER.registerModule(new JavaTimeModule());
        MAPPER.configure(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES, false);
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
        if (obj == null) {
            return "[]";
        }
        try {
            return MAPPER.writeValueAsString(obj);
        } catch (JsonProcessingException e) {
            log.warn("JSON serialization failed, returning empty array", e);
            return "[]";
        }
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
            return defaultValue;
        }
    }

    public static List<String> fromJsonToStringList(String json) {
        if (json == null || json.isBlank()) {
            return Collections.emptyList();
        }
        try {
            return MAPPER.readValue(json, new TypeReference<List<String>>() {});
        } catch (JsonProcessingException e) {
            log.warn("Failed to parse JSON string list", e);
            return Collections.emptyList();
        }
    }
    
    /**
     * 将 JSON 字符串转换为指定类型的 List
     * @param json JSON 字符串
     * @param clazz 元素类型
     * @param <T> 元素类型
     * @return 转换后的 List，失败返回空 List
     */
    public static <T> List<T> fromJsonList(String json, Class<T> clazz) {
        if (json == null || json.isBlank()) {
            return Collections.emptyList();
        }
        try {
            return MAPPER.readValue(json, MAPPER.getTypeFactory()
                    .constructCollectionType(List.class, clazz));
        } catch (JsonProcessingException e) {
            log.warn("Failed to parse JSON list for type {}", clazz.getSimpleName(), e);
            return Collections.emptyList();
        }
    }
}
