package cn.edu.nju.Iot_Verify.configure;

import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;
import org.springframework.context.annotation.AnnotationConfigApplicationContext;
import org.springframework.core.env.MapPropertySource;
import org.springframework.http.converter.json.Jackson2ObjectMapperBuilder;

import java.time.LocalDateTime;
import java.time.ZoneId;
import java.util.Map;
import java.util.TimeZone;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ApplicationTimeConfigTest {

    @Test
    void localDateTimeSerializationUsesTheConfiguredZoneOffset() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Asia/Shanghai"));

        String json = objectMapper.writeValueAsString(LocalDateTime.of(2026, 7, 22, 14, 30, 5));

        assertEquals("\"2026-07-22T14:30:05+08:00\"", json);
    }

    @Test
    void serializationUsesTheOffsetInEffectAtTheLocalDateTime() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Europe/Paris"));

        assertEquals("\"2026-01-15T12:00:00+01:00\"",
                objectMapper.writeValueAsString(LocalDateTime.of(2026, 1, 15, 12, 0)));
        assertEquals("\"2026-07-15T12:00:00+02:00\"",
                objectMapper.writeValueAsString(LocalDateTime.of(2026, 7, 15, 12, 0)));
    }

    @Test
    void dstGapPreservesTheStoredWallClockValueWithTheEarlierOffset() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Europe/Paris"));

        assertEquals("\"2026-03-29T02:30:00+01:00\"",
                objectMapper.writeValueAsString(LocalDateTime.of(2026, 3, 29, 2, 30)));
    }

    @Test
    void dstOverlapUsesTheEarlierOffsetDeterministically() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Europe/Paris"));

        assertEquals("\"2026-10-25T02:30:00+02:00\"",
                objectMapper.writeValueAsString(LocalDateTime.of(2026, 10, 25, 2, 30)));
    }

    @Test
    void emittedOffsetTimestampRoundTripsToTheStoredLocalDateTime() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Europe/Paris"));
        LocalDateTime stored = LocalDateTime.of(2026, 3, 29, 2, 30);

        String json = objectMapper.writeValueAsString(stored);

        assertEquals(stored, objectMapper.readValue(json, LocalDateTime.class));
    }

    @Test
    void legacyLocalTimestampRemainsReadableButWrongOffsetIsRejected() throws Exception {
        ObjectMapper objectMapper = configuredObjectMapper(ZoneId.of("Asia/Shanghai"));

        assertEquals(LocalDateTime.of(2026, 7, 22, 14, 30),
                objectMapper.readValue("\"2026-07-22T14:30:00\"", LocalDateTime.class));
        assertThrows(com.fasterxml.jackson.databind.JsonMappingException.class,
                () -> objectMapper.readValue("\"2026-07-22T14:30:00Z\"", LocalDateTime.class));
    }

    @Test
    void configuredZoneBecomesTheJvmDefaultBeforeRuntimeBeansAreCreated() {
        TimeZone originalTimeZone = TimeZone.getDefault();
        try (AnnotationConfigApplicationContext context = new AnnotationConfigApplicationContext()) {
            context.getEnvironment().getPropertySources().addFirst(new MapPropertySource(
                    "test-time-zone",
                    Map.of(ApplicationTimeConfig.TIME_ZONE_PROPERTY, "UTC")));
            context.register(ApplicationTimeConfig.class);
            context.refresh();

            assertEquals(ZoneId.of("UTC"), context.getBean("applicationZoneId", ZoneId.class));
            assertEquals(ZoneId.of("UTC"), ZoneId.systemDefault());
        } finally {
            TimeZone.setDefault(originalTimeZone);
        }
    }

    @Test
    void invalidZoneFailsFastWithTheOwningPropertyName() {
        IllegalStateException exception = assertThrows(IllegalStateException.class,
                () -> ApplicationTimeConfig.resolveZoneId("not/a-real-zone"));

        assertTrue(exception.getMessage().contains(ApplicationTimeConfig.TIME_ZONE_PROPERTY));
    }

    private ObjectMapper configuredObjectMapper(ZoneId zoneId) {
        Jackson2ObjectMapperBuilder builder = new Jackson2ObjectMapperBuilder();
        new ApplicationTimeConfig().localDateTimeOffsetSerialization(zoneId).customize(builder);
        return builder.build();
    }
}
