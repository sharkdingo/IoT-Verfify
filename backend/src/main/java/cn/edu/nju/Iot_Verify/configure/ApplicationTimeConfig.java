package cn.edu.nju.Iot_Verify.configure;

import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.core.JsonToken;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.databind.DeserializationContext;
import com.fasterxml.jackson.databind.JsonDeserializer;
import com.fasterxml.jackson.databind.JsonSerializer;
import com.fasterxml.jackson.databind.SerializerProvider;
import org.springframework.beans.factory.config.BeanFactoryPostProcessor;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.boot.autoconfigure.jackson.Jackson2ObjectMapperBuilderCustomizer;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.core.env.Environment;

import java.io.IOException;
import java.time.DateTimeException;
import java.time.LocalDateTime;
import java.time.OffsetDateTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.TimeZone;

@Configuration(proxyBeanMethods = false)
public class ApplicationTimeConfig {

    static final String TIME_ZONE_PROPERTY = "iot-verify.time-zone";
    static final String DEFAULT_TIME_ZONE = "Asia/Shanghai";

    @Bean
    static BeanFactoryPostProcessor configureJvmDefaultTimeZone(Environment environment) {
        ZoneId zoneId = resolveZoneId(environment.getProperty(TIME_ZONE_PROPERTY, DEFAULT_TIME_ZONE));
        return beanFactory -> TimeZone.setDefault(TimeZone.getTimeZone(zoneId));
    }

    @Bean("applicationZoneId")
    ZoneId applicationZoneId(Environment environment) {
        return resolveZoneId(environment.getProperty(TIME_ZONE_PROPERTY, DEFAULT_TIME_ZONE));
    }

    @Bean
    Jackson2ObjectMapperBuilderCustomizer localDateTimeOffsetSerialization(
            @Qualifier("applicationZoneId") ZoneId applicationZoneId) {
        JsonSerializer<LocalDateTime> serializer = new LocalDateTimeOffsetSerializer(applicationZoneId);
        JsonDeserializer<LocalDateTime> deserializer = new LocalDateTimeOffsetDeserializer(applicationZoneId);
        return builder -> builder
                .timeZone(TimeZone.getTimeZone(applicationZoneId))
                .serializerByType(LocalDateTime.class, serializer)
                .deserializerByType(LocalDateTime.class, deserializer);
    }

    static ZoneId resolveZoneId(String configuredZoneId) {
        try {
            return ZoneId.of(configuredZoneId);
        } catch (DateTimeException exception) {
            throw new IllegalStateException(
                    "Invalid " + TIME_ZONE_PROPERTY + " value: " + configuredZoneId,
                    exception);
        }
    }

    private static final class LocalDateTimeOffsetSerializer extends JsonSerializer<LocalDateTime> {
        private final ZoneId zoneId;

        private LocalDateTimeOffsetSerializer(ZoneId zoneId) {
            this.zoneId = zoneId;
        }

        @Override
        public void serialize(LocalDateTime value,
                              JsonGenerator generator,
                              SerializerProvider serializers) throws IOException {
            generator.writeString(DateTimeFormatter.ISO_OFFSET_DATE_TIME.format(
                    value.atOffset(zoneId.getRules().getOffset(value))));
        }
    }

    private static final class LocalDateTimeOffsetDeserializer extends JsonDeserializer<LocalDateTime> {
        private final ZoneId zoneId;

        private LocalDateTimeOffsetDeserializer(ZoneId zoneId) {
            this.zoneId = zoneId;
        }

        @Override
        public LocalDateTime deserialize(JsonParser parser,
                                         DeserializationContext context) throws IOException {
            if (!parser.hasToken(JsonToken.VALUE_STRING)) {
                return (LocalDateTime) context.handleUnexpectedToken(LocalDateTime.class, parser);
            }
            String value = parser.getText().trim();
            try {
                OffsetDateTime offsetDateTime = OffsetDateTime.parse(value, DateTimeFormatter.ISO_OFFSET_DATE_TIME);
                LocalDateTime localDateTime = offsetDateTime.toLocalDateTime();
                ZoneOffset expectedOffset = zoneId.getRules().getOffset(localDateTime);
                if (!expectedOffset.equals(offsetDateTime.getOffset())) {
                    return (LocalDateTime) context.handleWeirdStringValue(
                            LocalDateTime.class,
                            value,
                            "Timestamp offset does not match the configured application time zone");
                }
                return localDateTime;
            } catch (DateTimeParseException ignored) {
                try {
                    return LocalDateTime.parse(value, DateTimeFormatter.ISO_LOCAL_DATE_TIME);
                } catch (DateTimeParseException invalidLocalDateTime) {
                    return (LocalDateTime) context.handleWeirdStringValue(
                            LocalDateTime.class, value, "Expected an ISO-8601 local or offset date-time");
                }
            }
        }
    }
}
