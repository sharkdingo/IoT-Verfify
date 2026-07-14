package cn.edu.nju.Iot_Verify.configure;

import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyRequestDto;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.exc.UnrecognizedPropertyException;
import org.junit.jupiter.api.Test;
import org.springframework.http.converter.json.Jackson2ObjectMapperBuilder;

import static org.junit.jupiter.api.Assertions.assertThrows;

class JacksonConfigTest {

    private final ObjectMapper objectMapper = configuredObjectMapper();

    @Test
    void boardMutationDtosRejectUnknownFieldsInsteadOfSilentlyDroppingSemantics() {
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"name\":\"temperature\",\"value\":\"20\",\"truust\":\"untrusted\"}",
                BoardEnvironmentVariableDto.class));
    }

    @Test
    void fixRequestsRejectUnknownPreferenceFields() {
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"preferredRangeSelection\":[]}", FixRequestDto.class));
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"preferredRanges\":{\"r0_c0\":{\"lower\":1,\"upper\":10}}}", FixRequestDto.class));
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"strategy\":\"parameter\",\"preferredRanges\":{}}", FixApplyRequestDto.class));
    }

    @Test
    void authAndChatRequestsDoNotSilentlyDropMisspelledFields() {
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"identifier\":\"user\",\"password\":\"secret\",\"rememberMe\":true}",
                LoginRequestDto.class));
        assertThrows(UnrecognizedPropertyException.class, () -> objectMapper.readValue(
                "{\"sessionId\":\"session-1\",\"content\":\"hello\",\"boardContex\":{}}",
                ChatRequestDto.class));
    }

    private ObjectMapper configuredObjectMapper() {
        Jackson2ObjectMapperBuilder builder = new Jackson2ObjectMapperBuilder();
        new JacksonConfig().strictJsonScalarCoercion().customize(builder);
        return builder.build();
    }
}
