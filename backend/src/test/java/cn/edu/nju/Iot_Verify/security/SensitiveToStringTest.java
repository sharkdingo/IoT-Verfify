package cn.edu.nju.Iot_Verify.security;

import cn.edu.nju.Iot_Verify.configure.JwtConfig;
import cn.edu.nju.Iot_Verify.configure.LlmConfig;
import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.DeleteAccountRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceDeleteRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.po.AiSessionStatePo;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

class SensitiveToStringTest {

    private static final String SECRET = "never-log-this-sensitive-value";

    @Test
    void credentialsAndPrivateChatContentAreExcludedFromToString() {
        RegisterRequestDto register = new RegisterRequestDto();
        register.setPassword(SECRET);
        LoginRequestDto login = new LoginRequestDto();
        login.setPassword(SECRET);
        DeleteAccountRequestDto deleteAccount = new DeleteAccountRequestDto();
        deleteAccount.setPassword(SECRET);
        LlmConfig llmConfig = new LlmConfig();
        llmConfig.setApiKey(SECRET);
        JwtConfig jwtConfig = new JwtConfig();
        jwtConfig.setSecret(SECRET);
        AiSessionStatePo aiState = new AiSessionStatePo();
        aiState.setPayloadJson(SECRET);
        ChatMessagePo chatMessage = new ChatMessagePo();
        chatMessage.setContent(SECRET);
        chatMessage.setExecutionTraceJson(SECRET);
        ChatRequestDto chatRequest = new ChatRequestDto();
        chatRequest.setContent(SECRET);
        StreamResponseDto streamResponse = new StreamResponseDto(SECRET);
        StreamResponseDto streamError = StreamResponseDto.error(SECRET);

        assertRedacted(List.of(
                register,
                login,
                deleteAccount,
                AuthResponseDto.builder().token(SECRET).build(),
                UserPo.builder().password(SECRET).build(),
                llmConfig,
                jwtConfig,
                aiState,
                chatMessage,
                chatRequest,
                ChatMessageResponseDto.builder().content(SECRET).build(),
                streamResponse,
                streamError));
    }

    @Test
    void destructiveActionCapabilityTokensAreExcludedFromToString() {
        BoardBatchDto boardBatch = new BoardBatchDto();
        boardBatch.setImpactToken(SECRET);
        DeviceDeleteRequestDto deviceDelete = new DeviceDeleteRequestDto();
        deviceDelete.setImpactToken(SECRET);

        assertRedacted(List.of(
                FixSuggestionDto.builder().suggestionToken(SECRET).build(),
                FixApplyRequestDto.builder().suggestionToken(SECRET).build(),
                DefaultTemplateResetResultDto.builder().impactToken(SECRET).build(),
                BoardReplacementPreviewDto.builder().impactToken(SECRET).build(),
                new DefaultTemplateResetRequestDto(SECRET),
                boardBatch,
                DeviceDeletionResultDto.builder().impactToken(SECRET).build(),
                deviceDelete,
                DeviceTemplateDeletionResultDto.builder().impactToken(SECRET).build(),
                new DeviceTemplateDeletionRequestDto(SECRET)));
    }

    private void assertRedacted(List<?> values) {
        for (Object value : values) {
            assertFalse(value.toString().contains(SECRET), value.getClass().getName());
        }
    }
}
