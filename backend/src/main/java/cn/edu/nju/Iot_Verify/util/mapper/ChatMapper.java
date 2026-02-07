package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * Chat PO 相关的转换映射器
 */
@Component
public class ChatMapper {

    /**
     * ChatMessagePo -> DTO (简化版响应)
     */
    public cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto toChatMessageDto(ChatMessagePo chatMessagePo) {
        if (chatMessagePo == null) {
            return null;
        }
        cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto dto = new cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto();
        dto.setId(chatMessagePo.getId());
        dto.setSessionId(chatMessagePo.getSessionId());
        dto.setRole(chatMessagePo.getRole());
        dto.setContent(chatMessagePo.getContent());
        dto.setCreatedAt(chatMessagePo.getCreatedAt());
        return dto;
    }

    /**
     * List<ChatMessagePo> -> List<ChatMessageResponseDto>
     */
    public List<cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto> toChatMessageDtoList(List<ChatMessagePo> list) {
        return list.stream().map(this::toChatMessageDto).toList();
    }

    /**
     * ChatSessionPo -> DTO (简化版响应)
     */
    public cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto toChatSessionDto(ChatSessionPo chatSessionPo) {
        if (chatSessionPo == null) {
            return null;
        }
        cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto dto = new cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto();
        dto.setId(chatSessionPo.getId());
        dto.setUserId(chatSessionPo.getUserId());
        dto.setTitle(chatSessionPo.getTitle());
        dto.setCreatedAt(chatSessionPo.getCreatedAt());
        dto.setUpdatedAt(chatSessionPo.getUpdatedAt());
        return dto;
    }

    /**
     * List<ChatSessionPo> -> List<ChatSessionResponseDto>
     */
    public List<cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto> toChatSessionDtoList(List<ChatSessionPo> list) {
        return list.stream().map(this::toChatSessionDto).toList();
    }
}
