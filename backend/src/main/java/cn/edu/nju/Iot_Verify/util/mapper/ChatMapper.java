package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * Chat PO 相关的转换映射器
 */
@Component
public class ChatMapper {

    public ChatMessageResponseDto toChatMessageDto(ChatMessagePo chatMessagePo) {
        if (chatMessagePo == null) {
            return null;
        }
        ChatMessageResponseDto dto = new ChatMessageResponseDto();
        dto.setId(chatMessagePo.getId());
        dto.setSessionId(chatMessagePo.getSessionId());
        dto.setRole(chatMessagePo.getRole());
        dto.setContent(chatMessagePo.getContent());
        dto.setCreatedAt(chatMessagePo.getCreatedAt());
        return dto;
    }

    public List<ChatMessageResponseDto> toChatMessageDtoList(List<ChatMessagePo> list) {
        return list.stream().map(this::toChatMessageDto).toList();
    }

    public ChatSessionResponseDto toChatSessionDto(ChatSessionPo chatSessionPo) {
        if (chatSessionPo == null) {
            return null;
        }
        ChatSessionResponseDto dto = new ChatSessionResponseDto();
        dto.setId(chatSessionPo.getId());
        dto.setUserId(chatSessionPo.getUserId());
        dto.setTitle(chatSessionPo.getTitle());
        dto.setCreatedAt(chatSessionPo.getCreatedAt());
        dto.setUpdatedAt(chatSessionPo.getUpdatedAt());
        return dto;
    }

    public List<ChatSessionResponseDto> toChatSessionDtoList(List<ChatSessionPo> list) {
        return list.stream().map(this::toChatSessionDto).toList();
    }
}
