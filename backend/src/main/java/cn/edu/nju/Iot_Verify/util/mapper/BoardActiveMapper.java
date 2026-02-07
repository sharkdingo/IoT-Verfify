package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.po.BoardActivePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

/**
 * BoardActive PO 与 DTO 之间的转换映射器
 */
@Component
public class BoardActiveMapper {

    /**
     * BoardActivePo -> BoardActiveDto
     */
    public BoardActiveDto toDto(BoardActivePo po) {
        if (po == null) {
            return null;
        }
        BoardActiveDto dto = new BoardActiveDto();
        dto.setInput(JsonUtils.fromJsonToStringList(po.getInputTabsJson()));
        dto.setStatus(JsonUtils.fromJsonToStringList(po.getStatusTabsJson()));
        return dto;
    }

    /**
     * BoardActiveDto -> BoardActivePo
     */
    public BoardActivePo toEntity(BoardActiveDto dto) {
        if (dto == null) {
            return null;
        }
        BoardActivePo po = new BoardActivePo();
        po.setInputTabsJson(JsonUtils.toJsonOrEmpty(dto.getInput()));
        po.setStatusTabsJson(JsonUtils.toJsonOrEmpty(dto.getStatus()));
        return po;
    }
}
