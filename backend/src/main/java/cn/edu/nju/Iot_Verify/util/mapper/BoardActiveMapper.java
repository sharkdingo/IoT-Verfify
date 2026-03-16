package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.po.BoardActivePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

import java.util.List;

@Component
public class BoardActiveMapper {

    private static final List<String> DEFAULT_INPUT_TABS = List.of("devices", "rules", "specs");
    private static final List<String> DEFAULT_STATUS_TABS = List.of("devices", "edges", "specs");

    public BoardActiveDto toDto(BoardActivePo po) {
        BoardActiveDto dto = new BoardActiveDto();
        if (po == null) {
            dto.setInput(DEFAULT_INPUT_TABS);
            dto.setStatus(DEFAULT_STATUS_TABS);
            return dto;
        }
        dto.setInput(JsonUtils.fromJsonToStringList(po.getInputTabsJson()));
        dto.setStatus(JsonUtils.fromJsonToStringList(po.getStatusTabsJson()));
        return dto;
    }

    public BoardActivePo toEntity(BoardActiveDto active, Long id, Long userId) {
        return BoardActivePo.builder()
                .id(id)
                .userId(userId)
                .inputTabsJson(JsonUtils.toJsonOrEmpty(active.getInput()))
                .statusTabsJson(JsonUtils.toJsonOrEmpty(active.getStatus()))
                .build();
    }
}
