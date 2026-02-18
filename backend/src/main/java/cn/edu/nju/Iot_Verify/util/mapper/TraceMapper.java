package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * Trace PO 与 DTO 之间的转换映射器
 */
@Component
public class TraceMapper {

    /**
     * TracePo -> TraceDto
     */
    public TraceDto toDto(TracePo tracePo) {
        if (tracePo == null) {
            return null;
        }
        TraceDto dto = new TraceDto();
        dto.setId(tracePo.getId());
        dto.setUserId(tracePo.getUserId());
        dto.setVerificationTaskId(tracePo.getVerificationTaskId());
        dto.setViolatedSpecId(tracePo.getViolatedSpecId());
        dto.setViolatedSpecJson(tracePo.getViolatedSpecJson());
        dto.setCreatedAt(tracePo.getCreatedAt());

        if (tracePo.getStatesJson() != null && !tracePo.getStatesJson().isEmpty()) {
            List<TraceStateDto> states = JsonUtils.fromJsonOrDefault(
                    tracePo.getStatesJson(),
                    new TypeReference<List<TraceStateDto>>() {},
                    List.of()
            );
            dto.setStates(states);
        } else {
            dto.setStates(List.of());
        }

        return dto;
    }

    /**
     * TraceDto -> TracePo
     */
    public TracePo toEntity(TraceDto traceDto) {
        if (traceDto == null) {
            return null;
        }
        TracePo po = new TracePo();
        po.setId(traceDto.getId());
        po.setUserId(traceDto.getUserId());
        po.setVerificationTaskId(traceDto.getVerificationTaskId());
        po.setViolatedSpecId(traceDto.getViolatedSpecId());
        po.setViolatedSpecJson(traceDto.getViolatedSpecJson());
        po.setCreatedAt(traceDto.getCreatedAt());

        if (traceDto.getStates() != null && !traceDto.getStates().isEmpty()) {
            po.setStatesJson(JsonUtils.toJson(traceDto.getStates()));
        } else {
            po.setStatesJson("[]");
        }

        return po;
    }

    /**
     * List<TracePo> -> List<TraceDto>
     */
    public List<TraceDto> toDtoList(List<TracePo> tracePoList) {
        return tracePoList.stream().map(this::toDto).toList();
    }
}
