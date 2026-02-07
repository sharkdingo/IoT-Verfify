package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.po.TracePo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.time.LocalDateTime;
import java.util.Collections;
import java.util.List;

@Slf4j
@Component
@RequiredArgsConstructor
public class TraceMapper {
    
    private final ObjectMapper objectMapper;
    
    /**
     * TraceDto 转换为 TracePo
     */
    public TracePo toPo(TraceDto dto) {
        if (dto == null) {
            return null;
        }
        try {
            return TracePo.builder()
                    .id(dto.getId())
                    .userId(dto.getUserId())
                    .verificationTaskId(dto.getVerificationTaskId())
                    .violatedSpecId(dto.getViolatedSpecId())
                    .violatedSpecJson(dto.getViolatedSpecJson())
                    .statesJson(objectMapper.writeValueAsString(dto.getStates()))
                    .createdAt(dto.getCreatedAt() != null ? dto.getCreatedAt() : LocalDateTime.now())
                    .build();
        } catch (Exception e) {
            log.error("Failed to convert TraceDto to TracePo", e);
            return null;
        }
    }
    
    /**
     * TracePo 转换为 TraceDto
     */
    public TraceDto fromPo(TracePo po) {
        if (po == null) {
            return null;
        }
        try {
            List<TraceStateDto> states = objectMapper.readValue(
                    po.getStatesJson(), 
                    new TypeReference<List<TraceStateDto>>() {}
            );
            
            return TraceDto.builder()
                    .id(po.getId())
                    .userId(po.getUserId())
                    .verificationTaskId(po.getVerificationTaskId())
                    .violatedSpecId(po.getViolatedSpecId())
                    .violatedSpecJson(po.getViolatedSpecJson())
                    .states(states)
                    .createdAt(po.getCreatedAt())
                    .build();
        } catch (Exception e) {
            log.error("Failed to convert TracePo to TraceDto", e);
            return null;
        }
    }
    
    /**
     * List<TracePo> 转换为 List<TraceDto>
     */
    public List<TraceDto> fromPoList(List<TracePo> poList) {
        if (poList == null || poList.isEmpty()) {
            return Collections.emptyList();
        }
        return poList.stream()
                .map(this::fromPo)
                    .toList();
    }
}
