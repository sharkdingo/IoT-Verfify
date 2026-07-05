package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import cn.edu.nju.Iot_Verify.util.SmvConstants;

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
        dto.setRequestJson(tracePo.getRequestJson());
        dto.setCreatedAt(tracePo.getCreatedAt());

        // Derive the verification context flags (attack/intensity/privacy) from the stored request
        // snapshot so the frontend can label a historical trace with the parameters it was run under,
        // instead of reading the current (possibly-changed) verification form. requestJson is @JsonIgnore
        // so these derived fields are the only way the client sees them.
        applyRequestContext(dto, tracePo.getRequestJson());

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
     * Parse the verification-context flags from the request snapshot JSON and set them on the DTO.
     * Best-effort: a missing/legacy/unparseable snapshot leaves the derived fields null (the frontend
     * then simply omits the labels), so this must never throw.
     */
    private void applyRequestContext(TraceDto dto, String requestJson) {
        if (requestJson == null || requestJson.isBlank()) {
            return;
        }
        VerificationRequestDto req;
        try {
            req = JsonUtils.fromJson(requestJson, VerificationRequestDto.class);
        } catch (Exception e) {
            return;
        }
        if (req == null) {
            return;
        }
        dto.setAttack(req.isAttack());
        dto.setIntensity(req.getIntensity());
        dto.setEnablePrivacy(req.isEnablePrivacy());
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
        po.setViolatedSpecId(traceDto.getViolatedSpecId() != null
                ? traceDto.getViolatedSpecId()
                : SmvConstants.UNKNOWN_VIOLATED_SPEC_ID);
        po.setViolatedSpecJson(traceDto.getViolatedSpecJson());
        po.setRequestJson(traceDto.getRequestJson());
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
