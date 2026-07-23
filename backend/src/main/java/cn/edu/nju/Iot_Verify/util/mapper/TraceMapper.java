package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.projection.TraceSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.TraceStateIntegrity;
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
        dto.setViolatedSpec(JsonUtils.readPersistedRequired("verification trace", tracePo.getId(),
                "violatedSpecJson", () -> JsonUtils.fromJson(tracePo.getViolatedSpecJson(), SpecificationDto.class)));
        dto.setCheckedExpression(tracePo.getCheckedExpression());
        dto.setRequestJson(tracePo.getRequestJson());
        dto.setTemplateSnapshotsJson(tracePo.getTemplateSnapshotsJson());
        dto.setModelSnapshot(JsonUtils.readPersistedRequired("verification trace", tracePo.getId(),
                "modelSnapshotJson", () -> JsonUtils.fromJson(
                        tracePo.getModelSnapshotJson(), ModelRunSnapshotDto.class)));
        dto.setDisabledRuleCount(tracePo.getDisabledRuleCount());
        dto.setSkippedSpecCount(tracePo.getSkippedSpecCount());
        dto.setGenerationIssues(JsonUtils.readPersisted("verification trace", tracePo.getId(),
                "generationIssuesJson", () -> JsonUtils.fromJsonList(
                        tracePo.getGenerationIssuesJson(), ModelGenerationIssueDto.class)));
        dto.setModelComplete((tracePo.getDisabledRuleCount() == null || tracePo.getDisabledRuleCount() == 0)
                && (tracePo.getSkippedSpecCount() == null || tracePo.getSkippedSpecCount() == 0));
        dto.setCreatedAt(tracePo.getCreatedAt());

        applyPersistedModelContext(dto, tracePo);

        List<TraceStateDto> states = JsonUtils.readPersistedRequired("verification trace", tracePo.getId(),
                "statesJson", () -> TraceStateIntegrity.requireValidStates(JsonUtils.fromJson(
                        tracePo.getStatesJson(), new TypeReference<List<TraceStateDto>>() {})));
        if (states.isEmpty()) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", tracePo.getId(), "statesJson", "trace has no states");
        }
        int persistedStateCount = requiredStateCount(tracePo.getId(), tracePo.getStateCount());
        if (states.size() != persistedStateCount) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", tracePo.getId(), "stateCount",
                    "state count does not match statesJson");
        }
        dto.setStates(states);

        return dto;
    }

    private void applyPersistedModelContext(TraceDto dto, TracePo po) {
        if (po.getIsAttack() == null || po.getAttackBudget() == null || po.getEnablePrivacy() == null) {
            return;
        }
        dto.setAttack(po.getIsAttack());
        dto.setAttackBudget(Boolean.TRUE.equals(po.getIsAttack()) ? po.getAttackBudget() : 0);
        dto.setEnablePrivacy(po.getEnablePrivacy());
        if (po.getModelSemanticsJson() != null && !po.getModelSemanticsJson().isBlank()) {
            dto.setModelSemantics(JsonUtils.readPersistedRequired(
                    "verification trace", po.getId(), "modelSemanticsJson",
                    () -> JsonUtils.fromJson(po.getModelSemanticsJson(), ModelSemanticsDto.class)));
        } else if (po.getModeledDeviceAttackPointCount() != null
                && po.getModeledAutomationLinkAttackPointCount() != null
                && po.getModeledFalsifiableReadingDeviceCount() != null) {
            dto.setModelSemantics(ModelSemanticsDto.forRun(
                    Boolean.TRUE.equals(po.getIsAttack()), Boolean.TRUE.equals(po.getEnablePrivacy()),
                    po.getModeledDeviceAttackPointCount(),
                    po.getModeledAutomationLinkAttackPointCount(),
                    po.getModeledFalsifiableReadingDeviceCount()));
        }
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
        po.setViolatedSpecJson(traceDto.getViolatedSpecJson() != null
                ? traceDto.getViolatedSpecJson()
                : JsonUtils.toJson(traceDto.getViolatedSpec()));
        po.setCheckedExpression(traceDto.getCheckedExpression());
        po.setRequestJson(traceDto.getRequestJson());
        po.setTemplateSnapshotsJson(traceDto.getTemplateSnapshotsJson());
        po.setModelSnapshotJson(JsonUtils.toJson(traceDto.getModelSnapshot()));
        po.setModelSemanticsJson(JsonUtils.toJson(traceDto.getModelSemantics()));
        po.setIsAttack(traceDto.getAttack());
        po.setAttackBudget(Boolean.TRUE.equals(traceDto.getAttack()) ? traceDto.getAttackBudget() : 0);
        po.setEnablePrivacy(traceDto.getEnablePrivacy());
        if (traceDto.getModelSemantics() != null) {
            po.setModeledDeviceAttackPointCount(
                    traceDto.getModelSemantics().getModeledDeviceAttackPointCount());
            po.setModeledFalsifiableReadingDeviceCount(
                    traceDto.getModelSemantics().getModeledFalsifiableReadingDeviceCount());
            po.setModeledAutomationLinkAttackPointCount(
                    traceDto.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        }
        po.setDisabledRuleCount(traceDto.getDisabledRuleCount());
        po.setSkippedSpecCount(traceDto.getSkippedSpecCount());
        po.setGenerationIssuesJson(JsonUtils.toJsonOrEmpty(traceDto.getGenerationIssues()));
        po.setCreatedAt(traceDto.getCreatedAt());

        if (traceDto.getStates() != null && !traceDto.getStates().isEmpty()) {
            po.setStatesJson(JsonUtils.toJson(traceDto.getStates()));
            po.setStateCount(traceDto.getStates().size());
        } else {
            po.setStatesJson("[]");
            po.setStateCount(0);
        }

        return po;
    }

    /**
     * List<TracePo> -> List<TraceDto>
     */
    public List<TraceDto> toDtoList(List<TracePo> tracePoList) {
        return tracePoList.stream().map(this::toDto).toList();
    }

    public TraceSummaryDto toSummaryDto(TraceSummaryProjection projection) {
        if (projection == null) return null;
        SpecificationDto violatedSpec = JsonUtils.readPersistedRequired(
                "verification trace", projection.getId(), "violatedSpecJson",
                () -> JsonUtils.fromJson(projection.getViolatedSpecJson(), SpecificationDto.class));
        return TraceSummaryDto.builder()
                .id(projection.getId())
                .verificationTaskId(projection.getVerificationTaskId())
                .violatedSpecId(projection.getViolatedSpecId())
                .violatedSpec(violatedSpec)
                .stateCount(requiredStateCount(projection.getId(), projection.getStateCount()))
                .createdAt(projection.getCreatedAt())
                .dataAvailable(true)
                .build();
    }

    private int requiredStateCount(Long id, Integer stateCount) {
        if (stateCount == null || stateCount < 1) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", id, "stateCount", "trace has no states");
        }
        return stateCount;
    }

}
