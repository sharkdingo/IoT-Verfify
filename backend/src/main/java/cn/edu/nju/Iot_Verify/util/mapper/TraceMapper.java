package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.trace.*;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.projection.TraceSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.PersistedModelContextIntegrity;
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
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(tracePo);
        List<RuleDto> frozenRules = readFrozenRules(
                tracePo.getId(), tracePo.getRequestJson(), context.modelSnapshot().getRuleCount());
        TraceDto dto = new TraceDto();
        dto.setId(tracePo.getId());
        dto.setUserId(tracePo.getUserId());
        dto.setVerificationTaskId(requireVerificationTaskId(tracePo.getId(), tracePo.getVerificationTaskId()));
        dto.setViolatedSpecId(tracePo.getViolatedSpecId());
        dto.setViolatedSpecJson(tracePo.getViolatedSpecJson());
        dto.setViolatedSpec(JsonUtils.readPersistedRequired("verification trace", tracePo.getId(),
                "violatedSpecJson", () -> JsonUtils.fromJson(tracePo.getViolatedSpecJson(), SpecificationDto.class)));
        dto.setCheckedExpression(tracePo.getCheckedExpression());
        dto.setRequestJson(tracePo.getRequestJson());
        dto.setTemplateSnapshotsJson(tracePo.getTemplateSnapshotsJson());
        dto.setModelSnapshot(context.modelSnapshot());
        dto.setDisabledRuleCount(tracePo.getDisabledRuleCount());
        dto.setSkippedSpecCount(tracePo.getSkippedSpecCount());
        dto.setGenerationIssues(JsonUtils.readPersisted("verification trace", tracePo.getId(),
                "generationIssuesJson", () -> JsonUtils.fromJsonList(
                        tracePo.getGenerationIssuesJson(), ModelGenerationIssueDto.class)));
        dto.setModelComplete((tracePo.getDisabledRuleCount() == null || tracePo.getDisabledRuleCount() == 0)
                && (tracePo.getSkippedSpecCount() == null || tracePo.getSkippedSpecCount() == 0));
        dto.setCreatedAt(tracePo.getCreatedAt());

        applyPersistedModelContext(dto, context);

        dto.setStates(readRequiredStates(
                tracePo.getId(), tracePo.getStatesJson(), tracePo.getStateCount(), frozenRules));

        return dto;
    }

    private void applyPersistedModelContext(
            TraceDto dto, PersistedModelContextIntegrity.ValidatedContext context) {
        dto.setAttack(context.isAttack());
        dto.setAttackBudget(context.attackBudget());
        dto.setEnablePrivacy(context.enablePrivacy());
        dto.setModelSemantics(context.modelSemantics());
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
        po.setVerificationTaskId(requireVerificationTaskId(traceDto.getId(), traceDto.getVerificationTaskId()));
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
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(projection);
        List<RuleDto> frozenRules = readFrozenRules(
                projection.getId(), projection.getRequestJson(), context.modelSnapshot().getRuleCount());
        List<TraceStateDto> states = readRequiredStates(
                projection.getId(), projection.getStatesJson(), projection.getStateCount(), frozenRules);
        SpecificationDto violatedSpec = JsonUtils.readPersistedRequired(
                "verification trace", projection.getId(), "violatedSpecJson",
                () -> JsonUtils.fromJson(projection.getViolatedSpecJson(), SpecificationDto.class));
        return TraceSummaryDto.builder()
                .id(projection.getId())
                .verificationTaskId(requireVerificationTaskId(
                        projection.getId(), projection.getVerificationTaskId()))
                .violatedSpecId(projection.getViolatedSpecId())
                .violatedSpec(violatedSpec)
                .stateCount(states.size())
                .createdAt(projection.getCreatedAt())
                .dataAvailable(true)
                .build();
    }

    private List<TraceStateDto> readRequiredStates(
            Long id, String statesJson, Integer stateCount, List<RuleDto> frozenRules) {
        List<TraceStateDto> states = JsonUtils.readPersistedRequired(
                "verification trace", id, "statesJson",
                () -> TraceStateIntegrity.requireValidStates(JsonUtils.fromJson(
                        statesJson, new TypeReference<List<TraceStateDto>>() {})));
        if (states.isEmpty()) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", id, "statesJson", "trace has no states");
        }
        int persistedStateCount = requiredStateCount(id, stateCount);
        if (states.size() != persistedStateCount) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", id, "stateCount",
                    "state count does not match statesJson");
        }
        return JsonUtils.readPersisted(
                "verification trace", id, "statesJson", () -> {
                    TraceStateIntegrity.requireRuleEvidenceMatchesFrozenRules(states, frozenRules);
                    return states;
                });
    }

    private List<RuleDto> readFrozenRules(Long id, String requestJson, int expectedRuleCount) {
        VerificationRequestDto request = JsonUtils.readPersistedJsonRequired(
                "verification trace", id, "requestJson", requestJson,
                () -> JsonUtils.fromJson(requestJson, VerificationRequestDto.class));
        return JsonUtils.readPersisted(
                "verification trace", id, "requestJson",
                () -> TraceStateIntegrity.requireFrozenRules(request.getRules(), expectedRuleCount));
    }

    private int requiredStateCount(Long id, Integer stateCount) {
        if (stateCount == null || stateCount < 1) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", id, "stateCount", "trace has no states");
        }
        return stateCount;
    }

    private Long requireVerificationTaskId(Long traceId, Long verificationTaskId) {
        if (verificationTaskId == null || verificationTaskId < 1) {
            throw new cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException(
                    "verification trace", traceId, "verificationTaskId", "trace owner is missing");
        }
        return verificationTaskId;
    }

    private PersistedModelContextIntegrity.ValidatedContext modelContext(TracePo po) {
        return PersistedModelContextIntegrity.readVerification(
                "verification trace", po.getId(), po.getIsAttack(), po.getAttackBudget(),
                po.getEnablePrivacy(), po.getModeledDeviceAttackPointCount(),
                po.getModeledFalsifiableReadingDeviceCount(),
                po.getModeledAutomationLinkAttackPointCount(), po.getModelSemanticsJson(),
                po.getModelSnapshotJson());
    }

    private PersistedModelContextIntegrity.ValidatedContext modelContext(
            TraceSummaryProjection projection) {
        return PersistedModelContextIntegrity.readVerification(
                "verification trace", projection.getId(), projection.getIsAttack(),
                projection.getAttackBudget(), projection.getEnablePrivacy(),
                projection.getModeledDeviceAttackPointCount(),
                projection.getModeledFalsifiableReadingDeviceCount(),
                projection.getModeledAutomationLinkAttackPointCount(),
                projection.getModelSemanticsJson(), projection.getModelSnapshotJson());
    }

}
