package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.ModelGenerationDiagnostics;
import cn.edu.nju.Iot_Verify.util.TraceStateIntegrity;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;
import lombok.extern.slf4j.Slf4j;

import java.util.List;

/**
 * SimulationTrace PO 与 DTO 之间的转换映射器
 */
@Component
@Slf4j
public class SimulationTraceMapper {

    /**
     * SimulationTracePo -> SimulationTraceDto（详情）
     */
    public SimulationTraceDto toDto(SimulationTracePo po) {
        if (po == null) return null;

        List<String> logs = JsonUtils.readPersisted("simulation trace", po.getId(), "logsJson",
                () -> JsonUtils.fromJsonToStringList(po.getLogsJson()));
        List<ModelGenerationIssueDto> generationIssues = JsonUtils.readPersisted(
                "simulation trace", po.getId(), "generationIssuesJson",
                () -> readGenerationIssues(po.getGenerationIssuesJson()));
        List<TraceStateDto> states = readRequiredStates(po);
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, logs);
        SimulationTraceDto dto = SimulationTraceDto.builder()
                .id(po.getId())
                .userId(po.getUserId())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .modelComplete(disabledRuleCount == 0)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .states(states)
                .logs(logs)
                .nusmvOutput(po.getNusmvOutput())
                .requestJson(po.getRequestJson())
                .templateSnapshotsJson(po.getTemplateSnapshotsJson())
                .modelSnapshot(JsonUtils.readPersistedRequired("simulation trace", po.getId(),
                        "modelSnapshotJson", () -> readModelSnapshot(po.getModelSnapshotJson())))
                .createdAt(po.getCreatedAt())
                .historyPersistence(RunPersistenceDto.saved(po.getId()))
                .build();
        applyPersistedContext(dto, po);
        return dto;
    }

    public SimulationTraceSummaryDto toSummaryProjectionDto(SimulationTraceSummaryProjection projection) {
        if (projection == null) return null;

        requireStateMetadata(projection.getId(), projection.getStateCount(),
                projection.getSteps(), projection.getRequestedSteps());
        List<ModelGenerationIssueDto> generationIssues = JsonUtils.readPersisted(
                "simulation trace", projection.getId(), "generationIssuesJson",
                () -> readGenerationIssues(projection.getGenerationIssuesJson()));
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(
                generationIssues, JsonUtils.readPersisted("simulation trace", projection.getId(), "logsJson",
                        () -> JsonUtils.fromJsonToStringList(projection.getLogsJson())));
        SimulationTraceSummaryDto dto = SimulationTraceSummaryDto.builder()
                .id(projection.getId())
                .requestedSteps(projection.getRequestedSteps())
                .steps(projection.getSteps())
                .modelComplete(disabledRuleCount == 0)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .modelSnapshot(JsonUtils.readPersistedRequired("simulation trace", projection.getId(),
                        "modelSnapshotJson", () -> readModelSnapshot(projection.getModelSnapshotJson())))
                .createdAt(projection.getCreatedAt())
                .dataAvailable(true)
                .build();
        requirePersistedContext(projection.getId(), projection.getIsAttack(),
                projection.getAttackBudget(), projection.getEnablePrivacy());
        dto.setAttack(projection.getIsAttack());
        dto.setAttackBudget(Boolean.TRUE.equals(projection.getIsAttack())
                ? projection.getAttackBudget() : 0);
        dto.setEnablePrivacy(projection.getEnablePrivacy());
        return dto;
    }

    public List<SimulationTraceSummaryDto> toSummaryProjectionDtoList(
            List<SimulationTraceSummaryProjection> projections) {
        if (projections == null) return List.of();
        return projections.stream().map(projection -> {
            try {
                return toSummaryProjectionDto(projection);
            } catch (RuntimeException e) {
                log.error("Simulation history item {} is unavailable because persisted data is invalid",
                        projection != null ? projection.getId() : null, e);
                return SimulationTraceSummaryDto.builder()
                        .id(projection != null ? projection.getId() : null)
                        .createdAt(projection != null ? projection.getCreatedAt() : null)
                        .dataAvailable(false)
                        .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                        .build();
            }
        }).toList();
    }

    private List<ModelGenerationIssueDto> readGenerationIssues(String json) {
        return JsonUtils.fromJsonList(json, ModelGenerationIssueDto.class);
    }

    private ModelRunSnapshotDto readModelSnapshot(String json) {
        return JsonUtils.fromJson(json, ModelRunSnapshotDto.class);
    }

    private List<TraceStateDto> readRequiredStates(SimulationTracePo po) {
        List<TraceStateDto> states = JsonUtils.readPersistedRequired(
                "simulation trace", po.getId(), "statesJson",
                () -> TraceStateIntegrity.requireValidStates(JsonUtils.fromJson(
                        po.getStatesJson(), new TypeReference<List<TraceStateDto>>() {})));
        if (states.isEmpty()) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", po.getId(), "statesJson", "state list is empty");
        }
        requireStateMetadata(po.getId(), po.getStateCount(), po.getSteps(), po.getRequestedSteps());
        if (states.size() != po.getStateCount()) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", po.getId(), "stateCount",
                    "state count does not match statesJson");
        }
        return states;
    }

    private void requireStateMetadata(Long id, Integer stateCount, int steps, int requestedSteps) {
        if (stateCount == null || stateCount < 1) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", id, "stateCount", "state list is empty");
        }
        if (requestedSteps < 1 || steps < 0 || steps > requestedSteps) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", id, "steps", "step metadata is inconsistent");
        }
        if (stateCount != steps + 1) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", id, "stateCount",
                    "state count must equal steps plus the initial state");
        }
    }

    private void applyPersistedContext(SimulationTraceDto dto, SimulationTracePo po) {
        requirePersistedContext(po.getId(), po.getIsAttack(), po.getAttackBudget(), po.getEnablePrivacy());
        dto.setAttack(po.getIsAttack());
        dto.setAttackBudget(Boolean.TRUE.equals(po.getIsAttack()) ? po.getAttackBudget() : 0);
        dto.setEnablePrivacy(po.getEnablePrivacy());
        if (po.getModelSemanticsJson() != null && !po.getModelSemanticsJson().isBlank()) {
            dto.setModelSemantics(JsonUtils.readPersistedRequired(
                    "simulation trace", po.getId(), "modelSemanticsJson",
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

    private void requirePersistedContext(Long id, Boolean isAttack, Integer attackBudget,
                                         Boolean enablePrivacy) {
        if (isAttack == null) {
            throw missingContextField(id, "isAttack");
        }
        if (attackBudget == null) {
            throw missingContextField(id, "attackBudget");
        }
        if (enablePrivacy == null) {
            throw missingContextField(id, "enablePrivacy");
        }
    }

    private PersistedDataIntegrityException missingContextField(Long id, String field) {
        return new PersistedDataIntegrityException(
                "simulation trace", id, field, "required run context is missing");
    }
}
