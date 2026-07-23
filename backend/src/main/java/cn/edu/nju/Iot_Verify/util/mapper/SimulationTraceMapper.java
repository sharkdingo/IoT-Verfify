package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.ModelGenerationDiagnostics;
import cn.edu.nju.Iot_Verify.util.PersistedModelContextIntegrity;
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
        List<TraceStateDto> states = readRequiredStates(
                po.getId(), po.getStatesJson(), po.getStateCount(),
                po.getSteps(), po.getRequestedSteps());
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, logs);
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(po);
        List<RuleDto> frozenRules = readFrozenRules(
                po.getId(), po.getRequestJson(), context.modelSnapshot().getRuleCount());
        states = validateRuleEvidence(po.getId(), states, frozenRules);
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
                .modelSnapshot(context.modelSnapshot())
                .createdAt(po.getCreatedAt())
                .historyPersistence(RunPersistenceDto.saved(po.getId()))
                .build();
        applyPersistedContext(dto, context);
        return dto;
    }

    public SimulationTraceSummaryDto toSummaryProjectionDto(SimulationTraceSummaryProjection projection) {
        if (projection == null) return null;

        List<TraceStateDto> states = readRequiredStates(projection.getId(), projection.getStatesJson(),
                projection.getStateCount(), projection.getSteps(), projection.getRequestedSteps());
        List<ModelGenerationIssueDto> generationIssues = JsonUtils.readPersisted(
                "simulation trace", projection.getId(), "generationIssuesJson",
                () -> readGenerationIssues(projection.getGenerationIssuesJson()));
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(
                generationIssues, JsonUtils.readPersisted("simulation trace", projection.getId(), "logsJson",
                        () -> JsonUtils.fromJsonToStringList(projection.getLogsJson())));
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(projection);
        List<RuleDto> frozenRules = readFrozenRules(
                projection.getId(), projection.getRequestJson(), context.modelSnapshot().getRuleCount());
        validateRuleEvidence(projection.getId(), states, frozenRules);
        SimulationTraceSummaryDto dto = SimulationTraceSummaryDto.builder()
                .id(projection.getId())
                .requestedSteps(projection.getRequestedSteps())
                .steps(projection.getSteps())
                .modelComplete(disabledRuleCount == 0)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .modelSnapshot(context.modelSnapshot())
                .createdAt(projection.getCreatedAt())
                .dataAvailable(true)
                .build();
        dto.setAttack(context.isAttack());
        dto.setAttackBudget(context.attackBudget());
        dto.setEnablePrivacy(context.enablePrivacy());
        return dto;
    }

    public List<SimulationTraceSummaryDto> toSummaryProjectionDtoList(
            List<SimulationTraceSummaryProjection> projections) {
        if (projections == null) return List.of();
        return projections.stream().map(projection -> {
            try {
                return toSummaryProjectionDto(projection);
            } catch (PersistedDataIntegrityException e) {
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

    private List<TraceStateDto> readRequiredStates(
            Long id, String statesJson, Integer stateCount, int steps, int requestedSteps) {
        List<TraceStateDto> states = JsonUtils.readPersistedRequired(
                "simulation trace", id, "statesJson",
                () -> TraceStateIntegrity.requireValidStates(JsonUtils.fromJson(
                        statesJson, new TypeReference<List<TraceStateDto>>() {})));
        if (states.isEmpty()) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", id, "statesJson", "state list is empty");
        }
        requireStateMetadata(id, stateCount, steps, requestedSteps);
        if (states.size() != stateCount) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", id, "stateCount",
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

    private List<RuleDto> readFrozenRules(Long id, String requestJson, int expectedRuleCount) {
        SimulationRequestDto request = JsonUtils.readPersistedJsonRequired(
                "simulation trace", id, "requestJson", requestJson,
                () -> JsonUtils.fromJson(requestJson, SimulationRequestDto.class));
        return JsonUtils.readPersisted(
                "simulation trace", id, "requestJson",
                () -> TraceStateIntegrity.requireFrozenRules(request.getRules(), expectedRuleCount));
    }

    private List<TraceStateDto> validateRuleEvidence(
            Long id, List<TraceStateDto> states, List<RuleDto> frozenRules) {
        return JsonUtils.readPersisted(
                "simulation trace", id, "statesJson", () -> {
                    TraceStateIntegrity.requireRuleEvidenceMatchesFrozenRules(states, frozenRules);
                    return states;
                });
    }

    private void applyPersistedContext(
            SimulationTraceDto dto, PersistedModelContextIntegrity.ValidatedContext context) {
        dto.setAttack(context.isAttack());
        dto.setAttackBudget(context.attackBudget());
        dto.setEnablePrivacy(context.enablePrivacy());
        dto.setModelSemantics(context.modelSemantics());
    }

    private PersistedModelContextIntegrity.ValidatedContext modelContext(SimulationTracePo po) {
        return PersistedModelContextIntegrity.readSimulation(
                "simulation trace", po.getId(), po.getIsAttack(), po.getAttackBudget(),
                po.getEnablePrivacy(), po.getModeledDeviceAttackPointCount(),
                po.getModeledFalsifiableReadingDeviceCount(),
                po.getModeledAutomationLinkAttackPointCount(), po.getModelSemanticsJson(),
                po.getModelSnapshotJson());
    }

    private PersistedModelContextIntegrity.ValidatedContext modelContext(
            SimulationTraceSummaryProjection projection) {
        return PersistedModelContextIntegrity.readSimulation(
                "simulation trace", projection.getId(), projection.getIsAttack(),
                projection.getAttackBudget(), projection.getEnablePrivacy(),
                projection.getModeledDeviceAttackPointCount(),
                projection.getModeledFalsifiableReadingDeviceCount(),
                projection.getModeledAutomationLinkAttackPointCount(),
                projection.getModelSemanticsJson(), projection.getModelSnapshotJson());
    }
}
