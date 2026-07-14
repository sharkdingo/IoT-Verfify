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
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.ModelGenerationDiagnostics;
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

    /**
     * SimulationTracePo -> SimulationTraceSummaryDto（列表摘要）
     */
    public SimulationTraceSummaryDto toSummaryDto(SimulationTracePo po) {
        if (po == null) return null;

        readRequiredStates(po);
        List<ModelGenerationIssueDto> generationIssues = JsonUtils.readPersisted(
                "simulation trace", po.getId(), "generationIssuesJson",
                () -> readGenerationIssues(po.getGenerationIssuesJson()));
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(
                generationIssues, JsonUtils.readPersisted("simulation trace", po.getId(), "logsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getLogsJson())));
        SimulationTraceSummaryDto dto = SimulationTraceSummaryDto.builder()
                .id(po.getId())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .modelComplete(disabledRuleCount == 0)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .modelSnapshot(JsonUtils.readPersistedRequired("simulation trace", po.getId(),
                        "modelSnapshotJson", () -> readModelSnapshot(po.getModelSnapshotJson())))
                .createdAt(po.getCreatedAt())
                .dataAvailable(true)
                .build();
        applyPersistedContext(dto, po);
        return dto;
    }

    /**
     * List<SimulationTracePo> -> List<SimulationTraceSummaryDto>
     */
    public List<SimulationTraceSummaryDto> toSummaryDtoList(List<SimulationTracePo> poList) {
        if (poList == null) return List.of();
        return poList.stream().map(po -> {
            try {
                return toSummaryDto(po);
            } catch (RuntimeException e) {
                log.error("Simulation history item {} is unavailable because persisted data is invalid",
                        po != null ? po.getId() : null, e);
                return SimulationTraceSummaryDto.builder()
                        .id(po != null ? po.getId() : null)
                        .createdAt(po != null ? po.getCreatedAt() : null)
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
                () -> JsonUtils.fromJson(
                        po.getStatesJson(), new TypeReference<List<TraceStateDto>>() {}));
        if (states.isEmpty()) {
            throw new PersistedDataIntegrityException(
                    "simulation trace", po.getId(), "statesJson", "state list is empty");
        }
        return states;
    }

    private void applyPersistedContext(SimulationTraceDto dto, SimulationTracePo po) {
        if (po.getIsAttack() == null || po.getAttackBudget() == null || po.getEnablePrivacy() == null) return;
        dto.setAttack(po.getIsAttack());
        dto.setAttackBudget(Boolean.TRUE.equals(po.getIsAttack()) ? po.getAttackBudget() : 0);
        dto.setEnablePrivacy(po.getEnablePrivacy());
        if (po.getModeledDeviceAttackPointCount() != null
                && po.getModeledAutomationLinkAttackPointCount() != null
                && po.getModeledFalsifiableReadingDeviceCount() != null) {
            dto.setModelSemantics(ModelSemanticsDto.forRun(
                    Boolean.TRUE.equals(po.getIsAttack()), Boolean.TRUE.equals(po.getEnablePrivacy()),
                    po.getModeledDeviceAttackPointCount(),
                    po.getModeledAutomationLinkAttackPointCount(),
                    po.getModeledFalsifiableReadingDeviceCount()));
        }
    }

    private void applyPersistedContext(SimulationTraceSummaryDto dto, SimulationTracePo po) {
        if (po.getIsAttack() == null || po.getAttackBudget() == null || po.getEnablePrivacy() == null) return;
        dto.setAttack(po.getIsAttack());
        dto.setAttackBudget(Boolean.TRUE.equals(po.getIsAttack()) ? po.getAttackBudget() : 0);
        dto.setEnablePrivacy(po.getEnablePrivacy());
    }
}
