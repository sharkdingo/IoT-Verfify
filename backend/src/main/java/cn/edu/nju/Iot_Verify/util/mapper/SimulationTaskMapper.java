package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.ModelGenerationDiagnostics;
import org.springframework.stereotype.Component;

import java.util.List;

@Component
public class SimulationTaskMapper {

    public SimulationTaskDto toDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("simulation task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        List<ModelGenerationIssueDto> generationIssues = readGenerationIssues(po);
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, checkLogs);
        return SimulationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(po.getIsAttack()))
                .attackBudget(po.getAttackBudget() != null ? po.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(po.getEnablePrivacy()))
                .modelSemantics(ModelSemanticsDto.forRun(
                        Boolean.TRUE.equals(po.getIsAttack()), Boolean.TRUE.equals(po.getEnablePrivacy()),
                        pointCount(po.getModeledDeviceAttackPointCount()),
                        pointCount(po.getModeledAutomationLinkAttackPointCount()),
                        pointCount(po.getModeledFalsifiableReadingDeviceCount())))
                .modelSnapshot(JsonUtils.readPersistedRequired("simulation task", po.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                po.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .modelComplete(po.getStatus() == SimulationTaskPo.TaskStatus.COMPLETED
                        ? disabledRuleCount == 0 : null)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .simulationTraceId(po.getSimulationTraceId())
                .checkLogs(checkLogs)
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .build();
    }

    public SimulationTaskSummaryDto toSummaryDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("simulation task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        List<ModelGenerationIssueDto> generationIssues = readGenerationIssues(po);
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, checkLogs);
        return SimulationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(po.getIsAttack()))
                .attackBudget(po.getAttackBudget() != null ? po.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(po.getEnablePrivacy()))
                .modelSemantics(ModelSemanticsDto.forRun(
                        Boolean.TRUE.equals(po.getIsAttack()), Boolean.TRUE.equals(po.getEnablePrivacy()),
                        pointCount(po.getModeledDeviceAttackPointCount()),
                        pointCount(po.getModeledAutomationLinkAttackPointCount()),
                        pointCount(po.getModeledFalsifiableReadingDeviceCount())))
                .modelSnapshot(JsonUtils.readPersistedRequired("simulation task", po.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                po.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .modelComplete(po.getStatus() == SimulationTaskPo.TaskStatus.COMPLETED
                        ? disabledRuleCount == 0 : null)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .simulationTraceId(po.getSimulationTraceId())
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .build();
    }

    public List<SimulationTaskSummaryDto> toSummaryDtoList(List<SimulationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toSummaryDto)
                .toList();
    }

    private List<ModelGenerationIssueDto> readGenerationIssues(SimulationTaskPo po) {
        if (po.getGenerationIssues() != null) {
            return List.copyOf(po.getGenerationIssues());
        }
        return JsonUtils.readPersisted("simulation task", po.getId(), "generationIssuesJson",
                () -> JsonUtils.fromJsonList(po.getGenerationIssuesJson(), ModelGenerationIssueDto.class));
    }

    private int pointCount(Integer value) {
        return value != null ? Math.max(0, value) : 0;
    }
}

