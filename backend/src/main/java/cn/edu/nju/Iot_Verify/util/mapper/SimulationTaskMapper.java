package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.ModelGenerationDiagnostics;
import cn.edu.nju.Iot_Verify.util.PersistedModelContextIntegrity;
import org.springframework.stereotype.Component;

import java.util.List;

@Component
public class SimulationTaskMapper {

    public SimulationTaskDto toDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        validateLifecycle(po);
        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("simulation task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        List<ModelGenerationIssueDto> generationIssues = readGenerationIssues(po);
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, checkLogs);
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(po);
        return SimulationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus().name())
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
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
                .progressStage(po.getProgressStage())
                .build();
    }

    public SimulationTaskSummaryDto toSummaryDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        validateLifecycle(po);
        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("simulation task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        List<ModelGenerationIssueDto> generationIssues = readGenerationIssues(po);
        int disabledRuleCount = ModelGenerationDiagnostics.disabledRuleCount(generationIssues, checkLogs);
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(po);
        return SimulationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus().name())
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .modelComplete(po.getStatus() == SimulationTaskPo.TaskStatus.COMPLETED
                        ? disabledRuleCount == 0 : null)
                .disabledRuleCount(disabledRuleCount)
                .generationIssues(generationIssues)
                .simulationTraceId(po.getSimulationTraceId())
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .progressStage(po.getProgressStage())
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

    private PersistedModelContextIntegrity.ValidatedContext modelContext(SimulationTaskPo po) {
        return PersistedModelContextIntegrity.readSimulation(
                "simulation task", po.getId(), po.getIsAttack(), po.getAttackBudget(),
                po.getEnablePrivacy(), po.getModeledDeviceAttackPointCount(),
                po.getModeledFalsifiableReadingDeviceCount(),
                po.getModeledAutomationLinkAttackPointCount(), po.getModelSemanticsJson(),
                po.getModelSnapshotJson());
    }

    private void validateLifecycle(SimulationTaskPo po) {
        if (po.getId() == null || po.getId() < 1) {
            fail(po, "id", "task id is missing or invalid");
        }
        if (po.getUserId() == null || po.getUserId() < 1) {
            fail(po, "userId", "task owner is missing or invalid");
        }
        if (po.getStatus() == null) {
            fail(po, "status", "task status is missing");
        }
        if (po.getCreatedAt() == null) {
            fail(po, "createdAt", "task creation time is missing");
        }
        Integer requestedSteps = po.getRequestedSteps();
        if (requestedSteps == null || requestedSteps < 1) {
            fail(po, "requestedSteps", "requested steps must be positive");
        }
        Integer steps = po.getSteps();
        if (steps != null && (steps < 0 || steps > requestedSteps)) {
            fail(po, "steps", "actual steps must be between zero and requested steps");
        }
        if (po.getProcessingTimeMs() != null && po.getProcessingTimeMs() < 0) {
            fail(po, "processingTimeMs", "processing time cannot be negative");
        }
        if (po.getProgress() == null || po.getProgress() < 0 || po.getProgress() > 100) {
            fail(po, "progress", "task progress must be between zero and 100");
        }

        if (po.getStartedAt() != null && po.getStartedAt().isBefore(po.getCreatedAt())) {
            fail(po, "startedAt", "task start time precedes creation time");
        }
        if (po.getCompletedAt() != null
                && (po.getCompletedAt().isBefore(po.getCreatedAt())
                || (po.getStartedAt() != null && po.getCompletedAt().isBefore(po.getStartedAt())))) {
            fail(po, "completedAt", "task completion time is out of order");
        }
        if (po.getProcessingTimeMs() != null
                && (po.getStartedAt() == null || po.getCompletedAt() == null)) {
            fail(po, "processingTimeMs", "processing time requires start and completion times");
        }

        SimulationTaskPo.TaskStatus status = po.getStatus();
        boolean terminal = status == SimulationTaskPo.TaskStatus.COMPLETED
                || status == SimulationTaskPo.TaskStatus.FAILED
                || status == SimulationTaskPo.TaskStatus.CANCELLED;
        if (status == SimulationTaskPo.TaskStatus.PENDING && po.getStartedAt() != null) {
            fail(po, "startedAt", "pending task cannot have a start time");
        }
        if ((status == SimulationTaskPo.TaskStatus.RUNNING
                || status == SimulationTaskPo.TaskStatus.COMPLETED)
                && po.getStartedAt() == null) {
            fail(po, "startedAt", "running or completed task start time is missing");
        }
        if (terminal) {
            if (po.getCompletedAt() == null) {
                fail(po, "completedAt", "terminal task completion time is missing");
            }
            if (po.getProgress() == null || po.getProgress() != 100) {
                fail(po, "progress", "terminal task progress must be 100");
            }
        } else if (po.getCompletedAt() != null) {
            fail(po, "completedAt", "active task cannot have a completion time");
        }
        if (status == SimulationTaskPo.TaskStatus.FAILED
                && (po.getErrorMessage() == null || po.getErrorMessage().isBlank())) {
            fail(po, "errorMessage", "failed task error message is missing");
        }
        if (status == SimulationTaskPo.TaskStatus.COMPLETED) {
            if (steps == null) {
                fail(po, "steps", "completed task actual steps are missing");
            }
            if (po.getSimulationTraceId() == null || po.getSimulationTraceId() < 1) {
                fail(po, "simulationTraceId", "completed task trace reference is missing or invalid");
            }
        } else if (po.getSimulationTraceId() != null) {
            fail(po, "simulationTraceId", "non-completed task cannot reference a saved trace");
        }
    }

    private void fail(SimulationTaskPo po, String field, String detail) {
        throw new PersistedDataIntegrityException("simulation task", po.getId(), field, detail);
    }
}
