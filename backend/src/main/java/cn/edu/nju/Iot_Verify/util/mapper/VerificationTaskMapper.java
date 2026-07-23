package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationRunSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * VerificationTask PO 与 DTO 之间的转换映射器
 */
@Component
public class VerificationTaskMapper {

    /**
     * VerificationTaskPo -> VerificationTaskDto
     */
    public VerificationTaskDto toDto(VerificationTaskPo po) {
        if (po == null) {
            return null;
        }

        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("verification task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        VerificationOutcome outcome = taskOutcome(po);

        return VerificationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(po.getIsAttack()))
                .attackBudget(po.getAttackBudget() != null ? po.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(po.getEnablePrivacy()))
                .modelSemantics(modelSemantics(po, "verification task"))
                .modelSnapshot(JsonUtils.readPersistedRequired("verification task", po.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                po.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .outcome(outcome)
                .modelComplete(taskModelComplete(po, outcome))
                .violatedSpecCount(po.getViolatedSpecCount())
                .disabledRuleCount(po.getDisabledRuleCount())
                .skippedSpecCount(po.getSkippedSpecCount())
                .generationIssues(readGenerationIssues(po))
                .specResults(readSpecResults(po))
                .checkLogs(checkLogs)
                .nusmvOutput(po.getNusmvOutput())
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .progressStage(po.getProgressStage())
                .build();
    }

    /**
     * List<VerificationTaskPo> -> List<VerificationTaskDto>
     */
    public List<VerificationTaskDto> toDtoList(List<VerificationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toDto)
                .toList();
    }

    public VerificationTaskSummaryDto toSummaryDto(VerificationTaskPo po) {
        if (po == null) {
            return null;
        }

        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("verification task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        VerificationOutcome outcome = taskOutcome(po);

        return VerificationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(po.getIsAttack()))
                .attackBudget(po.getAttackBudget() != null ? po.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(po.getEnablePrivacy()))
                .modelSemantics(modelSemantics(po, "verification task"))
                .modelSnapshot(JsonUtils.readPersistedRequired("verification task", po.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                po.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .progress(po.getProgress())
                .progressStage(po.getProgressStage())
                .outcome(outcome)
                .modelComplete(taskModelComplete(po, outcome))
                .violatedSpecCount(po.getViolatedSpecCount())
                .disabledRuleCount(po.getDisabledRuleCount())
                .skippedSpecCount(po.getSkippedSpecCount())
                .generationIssues(readGenerationIssues(po))
                .errorMessage(po.getErrorMessage())
                .build();
    }

    public VerificationRunSummaryDto toRunSummaryDto(
            VerificationRunSummaryProjection projection, int counterexampleCount) {
        if (projection == null) return null;
        VerificationOutcome outcome = projection.getOutcome() != null
                ? projection.getOutcome() : VerificationOutcome.INCONCLUSIVE;
        int disabledRuleCount = pointCount(projection.getDisabledRuleCount());
        int skippedSpecCount = pointCount(projection.getSkippedSpecCount());
        return VerificationRunSummaryDto.builder()
                .id(projection.getId())
                .createdAt(projection.getCreatedAt())
                .startedAt(projection.getStartedAt())
                .completedAt(projection.getCompletedAt())
                .processingTimeMs(projection.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(projection.getIsAttack()))
                .attackBudget(projection.getAttackBudget() != null ? projection.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(projection.getEnablePrivacy()))
                .modelSemantics(modelSemantics(projection, "verification run"))
                .modelSnapshot(JsonUtils.readPersistedRequired("verification run", projection.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                projection.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .outcome(outcome)
                .modelComplete(outcome.isModelComplete(disabledRuleCount, skippedSpecCount))
                .violatedSpecCount(pointCount(projection.getViolatedSpecCount()))
                .counterexampleCount(Math.max(0, counterexampleCount))
                .disabledRuleCount(disabledRuleCount)
                .skippedSpecCount(skippedSpecCount)
                .generationIssues(JsonUtils.readPersisted(
                        "verification run", projection.getId(), "generationIssuesJson",
                        () -> JsonUtils.fromJsonList(
                                projection.getGenerationIssuesJson(), ModelGenerationIssueDto.class)))
                .dataAvailable(true)
                .build();
    }

    public VerificationRunDto toRunDto(VerificationTaskPo po, int counterexampleCount) {
        if (po == null) {
            return null;
        }
        VerificationOutcome outcome = taskOutcome(po);
        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("verification run", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        return VerificationRunDto.builder()
                .id(po.getId())
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(Boolean.TRUE.equals(po.getIsAttack()))
                .attackBudget(po.getAttackBudget() != null ? po.getAttackBudget() : 0)
                .enablePrivacy(Boolean.TRUE.equals(po.getEnablePrivacy()))
                .modelSemantics(modelSemantics(po, "verification run"))
                .modelSnapshot(JsonUtils.readPersistedRequired("verification run", po.getId(),
                        "modelSnapshotJson", () -> JsonUtils.fromJson(
                                po.getModelSnapshotJson(), ModelRunSnapshotDto.class)))
                .outcome(outcome)
                .modelComplete(taskModelComplete(po, outcome))
                .violatedSpecCount(po.getViolatedSpecCount() != null ? po.getViolatedSpecCount() : 0)
                .counterexampleCount(Math.max(0, counterexampleCount))
                .disabledRuleCount(po.getDisabledRuleCount() != null ? po.getDisabledRuleCount() : 0)
                .skippedSpecCount(po.getSkippedSpecCount() != null ? po.getSkippedSpecCount() : 0)
                .generationIssues(readGenerationIssues(po))
                .specResults(readSpecResults(po))
                .checkLogs(checkLogs)
                .nusmvOutput(po.getNusmvOutput())
                .build();
    }

    private VerificationOutcome taskOutcome(VerificationTaskPo po) {
        if (po.getStatus() == VerificationTaskPo.TaskStatus.PENDING
                || po.getStatus() == VerificationTaskPo.TaskStatus.RUNNING) {
            return null;
        }
        if (po.getOutcome() == null) {
            return VerificationOutcome.INCONCLUSIVE;
        }
        return po.getOutcome();
    }

    private Boolean taskModelComplete(VerificationTaskPo po, VerificationOutcome outcome) {
        if (outcome == null) {
            return null;
        }
        return outcome.isModelComplete(
                po.getDisabledRuleCount() != null ? po.getDisabledRuleCount() : 0,
                po.getSkippedSpecCount() != null ? po.getSkippedSpecCount() : 0);
    }

    public List<VerificationTaskSummaryDto> toSummaryDtoList(List<VerificationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toSummaryDto)
                .toList();
    }

    private List<SpecResultDto> readSpecResults(VerificationTaskPo po) {
        return JsonUtils.readPersisted("verification task", po.getId(), "specResultsJson",
                () -> JsonUtils.fromJsonList(po.getSpecResultsJson(), SpecResultDto.class));
    }

    private List<ModelGenerationIssueDto> readGenerationIssues(VerificationTaskPo po) {
        return JsonUtils.readPersisted("verification task", po.getId(), "generationIssuesJson",
                () -> JsonUtils.fromJsonList(po.getGenerationIssuesJson(), ModelGenerationIssueDto.class));
    }

    private int pointCount(Integer value) {
        return value != null ? Math.max(0, value) : 0;
    }

    private ModelSemanticsDto modelSemantics(VerificationTaskPo po, String recordType) {
        if (po.getModelSemanticsJson() != null && !po.getModelSemanticsJson().isBlank()) {
            return JsonUtils.readPersistedRequired(recordType, po.getId(), "modelSemanticsJson",
                    () -> JsonUtils.fromJson(po.getModelSemanticsJson(), ModelSemanticsDto.class));
        }
        return ModelSemanticsDto.forRun(
                Boolean.TRUE.equals(po.getIsAttack()), Boolean.TRUE.equals(po.getEnablePrivacy()),
                pointCount(po.getModeledDeviceAttackPointCount()),
                pointCount(po.getModeledAutomationLinkAttackPointCount()),
                pointCount(po.getModeledFalsifiableReadingDeviceCount()));
    }

    private ModelSemanticsDto modelSemantics(
            VerificationRunSummaryProjection projection, String recordType) {
        if (projection.getModelSemanticsJson() != null
                && !projection.getModelSemanticsJson().isBlank()) {
            return JsonUtils.readPersistedRequired(recordType, projection.getId(), "modelSemanticsJson",
                    () -> JsonUtils.fromJson(
                            projection.getModelSemanticsJson(), ModelSemanticsDto.class));
        }
        return ModelSemanticsDto.forRun(
                Boolean.TRUE.equals(projection.getIsAttack()),
                Boolean.TRUE.equals(projection.getEnablePrivacy()),
                pointCount(projection.getModeledDeviceAttackPointCount()),
                pointCount(projection.getModeledAutomationLinkAttackPointCount()),
                pointCount(projection.getModeledFalsifiableReadingDeviceCount()));
    }
}
