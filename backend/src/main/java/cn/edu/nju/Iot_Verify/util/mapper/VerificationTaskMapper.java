package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationRunSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.PersistedModelContextIntegrity;
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
        validateLifecycle(po, "verification task");

        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("verification task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        VerificationOutcome outcome = taskOutcome(po, "verification task");
        PersistedModelContextIntegrity.ValidatedContext context =
                modelContext(po, "verification task");

        return VerificationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
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
        validateLifecycle(po, "verification task");

        List<String> checkLogs = po.getCheckLogs() != null
                ? po.getCheckLogs()
                : JsonUtils.readPersisted("verification task", po.getId(), "checkLogsJson",
                        () -> JsonUtils.fromJsonToStringList(po.getCheckLogsJson()));
        VerificationOutcome outcome = taskOutcome(po, "verification task");
        PersistedModelContextIntegrity.ValidatedContext context =
                modelContext(po, "verification task");

        return VerificationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
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
        validateCompletedRunProjection(projection);
        VerificationOutcome outcome = completedOutcome(
                "verification run", projection.getId(), projection.getStatus(), projection.getOutcome());
        PersistedModelContextIntegrity.ValidatedContext context = modelContext(projection);
        int disabledRuleCount = projection.getDisabledRuleCount();
        int skippedSpecCount = projection.getSkippedSpecCount();
        return VerificationRunSummaryDto.builder()
                .id(projection.getId())
                .createdAt(projection.getCreatedAt())
                .startedAt(projection.getStartedAt())
                .completedAt(projection.getCompletedAt())
                .processingTimeMs(projection.getProcessingTimeMs())
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
                .outcome(outcome)
                .modelComplete(outcome.isModelComplete(disabledRuleCount, skippedSpecCount))
                .violatedSpecCount(projection.getViolatedSpecCount())
                .counterexampleCount(requireCounterexampleCount(
                        projection.getId(), counterexampleCount))
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
        validateLifecycle(po, "verification run");
        if (po.getStatus() != VerificationTaskPo.TaskStatus.COMPLETED) {
            throw new PersistedDataIntegrityException(
                    "verification run", po.getId(), "status", "completed run status is invalid");
        }
        VerificationOutcome outcome = taskOutcome(po, "verification run");
        PersistedModelContextIntegrity.ValidatedContext context =
                modelContext(po, "verification run");
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
                .isAttack(context.isAttack())
                .attackBudget(context.attackBudget())
                .enablePrivacy(context.enablePrivacy())
                .modelSemantics(context.modelSemantics())
                .modelSnapshot(context.modelSnapshot())
                .outcome(outcome)
                .modelComplete(taskModelComplete(po, outcome))
                .violatedSpecCount(po.getViolatedSpecCount())
                .counterexampleCount(requireCounterexampleCount(po.getId(), counterexampleCount))
                .disabledRuleCount(po.getDisabledRuleCount())
                .skippedSpecCount(po.getSkippedSpecCount())
                .generationIssues(readGenerationIssues(po))
                .specResults(readSpecResults(po))
                .checkLogs(checkLogs)
                .nusmvOutput(po.getNusmvOutput())
                .build();
    }

    private VerificationOutcome taskOutcome(VerificationTaskPo po, String recordType) {
        if (po.getStatus() == null) {
            throw new PersistedDataIntegrityException(
                    recordType, po.getId(), "status", "task status is missing");
        }
        if (po.getStatus() == VerificationTaskPo.TaskStatus.PENDING
                || po.getStatus() == VerificationTaskPo.TaskStatus.RUNNING) {
            if (po.getOutcome() != null) {
                throw new PersistedDataIntegrityException(
                        recordType, po.getId(), "outcome", "active task already has a terminal outcome");
            }
            return null;
        }
        if (po.getOutcome() == null) {
            throw new PersistedDataIntegrityException(
                    recordType, po.getId(), "outcome", "terminal task outcome is missing");
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

    private PersistedModelContextIntegrity.ValidatedContext modelContext(
            VerificationTaskPo po, String recordType) {
        return PersistedModelContextIntegrity.readVerification(
                recordType, po.getId(), po.getIsAttack(), po.getAttackBudget(), po.getEnablePrivacy(),
                po.getModeledDeviceAttackPointCount(), po.getModeledFalsifiableReadingDeviceCount(),
                po.getModeledAutomationLinkAttackPointCount(), po.getModelSemanticsJson(),
                po.getModelSnapshotJson());
    }

    private PersistedModelContextIntegrity.ValidatedContext modelContext(
            VerificationRunSummaryProjection projection) {
        return PersistedModelContextIntegrity.readVerification(
                "verification run", projection.getId(), projection.getIsAttack(),
                projection.getAttackBudget(), projection.getEnablePrivacy(),
                projection.getModeledDeviceAttackPointCount(),
                projection.getModeledFalsifiableReadingDeviceCount(),
                projection.getModeledAutomationLinkAttackPointCount(),
                projection.getModelSemanticsJson(), projection.getModelSnapshotJson());
    }

    private VerificationOutcome completedOutcome(
            String recordType,
            Object recordId,
            VerificationTaskPo.TaskStatus status,
            VerificationOutcome outcome) {
        if (status != VerificationTaskPo.TaskStatus.COMPLETED) {
            throw new PersistedDataIntegrityException(
                    recordType, recordId, "status", "completed run status is invalid");
        }
        if (outcome == null) {
            throw new PersistedDataIntegrityException(
                    recordType, recordId, "outcome", "completed run outcome is missing");
        }
        return outcome;
    }

    private void validateLifecycle(VerificationTaskPo po, String recordType) {
        if (po.getId() == null || po.getId() < 1) {
            fail(recordType, po.getId(), "id", "task id is missing or invalid");
        }
        if (po.getUserId() == null || po.getUserId() < 1) {
            fail(recordType, po.getId(), "userId", "task owner is missing or invalid");
        }
        if (po.getStatus() == null) {
            fail(recordType, po.getId(), "status", "task status is missing");
        }
        if (po.getCreatedAt() == null) {
            fail(recordType, po.getId(), "createdAt", "task creation time is missing");
        }
        if (po.getProgress() == null || po.getProgress() < 0 || po.getProgress() > 100) {
            fail(recordType, po.getId(), "progress", "task progress must be between zero and 100");
        }
        if (po.getProcessingTimeMs() != null && po.getProcessingTimeMs() < 0) {
            fail(recordType, po.getId(), "processingTimeMs", "processing time cannot be negative");
        }
        validateTimeOrder(po, recordType);

        VerificationTaskPo.TaskStatus status = po.getStatus();
        boolean terminal = status == VerificationTaskPo.TaskStatus.COMPLETED
                || status == VerificationTaskPo.TaskStatus.FAILED
                || status == VerificationTaskPo.TaskStatus.CANCELLED;
        if (status == VerificationTaskPo.TaskStatus.PENDING && po.getStartedAt() != null) {
            fail(recordType, po.getId(), "startedAt", "pending task cannot have a start time");
        }
        if ((status == VerificationTaskPo.TaskStatus.RUNNING
                || status == VerificationTaskPo.TaskStatus.COMPLETED)
                && po.getStartedAt() == null) {
            fail(recordType, po.getId(), "startedAt", "running or completed task start time is missing");
        }
        if (terminal) {
            if (po.getCompletedAt() == null) {
                fail(recordType, po.getId(), "completedAt", "terminal task completion time is missing");
            }
            if (po.getProgress() != 100) {
                fail(recordType, po.getId(), "progress", "terminal task progress must be 100");
            }
        } else if (po.getCompletedAt() != null) {
            fail(recordType, po.getId(), "completedAt", "active task cannot have a completion time");
        }
        if (status == VerificationTaskPo.TaskStatus.FAILED
                && (po.getErrorMessage() == null || po.getErrorMessage().isBlank())) {
            fail(recordType, po.getId(), "errorMessage", "failed task error message is missing");
        }
        if (status == VerificationTaskPo.TaskStatus.COMPLETED) {
            if (po.getProcessingTimeMs() == null) {
                fail(recordType, po.getId(), "processingTimeMs", "completed task processing time is missing");
            }
            requireCompletedCount(recordType, po.getId(), "violatedSpecCount", po.getViolatedSpecCount());
            requireCompletedCount(recordType, po.getId(), "disabledRuleCount", po.getDisabledRuleCount());
            requireCompletedCount(recordType, po.getId(), "skippedSpecCount", po.getSkippedSpecCount());
        }
    }

    private void validateTimeOrder(VerificationTaskPo po, String recordType) {
        if (po.getStartedAt() != null && po.getStartedAt().isBefore(po.getCreatedAt())) {
            fail(recordType, po.getId(), "startedAt", "task start time precedes creation time");
        }
        if (po.getCompletedAt() != null
                && (po.getCompletedAt().isBefore(po.getCreatedAt())
                || (po.getStartedAt() != null && po.getCompletedAt().isBefore(po.getStartedAt())))) {
            fail(recordType, po.getId(), "completedAt", "task completion time is out of order");
        }
        if (po.getProcessingTimeMs() != null
                && (po.getStartedAt() == null || po.getCompletedAt() == null)) {
            fail(recordType, po.getId(), "processingTimeMs",
                    "processing time requires start and completion times");
        }
    }

    private void validateCompletedRunProjection(VerificationRunSummaryProjection projection) {
        Object id = projection.getId();
        if (projection.getStatus() != VerificationTaskPo.TaskStatus.COMPLETED) {
            fail("verification run", id, "status", "completed run status is invalid");
        }
        if (projection.getCreatedAt() == null || projection.getStartedAt() == null
                || projection.getCompletedAt() == null) {
            fail("verification run", id, "completedAt", "completed run timestamps are incomplete");
        }
        if (projection.getStartedAt().isBefore(projection.getCreatedAt())
                || projection.getCompletedAt().isBefore(projection.getStartedAt())) {
            fail("verification run", id, "completedAt", "completed run timestamps are out of order");
        }
        if (projection.getProcessingTimeMs() == null || projection.getProcessingTimeMs() < 0) {
            fail("verification run", id, "processingTimeMs", "completed run processing time is invalid");
        }
        requireCompletedCount("verification run", id,
                "violatedSpecCount", projection.getViolatedSpecCount());
        requireCompletedCount("verification run", id,
                "disabledRuleCount", projection.getDisabledRuleCount());
        requireCompletedCount("verification run", id,
                "skippedSpecCount", projection.getSkippedSpecCount());
    }

    private void requireCompletedCount(
            String recordType, Object recordId, String field, Integer value) {
        if (value == null || value < 0) {
            fail(recordType, recordId, field, "completed run count is missing or invalid");
        }
    }

    private int requireCounterexampleCount(Object recordId, int counterexampleCount) {
        if (counterexampleCount < 0) {
            fail("verification run", recordId, "counterexampleCount",
                    "counterexample count cannot be negative");
        }
        return counterexampleCount;
    }

    private void fail(String recordType, Object recordId, String field, String detail) {
        throw new PersistedDataIntegrityException(recordType, recordId, field, detail);
    }
}
