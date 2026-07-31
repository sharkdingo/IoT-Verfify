package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class VerifyTaskStatusTool extends AbstractAiTool {

    private final VerificationService verificationService;

    public VerifyTaskStatusTool(VerificationService verificationService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "verify_task_status";
    }

    @Override
    public LlmToolSpec getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("taskId", Map.of("type", "integer", "description", "Verification task ID returned by verify_model_async.")),
                List.of("taskId")
        );

        return LlmToolSpec.of(getName(),
                "Query async verification task status and progress by taskId. A completed task exposes its runId for get_verification_run. Raw NuSMV output and execution logs are intentionally omitted.",
                schema);
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            requireOnlyFields(args, "arguments", Set.of("taskId"));
            long taskId = positiveLongArg(args, "taskId");

            VerificationTaskDto task = verificationService.getTask(userId, taskId);
            int progress = verificationService.getTaskProgress(userId, taskId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("taskId", taskId);
            body.put("progress", progress);
            body.put("task", taskProjection(task, progress));
            if ("COMPLETED".equals(task.getStatus())) {
                body.put("runId", taskId);
                body.put("nextTool", "get_verification_run");
            }
            return readOnlySuccessJson(body, "Verification task status retrieved.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("verify_task_status busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("verify_task_status business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("verify_task_status failed", e);
            return errorJson("Failed to query verification task.",
                    "INTERNAL_ERROR", 500);
        }
    }

    private Map<String, Object> taskProjection(VerificationTaskDto task, int progress) {
        Map<String, Object> projected = new LinkedHashMap<>();
        projected.put("id", task.getId());
        projected.put("initiator", task.getInitiator());
        projected.put("status", task.getStatus());
        projected.put("progress", progress);
        projected.put("progressStage", task.getProgressStage());
        projected.put("createdAt", task.getCreatedAt());
        projected.put("startedAt", task.getStartedAt());
        projected.put("completedAt", task.getCompletedAt());
        projected.put("processingTimeMs", task.getProcessingTimeMs());
        projected.put("isAttack", task.getIsAttack());
        projected.put("attackBudget", task.getAttackBudget());
        projected.put("enablePrivacy", task.getEnablePrivacy());
        projected.put("modelSemantics", task.getModelSemantics());
        projected.put("modelSnapshot", task.getModelSnapshot());
        projected.put("outcome", task.getOutcome());
        projected.put("modelComplete", task.getModelComplete());
        projected.put("violatedSpecCount", task.getViolatedSpecCount());
        projected.put("disabledRuleCount", task.getDisabledRuleCount());
        projected.put("skippedSpecCount", task.getSkippedSpecCount());
        projected.put("generationIssues", safeList(task.getGenerationIssues()));
        projected.put("specResults", VerificationToolPresenter.specResults(task.getSpecResults()));
        projected.put("checkLogCount", safeList(task.getCheckLogs()).size());
        projected.put("errorMessage", task.getErrorMessage());
        return projected;
    }
}
