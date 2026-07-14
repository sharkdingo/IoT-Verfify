package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class VerifyModelTool extends AbstractAiTool {

    private final BoardDataConverter boardDataConverter;
    private final VerificationService verificationService;

    public VerifyModelTool(BoardDataConverter boardDataConverter,
                           VerificationService verificationService,
                           ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardDataConverter = boardDataConverter;
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "verify_model";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("isAttack", Map.of(
                "type", "boolean",
                "description", "Include compromised device-instance and automation-link behavior. A device instance is a budget point only when it has a declared falsifiable reading or is a TAP command target; each submitted TAP rule's command-delivery link is another point. Inert devices are excluded. Declared falsifiable readings may vary within their domains; once a target or automation link is selected as compromised, that command is dropped. Other device-internal transitions are not frozen. Default false."
        ));
        props.put("attackBudget", Map.of(
                "type", "integer",
                "description", "Maximum compromised behavior-changing device-instance or automation-link points (1-50 when attack modeling is enabled, and no more than the effective attack surface returned by the model). Verification checks every modeled branch within this upper bound. Omit it or use 0 when attack modeling is disabled; a positive disabled budget is rejected. Default 1 when enabled."
        ));
        props.put("enablePrivacy", Map.of(
                "type", "boolean",
                "description", "Track private-data labels through automation chains. Privacy conditions force this on even when false. This models label propagation, not access control or encryption. Default false."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return LlmToolSpec.of(getName(), "Run NuSMV formal verification on the current board. " +
                "Atomically snapshots all devices, environment values, rules, specifications, and referenced templates from the board. " +
                "Returns whether every emitted specification was satisfied, plus generation warnings " +
                "and property-violation details. " +
                "Requires at least one device and one specification on the board.", schema);
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
            requireOnlyFields(args, "arguments", Set.of("isAttack", "attackBudget", "enablePrivacy"));
            boolean isAttack = booleanArg(args, "isAttack", false);
            int attackBudget = attackBudgetArg(args, isAttack);
            boolean enablePrivacy = booleanArg(args, "enablePrivacy", false);

            ModelInputSnapshot board = boardDataConverter.getModelInputSnapshot(userId);
            List<DeviceVerificationDto> devices = board.devices();
            List<RuleDto> rules = board.rules();
            List<SpecificationDto> specs = board.specifications();

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }
            if (specs.isEmpty()) {
                return errorJson("No specifications found on the board. Please add at least one specification to verify.",
                        "VALIDATION_ERROR", 400);
            }

            log.info("Executing verify_model: {} devices, {} rules, {} specs, attack={}, attackBudget={}, privacy={}",
                    devices.size(), rules.size(), specs.size(), isAttack, attackBudget, enablePrivacy);

            VerificationRequestDto request = new VerificationRequestDto();
            request.setDevices(devices);
            request.setEnvironmentVariables(board.environmentVariables());
            request.setRules(rules);
            request.setSpecs(specs);
            request.setAttack(isAttack);
            request.setAttackBudget(attackBudget);
            request.setEnablePrivacy(enablePrivacy);

            VerificationResultDto result = verificationService.verifyWithTemplateSnapshot(
                    userId, request, board.templateManifests());

            Map<String, Object> summary = new LinkedHashMap<>();
            summary.put("outcome", result.getOutcome());
            summary.put("modelComplete", result.isModelComplete());
            summary.put("disabledRuleCount", result.getDisabledRuleCount());
            summary.put("skippedSpecCount", result.getSkippedSpecCount());
            summary.put("requestedSpecCount", specs.size());
            summary.put("emittedSpecCount", result.getSpecResults() != null ? result.getSpecResults().size() : 0);
            summary.put("violationCount", countFailedSpecs(result));
            summary.put("specResults", presentSpecResults(result.getSpecResults()));
            summary.put("generationIssues", result.getGenerationIssues());
            summary.put("isAttack", Boolean.TRUE.equals(result.getIsAttack()));
            summary.put("attackBudget", result.getAttackBudget());
            summary.put("enablePrivacy", result.isEnablePrivacy());
            summary.put("modelSemantics", result.getModelSemantics());
            summary.put("modelSnapshot", result.getModelSnapshot());
            summary.put("historyPersistence", result.getHistoryPersistence());

            if (result.getOutcome() == VerificationOutcome.VIOLATED && result.getTraces() != null) {
                summary.put("traceCount", result.getTraces().size());
                List<Map<String, Object>> traceSummaries = new ArrayList<>();
                for (TraceDto trace : result.getTraces()) {
                    Map<String, Object> ts = new LinkedHashMap<>();
                    ts.put("traceId", trace.getId());
                    SpecificationDto violatedSpec = trace.getViolatedSpec();
                    if (violatedSpec != null) {
                        ts.put("violatedSpecificationLabel", violatedSpec.getTemplateLabel());
                        ts.put("formulaPreview", violatedSpec.getFormula());
                    }
                    ts.put("stateCount", trace.getStates() != null ? trace.getStates().size() : 0);
                    traceSummaries.add(ts);
                }
                summary.put("traces", traceSummaries);
            }

            if (result.getCheckLogs() != null && !result.getCheckLogs().isEmpty()) {
                summary.put("checkLogs", result.getCheckLogs());
            }

            String message = switch (result.getOutcome() != null
                    ? result.getOutcome() : VerificationOutcome.INCONCLUSIVE) {
                case SATISFIED -> result.isModelComplete()
                        ? "All emitted specifications were satisfied on the complete generated model."
                        : "Emitted specifications were satisfied, but the generated model was incomplete.";
                case VIOLATED -> "Verification found one or more specification violations.";
                case INCONCLUSIVE -> "Verification was inconclusive; no safety conclusion was produced.";
            };
            message = appendHistoryPersistenceNotice(message, result.getHistoryPersistence());
            summary.put("message", message);
            return successJson(summary, message);
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("verify_model busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (SmvGenerationException e) {
            log.warn("verify_model generation failed [{}]: {}", e.getErrorCategory(), e.getMessage());
            return errorJson(e.getMessage(),
                    "SMV_GENERATION_ERROR",
                    500,
                    Map.of("errorCategory", e.getErrorCategory()));
        } catch (BaseException e) {
            log.warn("verify_model business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("verify_model failed", e);
            return errorJson("Verification failed.", "INTERNAL_ERROR", 500);
        }
    }

    private int countFailedSpecs(VerificationResultDto result) {
        if (result == null || result.getSpecResults() == null) {
            return 0;
        }
        return (int) result.getSpecResults().stream()
                .filter(specResult -> specResult != null
                        && specResult.getOutcome() == VerificationOutcome.VIOLATED)
                .count();
    }

    private String appendHistoryPersistenceNotice(String message, RunPersistenceDto persistence) {
        if (persistence == null || persistence.getStatus() == null) {
            return message + " Run-history persistence status was unavailable.";
        }
        return switch (persistence.getStatus()) {
            case SAVED -> message + " The result was added to run history.";
            case FAILED -> message + " The result was produced but was not added to run history.";
            case OUTCOME_UNKNOWN -> message
                    + " The result was produced, but whether it entered run history could not be confirmed; refresh history before retrying.";
            case NOT_REQUESTED -> message + " No run-history save was requested.";
        };
    }

    /**
     * Chat-facing projection. Persistence ids are unnecessary for interpretation or the
     * follow-up fix flow, which is addressed by traceId, so keep them out of ordinary AI output.
     */
    private List<Map<String, Object>> presentSpecResults(List<SpecResultDto> specResults) {
        if (specResults == null || specResults.isEmpty()) {
            return List.of();
        }
        List<Map<String, Object>> presented = new ArrayList<>(specResults.size());
        for (SpecResultDto specResult : specResults) {
            if (specResult == null) {
                continue;
            }
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("specificationLabel", specResult.getSpecificationLabel());
            row.put("formulaPreview", specResult.getFormulaPreview());
            row.put("formulaKind", specResult.getFormulaKind());
            row.put("outcome", specResult.getOutcome());
            row.put("checkedExpression", specResult.getExpression());
            presented.add(row);
        }
        return List.copyOf(presented);
    }
}
