package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.BoardReplacementStaleException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Atomically applies the latest validated scenario draft from the current chat session. */
@Slf4j
@Component
public class ApplyScenarioTool extends AbstractAiTool {

    private final AiScenarioDraftStore draftStore;
    private final ScenarioDraftBatchMapper batchMapper;
    private final BoardStorageService boardStorageService;

    public ApplyScenarioTool(AiScenarioDraftStore draftStore,
                             ScenarioDraftBatchMapper batchMapper,
                             BoardStorageService boardStorageService,
                             ObjectMapper objectMapper) {
        super(objectMapper);
        this.draftStore = draftStore;
        this.batchMapper = batchMapper;
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "apply_scenario";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> properties = new LinkedHashMap<>();
        properties.put("confirmed", Map.of(
                "type", "boolean",
                "description", "Use false to preview the atomic full-scene replacement. Use true only in a later user turn that explicitly confirms that exact preview."
        ));
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", properties, List.of("confirmed"));
        return LlmToolSpec.of(
                getName(),
                "Preview or, after explicit later confirmation, atomically replace the board with the latest validated recommend_scenario draft from this chat session. Never delete devices individually to apply a scene draft.",
                schema);
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args = parseArgs(argsJson);
            requireOnlyFields(args, "arguments", Set.of("confirmed"));
            boolean confirmed = booleanArg(args, "confirmed", false);
            String sessionId = requireChatSession();

            boolean userConfirmed = UserContextHolder.isSceneReplacementConfirmed();
            AiScenarioDraftStore.PendingApplication pending = userConfirmed
                    ? draftStore.pendingApplication(userId, sessionId).orElse(null)
                    : null;
            if (pending == null) {
                return preview(userId, sessionId);
            }
            if (!confirmed) {
                log.info("Applying pending AI scenario from explicit server-side confirmation despite model confirmed=false: userId={}, sessionId={}",
                        userId, sessionId);
            }

            BoardBatchDto batch = batchMapper.toBatch(
                    pending.scene(), pending.preview().getImpactToken());
            BoardBatchDto saved = boardStorageService.saveBoardBatch(userId, batch);
            draftStore.completeApplication(userId, sessionId);

            Map<String, Object> response = new LinkedHashMap<>();
            response.put("message", "The scenario draft replaced the current board atomically. Its rules and specifications have not been formally verified.");
            response.put("operation", "replaced");
            response.put("scenarioName", pending.scenarioName());
            response.put("deviceCount", safeList(saved.getNodes()).size());
            response.put("environmentVariableCount", safeList(saved.getEnvironmentVariables()).size());
            response.put("ruleCount", safeList(saved.getRules()).size());
            response.put("specificationCount", safeList(saved.getSpecs()).size());
            response.put("createdTemplateCount", safeList(saved.getCreatedTemplates()).size());
            response.put("verificationStatus", "NOT_VERIFIED");
            putVerificationReadiness(response, pending.scene());
            log.info("Applied AI scenario draft atomically: userId={}, sessionId={}, scenarioName={}",
                    userId, sessionId, pending.scenarioName());
            return successJson(response, "Scenario replacement result unavailable.");
        } catch (ArgParseException e) {
            return e.getErrorResponse();
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (BoardReplacementStaleException e) {
            return stalePreview(userId, e);
        } catch (BaseException e) {
            log.warn("apply_scenario business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (IllegalArgumentException e) {
            return errorJson(e.getMessage(), "SCENARIO_DRAFT_NOT_FOUND", 404);
        } catch (Exception e) {
            log.error("apply_scenario failed", e);
            return errorJson("Failed to apply the stored scenario draft. No confirmed replacement result is available.",
                    "INTERNAL_ERROR", 500);
        }
    }

    private String preview(Long userId, String sessionId) {
        AiScenarioDraftStore.DraftSnapshot draft = draftStore.latestDraft(userId, sessionId)
                .orElseThrow(() -> new IllegalArgumentException(
                        "No validated scenario draft is available in this chat session. Generate one before applying it."));
        BoardReplacementPreviewDto current = boardStorageService.previewBoardReplacement(userId);
        AiScenarioDraftStore.PendingApplication pending = draftStore
                .beginApplication(userId, sessionId, current)
                .orElseThrow(() -> new IllegalArgumentException(
                        "No validated scenario draft is available in this chat session. Generate one before applying it."));

        Map<String, Object> response = replacementPreviewResponse(pending, current);
        response.put("message", "No changes were made. Explicit user confirmation is required before atomically replacing the current board with this scenario draft.");
        response.put("operation", "preview");
        response.put("requiresUserConfirmation", true);
        return readOnlySuccessJson(response, "Scenario replacement preview unavailable.");
    }

    private String stalePreview(Long userId, BoardReplacementStaleException exception) {
        String sessionId = requireChatSession();
        BoardReplacementPreviewDto current = exception.getCurrentPreview();
        AiScenarioDraftStore.PendingApplication refreshed = draftStore
                .refreshPendingApplication(userId, sessionId, current)
                .orElse(null);
        if (refreshed == null) {
            return errorJson(exception.getMessage(), "BOARD_REPLACEMENT_STALE", 409);
        }
        Map<String, Object> extras = replacementPreviewResponse(refreshed, current);
        extras.put("requiresUserConfirmation", true);
        return errorJson(exception.getMessage(), "BOARD_REPLACEMENT_STALE", 409, extras);
    }

    private Map<String, Object> replacementPreviewResponse(
            AiScenarioDraftStore.PendingApplication pending,
            BoardReplacementPreviewDto current) {
        Map<String, Object> response = new LinkedHashMap<>();
        response.put("scenarioName", pending.scenarioName());
        response.put("currentDeviceCount", current.getDeviceCount());
        response.put("currentEnvironmentVariableCount", current.getEnvironmentVariableCount());
        response.put("currentRuleCount", current.getRuleCount());
        response.put("currentSpecificationCount", current.getSpecificationCount());
        JsonNode scene = pending.scene();
        response.put("replacementDeviceCount", scene.path("devices").size());
        response.put("replacementEnvironmentVariableCount", scene.path("environmentVariables").size());
        response.put("replacementRuleCount", scene.path("rules").size());
        response.put("replacementSpecificationCount", scene.path("specs").size());
        putVerificationReadiness(response, scene);
        return response;
    }

    private void putVerificationReadiness(Map<String, Object> response, JsonNode scene) {
        ScenarioVerificationReadiness.Status readiness = ScenarioVerificationReadiness.assess(scene);
        response.put("verificationReady", readiness.verificationReady());
        response.put("readinessIssues", readiness.readinessIssues());
    }

    private String requireChatSession() {
        String sessionId = UserContextHolder.getChatSessionId();
        if (sessionId == null || sessionId.isBlank()) {
            throw new IllegalArgumentException(
                    "Scenario application requires an active chat session containing a validated draft.");
        }
        return sessionId;
    }
}
