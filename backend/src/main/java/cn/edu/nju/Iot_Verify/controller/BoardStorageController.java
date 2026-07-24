package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRulesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRelatedDevicesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckDuplicateRuleTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckRuleSimilarityTool;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.RecommendScenarioTool;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.ScenarioObjectiveTargets;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.ScenarioVerificationReadiness;
import cn.edu.nju.Iot_Verify.component.aitool.spec.RecommendSpecificationsTool;
import cn.edu.nju.Iot_Verify.component.board.BoardBatchRequestParser;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardSemanticSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.board.CollectionMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeUpdateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceUpdateResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceBatchCreateRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceDeleteRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRenameRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetRequestDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetResultDto;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStatusDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.DeviceRecommendationDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.DeviceRecommendationRequestDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.PortableSceneDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.RecommendationAdjustmentItemDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.RecommendationLimits;
import cn.edu.nju.Iot_Verify.dto.recommendation.RecommendationFilterItemDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.RecommendationResponseDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.RuleRecommendationDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioRecommendationRequestDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioRecommendationResponseDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioObjectiveIssueDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioObjectiveTargetsDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioReadinessIssueDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.ScenarioSemanticWarningDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.StandaloneRecommendationRequestDto;
import cn.edu.nju.Iot_Verify.dto.recommendation.SpecificationRecommendationDto;
import cn.edu.nju.Iot_Verify.dto.rule.DuplicateRuleCheckResultDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleOrderRequestDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleSimilarityResultDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BadGatewayException;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.InteractiveAiExecutionService;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Validated
@RestController
@RequestMapping("/api/board")
@RequiredArgsConstructor
public class BoardStorageController {

    private static final Set<String> DUPLICATE_REASON_CODES = Set.of(
            "NO_EXISTING_RULES",
            "EXACT_MATCH",
            "TRIGGER_SET_CONTAINS_OTHER",
            "SAME_TRIGGER_SHAPE_DIFFERENT_VALUES",
            "PARTIAL_TRIGGER_OVERLAP",
            "NO_MATCHING_SIGNATURE");
    private static final Set<String> SIMILARITY_REASON_CODES = Set.of(
            "NO_EXISTING_RULES",
            "AI_DUPLICATE",
            "AI_SIMILAR",
            "AI_HIGH_SCORE_REVIEW",
            "AI_NO_SIGNIFICANT_SIMILARITY");

    private final BoardStorageService boardService;
    private final RecommendRulesTool recommendRulesTool;
    private final RecommendRelatedDevicesTool recommendRelatedDevicesTool;
    private final CheckDuplicateRuleTool checkDuplicateRuleTool;
    private final CheckRuleSimilarityTool checkRuleSimilarityTool;
    private final RecommendSpecificationsTool recommendSpecificationsTool;
    private final RecommendScenarioTool recommendScenarioTool;
    private final ObjectMapper objectMapper;
    private final DeviceTemplateSchemaValidator deviceTemplateSchemaValidator;
    private final BoardBatchRequestParser boardBatchRequestParser;
    private final InteractiveAiExecutionService interactiveAiExecutionService;

    @GetMapping("/snapshot")
    public Result<BoardSemanticSnapshotDto> getSnapshot(@CurrentUser Long userId) {
        return Result.success(boardService.getSemanticSnapshot(userId));
    }

    @GetMapping("/nodes")
    public Result<List<DeviceNodeDto>> getNodes(@CurrentUser Long userId) {
        return Result.success(boardService.getNodes(userId));
    }

    @PostMapping("/nodes")
    public Result<DeviceMutationResultDto> addNodes(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody DeviceBatchCreateRequestDto request) {
        return Result.success(boardService.addNodes(
                userId, request.getDevices(), request.getEnvironmentVariablePatches()));
    }

    @PutMapping("/nodes/{nodeId}/layout")
    public Result<DeviceUpdateResultDto> updateNodeLayout(
            @CurrentUser Long userId,
            @PathVariable String nodeId,
            @NotNull @Valid @RequestBody DeviceLayoutDto layout) {
        return Result.success(boardService.updateNodeLayout(userId, nodeId, layout));
    }

    @PutMapping("/nodes/{nodeId}/runtime")
    public Result<DeviceUpdateResultDto> updateNodeRuntime(
            @CurrentUser Long userId,
            @PathVariable String nodeId,
            @NotNull @Valid @RequestBody DeviceRuntimeUpdateDto runtime) {
        return Result.success(boardService.updateNodeRuntime(userId, nodeId, runtime));
    }

    @PatchMapping("/nodes/{nodeId}/label")
    public Result<DeviceMutationResultDto> renameNode(
            @CurrentUser Long userId,
            @PathVariable String nodeId,
            @NotNull @Valid @RequestBody DeviceRenameRequestDto request) {
        return Result.success(boardService.renameNode(
                userId, nodeId, request.getLabel(), request.getExpectedLabel()));
    }

    @GetMapping("/nodes/{nodeId}/deletion-preview")
    public Result<DeviceDeletionResultDto> previewNodeDeletion(
            @CurrentUser Long userId,
            @PathVariable String nodeId) {
        return Result.success(boardService.previewNodeDeletion(userId, nodeId));
    }

    @PostMapping("/nodes/{nodeId}/delete")
    public Result<DeviceDeletionResultDto> deleteNode(
            @CurrentUser Long userId,
            @PathVariable String nodeId,
            @NotNull @Valid @RequestBody DeviceDeleteRequestDto request) {
        return Result.success(boardService.deleteNodeCascade(
                userId,
                nodeId,
                request.getImpactToken()));
    }

    @GetMapping("/environment")
    public Result<List<BoardEnvironmentVariableDto>> getEnvironment(@CurrentUser Long userId) {
        return Result.success(boardService.getEnvironmentVariables(userId));
    }

    @PostMapping("/environment")
    public Result<EnvironmentMutationResultDto> saveEnvironment(
            @CurrentUser Long userId,
            @NotNull @Size(max = RequestLimits.MAX_ENVIRONMENT_VARIABLES,
                    message = "At most 200 environment variables can be updated at once")
            @Valid @RequestBody List<@Valid @NotNull(message = "Environment variable item cannot be null") BoardEnvironmentVariableDto> variables) {
        return Result.success(boardService.saveEnvironmentVariables(userId, variables));
    }

    @GetMapping("/specs")
    public Result<List<SpecificationDto>> getSpecs(@CurrentUser Long userId) {
        return Result.success(boardService.getSpecs(userId));
    }

    @PostMapping("/specs")
    public Result<CollectionMutationResultDto<SpecificationDto>> addSpec(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody SpecificationDto spec) {
        return Result.success(boardService.addSpec(userId, spec));
    }

    @DeleteMapping("/specs/{specId}")
    public Result<CollectionMutationResultDto<SpecificationDto>> removeSpec(
            @CurrentUser Long userId,
            @PathVariable String specId) {
        return Result.success(boardService.removeSpec(userId, specId));
    }

    @GetMapping("/rules")
    public Result<List<RuleDto>> getRules(@CurrentUser Long userId) {
        return Result.success(boardService.getRules(userId));
    }

    @PostMapping("/rules")
    public Result<CollectionMutationResultDto<RuleDto>> addRule(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody RuleDto rule) {
        return Result.success(boardService.addRule(userId, rule));
    }

    @PutMapping("/rules/order")
    public Result<List<RuleDto>> reorderRules(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody RuleOrderRequestDto request) {
        return Result.success(boardService.reorderRules(userId, request.getRuleIds()));
    }

    @DeleteMapping("/rules/{ruleId}")
    public Result<CollectionMutationResultDto<RuleDto>> removeRule(
            @CurrentUser Long userId,
            @PathVariable long ruleId) {
        return Result.success(boardService.removeRule(userId, ruleId));
    }

    /**
     * Explicit atomic replacement of scene collections. Ordinary device/rule/spec mutations use
     * targeted endpoints; this command is reserved for confirmed scene import and scene clear.
     */
    @GetMapping("/replacement-preview")
    public Result<BoardReplacementPreviewDto> previewReplacement(@CurrentUser Long userId) {
        return Result.success(boardService.previewBoardReplacement(userId));
    }

    @PostMapping("/batch")
    public Result<BoardBatchDto> saveBatch(@CurrentUser Long userId, @NotNull @RequestBody JsonNode body) {
        return Result.success(boardService.saveBoardBatch(userId, boardBatchRequestParser.parse(body)));
    }

    @GetMapping("/layout")
    public Result<BoardLayoutDto> getLayout(@CurrentUser Long userId) {
        return Result.success(boardService.getLayout(userId));
    }

    @PostMapping("/layout")
    public Result<BoardLayoutDto> saveLayout(@CurrentUser Long userId, @NotNull @Valid @RequestBody BoardLayoutDto layout) {
        return Result.success(boardService.saveLayout(userId, layout));
    }

    @GetMapping("/templates")
    public Result<List<DeviceTemplateDto>> getTemplates(@CurrentUser Long userId) {
        return Result.success(boardService.getDeviceTemplates(userId));
    }

    @GetMapping("/templates/schema")
    public Result<JsonNode> getTemplateSchema() {
        return Result.success(deviceTemplateSchemaValidator.getSchemaNode());
    }

    @PostMapping("/templates")
    public Result<DeviceTemplateDto> addTemplate(@CurrentUser Long userId, @NotNull @RequestBody JsonNode body) {
        if (!body.isObject()) {
            throw new BadRequestException("Template request body must be a JSON object.");
        }
        String name = body.path("name").asText(null);
        deviceTemplateSchemaValidator.validateRawManifest(name, body.get("manifest"));
        DeviceTemplateDto dto;
        try {
            dto = objectMapper.treeToValue(body, DeviceTemplateDto.class);
        } catch (JsonProcessingException e) {
            throw new BadRequestException("Template request body is invalid: " + e.getOriginalMessage(), e);
        }
        return Result.success(boardService.addDeviceTemplate(userId, dto));
    }

    @GetMapping("/templates/{id}/deletion-preview")
    public Result<DeviceTemplateDeletionResultDto> previewTemplateDeletion(
            @CurrentUser Long userId, @PathVariable Long id) {
        return Result.success(boardService.previewDeviceTemplateDeletion(userId, id));
    }

    @PostMapping("/templates/{id}/delete")
    public Result<DeviceTemplateDeletionResultDto> deleteTemplate(
            @CurrentUser Long userId,
            @PathVariable Long id,
            @NotNull @Valid @RequestBody DeviceTemplateDeletionRequestDto request) {
        return Result.success(boardService.deleteDeviceTemplate(userId, id, request.getImpactToken()));
    }

    @GetMapping("/templates/defaults/reset-preview")
    public Result<DefaultTemplateResetResultDto> previewDefaultTemplateReset(
            @CurrentUser Long userId) {
        return Result.success(boardService.previewDefaultTemplateReset(userId));
    }

    @PostMapping("/templates/defaults/reset")
    public Result<DefaultTemplateResetResultDto> resetDefaultTemplates(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody DefaultTemplateResetRequestDto request) {
        return Result.success(boardService.resetDefaultTemplates(userId, request.getImpactToken()));
    }

    /**
     * 获取规则推荐
     * @param userId 用户ID
     * @param maxRecommendations 最大推荐数量
     * @param category 分类筛选
     * @return 规则推荐列表
     */
    @PostMapping("/rules/recommend")
    public Result<RecommendationResponseDto<RuleRecommendationDto>> recommendRules(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody StandaloneRecommendationRequestDto requestBody) {
        return recommendRules(userId,
                requestBody.getMaxRecommendations(), requestBody.getCategory(), requestBody.getLanguage(),
                requestBody.getUserRequirement(), requestBody.getRequestId());
    }

    Result<RecommendationResponseDto<RuleRecommendationDto>> recommendRules(
            Long userId, Integer maxRecommendations, String category, String language,
            String userRequirement, String requestId) {

        return interactiveAiExecutionService.execute(userId, requestId, () -> {
        try {
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.PREPARING_CONTEXT);
            String args = objectMapper.writeValueAsString(Map.of(
                    "maxRecommendations", maxRecommendations,
                    "category", category,
                    "language", language,
                    "userRequirement", userRequirement));
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.REQUESTING_MODEL);
            String result = recommendRulesTool.execute(args);

            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.VALIDATING_RESULT);
            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseRecommendationResponse(
                    resultMap, RuleRecommendationDto.class, true, "AI rule recommendation"));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process rule recommendations", e);
        }
        });
    }

    /**
     * 根据画布中所有设备推荐新设备
     * @param userId 用户ID
     * @param requestBody 包含设备列表和模板列表的请求体
     * @return 设备推荐列表
     */
    @PostMapping("/devices/recommend")
    public Result<RecommendationResponseDto<DeviceRecommendationDto>> recommendDevices(
            @CurrentUser Long userId,
            @RequestParam
            @Size(min = RequestLimits.MIN_REQUEST_ID_LENGTH, max = RequestLimits.MAX_REQUEST_ID_LENGTH,
                    message = "Request ID must contain 8 to 80 characters")
            @Pattern(regexp = RequestLimits.REQUEST_ID_PATTERN,
                    message = "Request ID contains unsupported characters") String requestId,
            @NotNull @Valid @RequestBody DeviceRecommendationRequestDto requestBody) {

        return interactiveAiExecutionService.execute(userId, requestId, () -> {
        try {
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.PREPARING_CONTEXT);
            String argsJson = objectMapper.writeValueAsString(requestBody);
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.REQUESTING_MODEL);
            String result = recommendRelatedDevicesTool.executeBoardRecommendations(argsJson);

            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.VALIDATING_RESULT);
            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseRecommendationResponse(
                    resultMap, DeviceRecommendationDto.class, true, "AI device recommendation"));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process device recommendations", e);
        }
        });
    }

    /**
     * 检查规则是否重复
     * 当用户添加一条规则后，检查该规则是否与现有规则重复
     * @param userId 用户ID
     * @param rule 新添加的规则
     * @return 重复检查结果
     */
    @PostMapping("/rules/check-duplicate")
    public Result<DuplicateRuleCheckResultDto> checkDuplicateRule(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody RuleDto rule) {

        try {
            String args = objectMapper.writeValueAsString(
                    Map.of("newRule", toRuleCandidateToolPayload(rule)));
            String result = checkDuplicateRuleTool.execute(args);

            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseDuplicateRuleCheckResult(resultMap));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process duplicate rule check", e);
        }
    }

    /**
     * 获取规约推荐
     * @param userId 用户ID
     * @param maxRecommendations 最大推荐数量
     * @param category 分类筛选
     * @return 规约推荐列表
     */
    @PostMapping("/specs/recommend")
    public Result<RecommendationResponseDto<SpecificationRecommendationDto>> recommendSpecs(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody StandaloneRecommendationRequestDto requestBody) {
        return recommendSpecs(userId,
                requestBody.getMaxRecommendations(), requestBody.getCategory(), requestBody.getLanguage(),
                requestBody.getUserRequirement(), requestBody.getRequestId());
    }

    Result<RecommendationResponseDto<SpecificationRecommendationDto>> recommendSpecs(
            Long userId, Integer maxRecommendations, String category, String language,
            String userRequirement, String requestId) {

        return interactiveAiExecutionService.execute(userId, requestId, () -> {
        try {
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.PREPARING_CONTEXT);
            String args = objectMapper.writeValueAsString(Map.of(
                    "maxRecommendations", maxRecommendations,
                    "category", category,
                    "language", language,
                    "userRequirement", userRequirement));
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.REQUESTING_MODEL);
            String result = recommendSpecificationsTool.execute(args);

            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.VALIDATING_RESULT);
            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseRecommendationResponse(
                    resultMap, SpecificationRecommendationDto.class, false,
                    "AI specification recommendation"));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process specification recommendations", e);
        }
        });
    }

    /**
     * Run an explicit AI semantic similarity check for a candidate rule.
     * This endpoint may call the configured LLM and is not used as a required save gate.
     */
    @PostMapping("/rules/check-similarity")
    public Result<RuleSimilarityResultDto> checkRuleSimilarity(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody RuleDto rule) {

        try {
            String args = objectMapper.writeValueAsString(
                    Map.of("newRule", toRuleCandidateToolPayload(rule)));
            String result = checkRuleSimilarityTool.execute(args);

            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseRuleSimilarityResult(resultMap));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process AI rule similarity check", e);
        }
    }

    /**
     * Generate one coupled, importable scene recommendation.
     */
    @PostMapping("/scenario/recommend")
    public Result<ScenarioRecommendationResponseDto> recommendScenario(
            @CurrentUser Long userId,
            @RequestParam
            @Size(min = RequestLimits.MIN_REQUEST_ID_LENGTH, max = RequestLimits.MAX_REQUEST_ID_LENGTH,
                    message = "Request ID must contain 8 to 80 characters")
            @Pattern(regexp = RequestLimits.REQUEST_ID_PATTERN,
                    message = "Request ID contains unsupported characters") String requestId,
            @NotNull @Valid @RequestBody ScenarioRecommendationRequestDto requestBody) {

        return interactiveAiExecutionService.execute(userId, requestId, () -> {
        try {
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.PREPARING_CONTEXT);
            String argsJson = objectMapper.writeValueAsString(requestBody);
            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.REQUESTING_MODEL);
            String result = recommendScenarioTool.execute(argsJson);

            interactiveAiExecutionService.markStage(
                    userId, requestId, InteractiveOperationStage.VALIDATING_RESULT);
            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(parseScenarioRecommendationResponse(resultMap, requestBody));
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process scenario recommendations", e);
        }
        });
    }

    @DeleteMapping("/recommendations/{requestId}")
    public Result<Boolean> cancelRecommendation(
            @CurrentUser Long userId,
            @PathVariable
            @Size(min = RequestLimits.MIN_REQUEST_ID_LENGTH, max = RequestLimits.MAX_REQUEST_ID_LENGTH,
                    message = "Request ID must contain 8 to 80 characters")
            @Pattern(regexp = RequestLimits.REQUEST_ID_PATTERN,
                    message = "Request ID contains unsupported characters") String requestId) {
        return Result.success(interactiveAiExecutionService.cancel(userId, requestId));
    }

    @GetMapping("/recommendations/{requestId}")
    public Result<InteractiveOperationStatusDto> getRecommendationStatus(
            @CurrentUser Long userId,
            @PathVariable
            @Size(min = RequestLimits.MIN_REQUEST_ID_LENGTH, max = RequestLimits.MAX_REQUEST_ID_LENGTH,
                    message = "Request ID must contain 8 to 80 characters")
            @Pattern(regexp = RequestLimits.REQUEST_ID_PATTERN,
                    message = "Request ID contains unsupported characters") String requestId) {
        return Result.success(interactiveAiExecutionService.getStatus(userId, requestId));
    }

    /**
     * Check if a Tool response is an error JSON and throw the appropriate exception.
     * Tool error format: {"error":"...", "errorCode":"...", "status": <int>}
     */
    private void throwIfToolError(Map<String, Object> resultMap) {
        if (!resultMap.containsKey("errorCode")) {
            return;
        }
        String message = String.valueOf(resultMap.getOrDefault("error", "AI tool error"));
        Object statusObj = resultMap.get("status");
        int status = (statusObj instanceof Number n) ? n.intValue() : 500;

        switch (status) {
            case 400 -> throw new BadRequestException(message);
            case 401 -> throw new UnauthorizedException(message);
            case 403 -> throw new ForbiddenException(message);
            case 404 -> throw new ResourceNotFoundException(message);
            case 409 -> throw new ConflictException(message);
            case 422 -> throw new ValidationException(message);
            case 502 -> throw new BadGatewayException(message);
            case 503 -> throw new ServiceUnavailableException(message);
            default  -> throw new InternalServerException(message);
        }
    }

    private <T> RecommendationResponseDto<T> parseRecommendationResponse(
            Map<String, Object> result,
            Class<T> candidateType,
            boolean requireAdjustments,
            String context) {
        Set<String> allowedFields = requireAdjustments
                ? Set.of("message", "count", "requestedCount", "validatedCount",
                        "filteredCount", "filteredItems", "adjustedCount", "adjustedItems",
                        "rawCandidateCount", "inspectedCount", "truncatedCount", "recommendations")
                : Set.of("message", "count", "requestedCount", "validatedCount",
                        "filteredCount", "filteredItems", "rawCandidateCount",
                        "inspectedCount", "truncatedCount", "recommendations");
        requireOnlyRecommendationFields(result, allowedFields, context);
        RecommendationAudit audit = parseRecommendationAudit(result, requireAdjustments, context);
        List<?> rawRecommendations = requireRecommendationList(result, "recommendations", context);
        List<T> recommendations = convertRecommendationItems(rawRecommendations, candidateType, context);
        validateKeptRecommendationCandidates(recommendations, candidateType, context);
        if (audit.count() != recommendations.size()
                || audit.validatedCount() != recommendations.size()) {
            throw invalidRecommendationResult(
                    context, "count and validatedCount must match kept recommendations");
        }

        RecommendationResponseDto<T> response = new RecommendationResponseDto<>();
        response.setMessage(audit.message());
        response.setCount(audit.count());
        response.setRequestedCount(audit.requestedCount());
        response.setValidatedCount(audit.validatedCount());
        response.setFilteredCount(audit.filteredCount());
        response.setFilteredItems(audit.filteredItems());
        response.setAdjustedCount(audit.adjustedCount());
        response.setAdjustedItems(audit.adjustedItems());
        response.setRawCandidateCount(audit.rawCandidateCount());
        response.setInspectedCount(audit.inspectedCount());
        response.setTruncatedCount(audit.truncatedCount());
        response.setRecommendations(recommendations);
        return response;
    }

    private <T> void validateKeptRecommendationCandidates(
            List<T> recommendations,
            Class<T> candidateType,
            String context) {
        for (int index = 0; index < recommendations.size(); index++) {
            Object candidate = recommendations.get(index);
            if (candidate instanceof RuleRecommendationDto rule) {
                if (isBlank(rule.getName()) || rule.getConditions() == null
                        || rule.getConditions().isEmpty() || rule.getCommand() == null) {
                    throw invalidRecommendationResult(
                            context, "recommendations[" + index
                                    + "] lacks saved rule name, conditions, or command");
                }
            } else if (candidate instanceof SpecificationRecommendationDto specification) {
                if (isBlank(specification.getRationale())
                        || specification.getTemplateId() == null
                        || !specification.getTemplateId().matches("^[1-7]$")
                        || specification.getAConditions() == null
                        || specification.getIfConditions() == null
                        || specification.getThenConditions() == null) {
                    throw invalidRecommendationResult(
                            context, "recommendations[" + index
                                    + "] lacks rationale, legal templateId, or condition collections");
                }
            } else if (candidate instanceof DeviceRecommendationDto device) {
                if (isBlank(device.getTemplateName()) || isBlank(device.getSuggestedLabel())) {
                    throw invalidRecommendationResult(
                            context, "recommendations[" + index
                                    + "] lacks device type or effective instance name");
                }
            } else if (candidate == null) {
                throw invalidRecommendationResult(
                        context, "recommendations[" + index + "] is null for " + candidateType.getSimpleName());
            }
        }
    }

    private ScenarioRecommendationResponseDto parseScenarioRecommendationResponse(
            Map<String, Object> result,
            ScenarioRecommendationRequestDto request) {
        String context = "AI scenario recommendation";
        requireOnlyRecommendationFields(result, Set.of(
                "message", "count", "requestedCount", "validatedCount",
                "filteredCount", "filteredItems", "adjustedCount", "adjustedItems",
                "rawCandidateCount", "inspectedCount", "truncatedCount",
                "scenarioName", "rationale", "objectiveTargets", "objectiveStatus", "objectiveIssues",
                "verificationReady", "readinessIssues",
                "semanticWarnings", "scene"), context);
        RecommendationAudit audit = parseRecommendationAudit(result, true, context);
        PortableSceneDto scene = convertRecommendationItem(
                result.get("scene"), PortableSceneDto.class, context, "scene");
        if (!"iot-verify.board-scene".equals(scene.getSchema())
                || !Integer.valueOf(4).equals(scene.getVersion())) {
            throw invalidRecommendationResult(context, "scene schema/version is unsupported");
        }
        if (scene.getTemplates() == null || scene.getDevices() == null
                || scene.getEnvironmentVariables() == null || scene.getRules() == null
                || scene.getSpecs() == null) {
            throw invalidRecommendationResult(context, "scene collections must all be arrays");
        }
        int finalCount = scene.getDevices().size()
                + scene.getEnvironmentVariables().size()
                + scene.getRules().size()
                + scene.getSpecs().size();
        if (audit.count() != finalCount) {
            throw invalidRecommendationResult(context, "count must match final scene items");
        }
        ScenarioObjectiveTargetsDto objectiveTargetsDto = convertRecommendationItem(
                result.get("objectiveTargets"),
                ScenarioObjectiveTargetsDto.class,
                context,
                "objectiveTargets");
        ScenarioObjectiveTargets objectiveTargets = parseScenarioObjectiveTargets(
                objectiveTargetsDto, request, context);
        if (audit.requestedCount() != objectiveTargets.requestedCount()) {
            throw invalidRecommendationResult(
                    context, "requestedCount must equal the sum of objectiveTargets");
        }

        ScenarioRecommendationResponseDto response = new ScenarioRecommendationResponseDto();
        response.setMessage(audit.message());
        response.setCount(audit.count());
        response.setRequestedCount(audit.requestedCount());
        response.setValidatedCount(audit.validatedCount());
        response.setFilteredCount(audit.filteredCount());
        response.setFilteredItems(audit.filteredItems());
        response.setAdjustedCount(audit.adjustedCount());
        response.setAdjustedItems(audit.adjustedItems());
        response.setRawCandidateCount(audit.rawCandidateCount());
        response.setInspectedCount(audit.inspectedCount());
        response.setTruncatedCount(audit.truncatedCount());
        response.setScenarioName(requireRecommendationString(result, "scenarioName", context));
        response.setRationale(requireRecommendationString(result, "rationale", context));
        response.setObjectiveTargets(objectiveTargetsDto);
        String objectiveStatus = requireRecommendationString(result, "objectiveStatus", context);
        List<ScenarioObjectiveIssueDto> objectiveIssues = convertRecommendationItems(
                requireRecommendationList(result, "objectiveIssues", context),
                ScenarioObjectiveIssueDto.class, context);
        boolean verificationReady = requireRecommendationBoolean(result, "verificationReady", context);
        List<ScenarioReadinessIssueDto> readinessIssues = convertRecommendationItems(
                requireRecommendationList(result, "readinessIssues", context),
                ScenarioReadinessIssueDto.class, context);
        List<ScenarioSemanticWarningDto> semanticWarnings = convertRecommendationItems(
                requireRecommendationList(result, "semanticWarnings", context),
                ScenarioSemanticWarningDto.class, context);
        validateScenarioAnalysis(
                scene,
                audit.filteredCount(),
                objectiveTargets,
                objectiveStatus,
                objectiveIssues,
                verificationReady,
                readinessIssues,
                semanticWarnings,
                context);
        response.setObjectiveStatus(objectiveStatus);
        response.setObjectiveIssues(objectiveIssues);
        response.setVerificationReady(verificationReady);
        response.setReadinessIssues(readinessIssues);
        response.setSemanticWarnings(semanticWarnings);
        response.setScene(scene);
        return response;
    }

    private void validateScenarioAnalysis(PortableSceneDto scene,
                                          int filteredCount,
                                          ScenarioObjectiveTargets objectiveTargets,
                                          String objectiveStatus,
                                          List<ScenarioObjectiveIssueDto> objectiveIssues,
                                          boolean verificationReady,
                                          List<ScenarioReadinessIssueDto> readinessIssues,
                                          List<ScenarioSemanticWarningDto> semanticWarnings,
                                          String context) {
        ScenarioVerificationReadiness.Status expected = ScenarioVerificationReadiness.assess(
                objectMapper.valueToTree(scene), filteredCount, "en", objectiveTargets);
        List<String> actualObjectiveCodes = new ArrayList<>();
        for (int index = 0; index < objectiveIssues.size(); index++) {
            ScenarioObjectiveIssueDto issue = objectiveIssues.get(index);
            if (issue == null || isBlank(issue.getCode()) || isBlank(issue.getMessage())) {
                throw invalidRecommendationResult(
                        context, "objectiveIssues[" + index + "] requires non-blank code and message");
            }
            actualObjectiveCodes.add(issue.getCode());
        }
        List<String> expectedObjectiveCodes = expected.objectiveIssues().stream()
                .map(ScenarioVerificationReadiness.Issue::code)
                .toList();
        if (!expected.objectiveStatus().equals(objectiveStatus)
                || !actualObjectiveCodes.equals(expectedObjectiveCodes)) {
            throw invalidRecommendationResult(
                    context, "objectiveStatus/objectiveIssues must match the returned scene");
        }

        List<String> actualCodes = new ArrayList<>();
        for (int index = 0; index < readinessIssues.size(); index++) {
            ScenarioReadinessIssueDto issue = readinessIssues.get(index);
            if (issue == null || isBlank(issue.getCode()) || isBlank(issue.getMessage())) {
                throw invalidRecommendationResult(
                        context, "readinessIssues[" + index + "] requires non-blank code and message");
            }
            actualCodes.add(issue.getCode());
        }
        List<String> expectedCodes = expected.readinessIssues().stream()
                .map(ScenarioVerificationReadiness.Issue::code)
                .toList();
        if (verificationReady != expected.verificationReady() || !actualCodes.equals(expectedCodes)) {
            throw invalidRecommendationResult(
                    context, "verificationReady/readinessIssues must match the returned scene");
        }

        List<String> actualWarningCodes = new ArrayList<>();
        for (int index = 0; index < semanticWarnings.size(); index++) {
            ScenarioSemanticWarningDto warning = semanticWarnings.get(index);
            if (warning == null || isBlank(warning.getCode()) || isBlank(warning.getMessage())) {
                throw invalidRecommendationResult(
                        context, "semanticWarnings[" + index + "] requires non-blank code and message");
            }
            actualWarningCodes.add(warning.getCode());
        }
        List<String> expectedWarningCodes = expected.semanticWarnings().stream()
                .map(ScenarioVerificationReadiness.Issue::code)
                .toList();
        if (!actualWarningCodes.equals(expectedWarningCodes)) {
            throw invalidRecommendationResult(
                    context, "semanticWarnings must match the returned scene and filtered candidates");
        }
    }

    private ScenarioObjectiveTargets parseScenarioObjectiveTargets(
            ScenarioObjectiveTargetsDto targets,
            ScenarioRecommendationRequestDto request,
            String context) {
        if (targets.getMinDevices() == null
                || targets.getMinRules() == null
                || targets.getMinSpecs() == null) {
            throw invalidRecommendationResult(
                    context, "objectiveTargets must contain all minimum counts");
        }
        ScenarioObjectiveTargets parsed;
        try {
            parsed = new ScenarioObjectiveTargets(
                    targets.getMinDevices(), targets.getMinRules(), targets.getMinSpecs());
        } catch (IllegalArgumentException e) {
            throw invalidRecommendationResult(context, e.getMessage());
        }
        if (request.getMinDevices() == null
                || request.getMinRules() == null
                || request.getMinSpecs() == null
                || parsed.minDevices() != request.getMinDevices()
                || parsed.minRules() != request.getMinRules()
                || parsed.minSpecs() != request.getMinSpecs()) {
            throw invalidRecommendationResult(
                    context, "objectiveTargets must match the submitted minimum counts");
        }
        return parsed;
    }

    private RecommendationAudit parseRecommendationAudit(
            Map<String, Object> result,
            boolean requireAdjustments,
            String context) {
        String message = requireRecommendationText(result, "message", context);
        int count = requireRecommendationInteger(result, "count", context);
        int requestedCount = requireRecommendationInteger(result, "requestedCount", context);
        int validatedCount = requireRecommendationInteger(result, "validatedCount", context);
        int filteredCount = requireRecommendationInteger(result, "filteredCount", context);
        int rawCandidateCount = requireRecommendationInteger(result, "rawCandidateCount", context);
        int inspectedCount = requireRecommendationInteger(result, "inspectedCount", context);
        int truncatedCount = requireRecommendationInteger(result, "truncatedCount", context);
        List<RecommendationFilterItemDto> filteredItems = convertRecommendationItems(
                requireRecommendationList(result, "filteredItems", context),
                RecommendationFilterItemDto.class, context);
        validateRecommendationFilterItems(filteredItems, context);
        if (filteredCount != filteredItems.size()) {
            throw invalidRecommendationResult(context, "filteredCount must match filteredItems");
        }
        if (inspectedCount != validatedCount + filteredCount) {
            throw invalidRecommendationResult(
                    context, "inspectedCount must equal validatedCount plus filteredCount");
        }
        if (rawCandidateCount != inspectedCount + truncatedCount) {
            throw invalidRecommendationResult(
                    context, "rawCandidateCount must equal inspectedCount plus truncatedCount");
        }

        boolean hasAdjustedCount = result.containsKey("adjustedCount");
        boolean hasAdjustedItems = result.containsKey("adjustedItems");
        if (hasAdjustedCount != hasAdjustedItems || (requireAdjustments && !hasAdjustedCount)) {
            throw invalidRecommendationResult(
                    context, "adjustedCount and adjustedItems must be returned together");
        }
        if (!requireAdjustments && hasAdjustedCount) {
            throw invalidRecommendationResult(context, "unexpected adjustment fields");
        }

        Integer adjustedCount = null;
        List<RecommendationAdjustmentItemDto> adjustedItems = null;
        if (hasAdjustedCount) {
            adjustedCount = requireRecommendationInteger(result, "adjustedCount", context);
            adjustedItems = convertRecommendationItems(
                    requireRecommendationList(result, "adjustedItems", context),
                    RecommendationAdjustmentItemDto.class, context);
            validateRecommendationAdjustmentItems(adjustedItems, context);
            if (adjustedCount != adjustedItems.size()) {
                throw invalidRecommendationResult(context, "adjustedCount must match adjustedItems");
            }
        }

        return new RecommendationAudit(
                message, count, requestedCount, validatedCount, filteredCount, filteredItems,
                adjustedCount, adjustedItems, rawCandidateCount, inspectedCount, truncatedCount);
    }

    private void validateRecommendationFilterItems(
            List<RecommendationFilterItemDto> items, String context) {
        for (int index = 0; index < items.size(); index++) {
            RecommendationFilterItemDto item = items.get(index);
            if (item == null || isBlank(item.getType()) || item.getIndex() == null
                    || item.getIndex() < 1 || isBlank(item.getReasonCode())
                    || isBlank(item.getReason())) {
                throw invalidRecommendationResult(
                        context, "filteredItems[" + index + "] lacks type/index/reasonCode/reason");
            }
        }
    }

    private void validateRecommendationAdjustmentItems(
            List<RecommendationAdjustmentItemDto> items, String context) {
        for (int index = 0; index < items.size(); index++) {
            RecommendationAdjustmentItemDto item = items.get(index);
            if (item == null || isBlank(item.getType())
                    || (item.getIndex() != null && item.getIndex() < 1)
                    || isBlank(item.getReasonCode()) || isBlank(item.getReason())
                    || item.getAppliedValues() == null) {
                throw invalidRecommendationResult(
                        context, "adjustedItems[" + index + "] lacks required explanation data");
            }
        }
    }

    private List<?> requireRecommendationList(
            Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value instanceof List<?> list) {
            return list;
        }
        throw invalidRecommendationResult(context, field + " must be an array");
    }

    private void requireOnlyRecommendationFields(
            Map<String, Object> result, Set<String> allowedFields, String context) {
        for (String field : result.keySet()) {
            if (!allowedFields.contains(field)) {
                throw invalidRecommendationResult(context, "unknown field: " + field);
            }
        }
    }

    private int requireRecommendationInteger(
            Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value instanceof Number number) {
            double numeric = number.doubleValue();
            if (Double.isFinite(numeric) && numeric >= 0.0 && numeric == Math.rint(numeric)
                    && numeric <= Integer.MAX_VALUE) {
                return (int) numeric;
            }
        }
        throw invalidRecommendationResult(context, field + " must be a non-negative integer");
    }

    private boolean requireRecommendationBoolean(
            Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value instanceof Boolean bool) {
            return bool;
        }
        throw invalidRecommendationResult(context, field + " must be boolean");
    }

    private String requireRecommendationText(
            Map<String, Object> result, String field, String context) {
        String value = requireRecommendationString(result, field, context);
        if (value.isBlank()) {
            throw invalidRecommendationResult(context, field + " must be non-blank text");
        }
        return value;
    }

    private String requireRecommendationString(
            Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value instanceof String text) {
            return text;
        }
        throw invalidRecommendationResult(context, field + " must be text");
    }

    private <T> List<T> convertRecommendationItems(
            List<?> values, Class<T> type, String context) {
        return values.stream()
                .map(value -> convertRecommendationItem(value, type, context, type.getSimpleName()))
                .toList();
    }

    private <T> T convertRecommendationItem(
            Object value, Class<T> type, String context, String field) {
        if (value == null) {
            throw invalidRecommendationResult(context, field + " cannot be null");
        }
        try {
            return objectMapper.convertValue(value, type);
        } catch (IllegalArgumentException e) {
            throw new BadGatewayException(
                    context + " returned an invalid " + field + " object", e);
        }
    }

    private boolean isBlank(String value) {
        return value == null || value.isBlank();
    }

    private BadGatewayException invalidRecommendationResult(String context, String detail) {
        return new BadGatewayException(context + " returned an incomplete result: " + detail);
    }

    private record RecommendationAudit(
            String message,
            int count,
            int requestedCount,
            int validatedCount,
            int filteredCount,
            List<RecommendationFilterItemDto> filteredItems,
            Integer adjustedCount,
            List<RecommendationAdjustmentItemDto> adjustedItems,
            int rawCandidateCount,
            int inspectedCount,
            int truncatedCount) {
    }

    private Map<String, Object> toRuleCandidateToolPayload(RuleDto rule) {
        Map<String, Object> candidate = new LinkedHashMap<>();
        if (rule.getId() != null) {
            candidate.put("id", rule.getId());
        }

        List<Map<String, Object>> conditions = new ArrayList<>();
        for (RuleDto.Condition condition : rule.getConditions()) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("deviceName", condition.getDeviceName());
            row.put("attribute", condition.getAttribute());
            row.put("targetType", condition.getTargetType());
            if (condition.getRelation() != null) {
                row.put("relation", condition.getRelation());
            }
            if (condition.getValue() != null) {
                row.put("value", condition.getValue());
            }
            conditions.add(row);
        }
        candidate.put("conditions", conditions);

        RuleDto.Command command = rule.getCommand();
        Map<String, Object> commandPayload = new LinkedHashMap<>();
        commandPayload.put("deviceName", command.getDeviceName());
        commandPayload.put("action", command.getAction());
        if (command.getContentDevice() != null) {
            commandPayload.put("contentDevice", command.getContentDevice());
        }
        if (command.getContent() != null) {
            commandPayload.put("content", command.getContent());
        }
        candidate.put("command", commandPayload);
        if (rule.getRuleString() != null) {
            candidate.put("ruleString", rule.getRuleString());
        }
        return candidate;
    }

    private DuplicateRuleCheckResultDto parseDuplicateRuleCheckResult(Map<String, Object> result) {
        String reasonCode = requireText(result, "reasonCode", "Duplicate-rule check");
        if (!DUPLICATE_REASON_CODES.contains(reasonCode)) {
            throw new BadGatewayException("Duplicate-rule check returned an unknown reason code");
        }
        return DuplicateRuleCheckResultDto.builder()
                .isDuplicate(requireBoolean(result, "isDuplicate", "Duplicate-rule check"))
                .requiresReview(requireBoolean(result, "requiresReview", "Duplicate-rule check"))
                .matchedRule(optionalString(result, "matchedRule", "Duplicate-rule check"))
                .similarity(requireSimilarity(result, "Duplicate-rule check"))
                .matchType(requireText(result, "matchType", "Duplicate-rule check"))
                .reasonCode(reasonCode)
                .reason(requireText(result, "reason", "Duplicate-rule check"))
                .message(requireText(result, "message", "Duplicate-rule check"))
                .build();
    }

    private RuleSimilarityResultDto parseRuleSimilarityResult(Map<String, Object> result) {
        boolean isSimilar = requireBoolean(result, "isSimilar", "AI similarity check");
        boolean isDuplicate = requireBoolean(result, "isDuplicate", "AI similarity check");
        boolean requiresReview = requireBoolean(result, "requiresReview", "AI similarity check");
        double similarity = requireSimilarity(result, "AI similarity check");
        if (isDuplicate && !isSimilar) {
            throw new BadGatewayException(
                    "AI similarity check returned an inconsistent duplicate result");
        }
        if (requiresReview != (isDuplicate || isSimilar || similarity >= 0.8)) {
            throw new BadGatewayException(
                    "AI similarity check returned an inconsistent review decision");
        }
        String reasonCode = requireText(result, "reasonCode", "AI similarity check");
        if (!SIMILARITY_REASON_CODES.contains(reasonCode)) {
            throw new BadGatewayException("AI similarity check returned an unknown reason code");
        }
        String expectedReasonCode = isDuplicate
                ? "AI_DUPLICATE"
                : isSimilar
                ? "AI_SIMILAR"
                : similarity >= 0.8
                ? "AI_HIGH_SCORE_REVIEW"
                : "AI_NO_SIGNIFICANT_SIMILARITY";
        if (!expectedReasonCode.equals(reasonCode)
                && !("NO_EXISTING_RULES".equals(reasonCode)
                && !isSimilar && !isDuplicate && similarity == 0.0)) {
            throw new BadGatewayException(
                    "AI similarity check returned a reason code inconsistent with its result");
        }
        return RuleSimilarityResultDto.builder()
                .isSimilar(isSimilar)
                .isDuplicate(isDuplicate)
                .requiresReview(requiresReview)
                .matchedRule(optionalString(result, "matchedRule", "AI similarity check"))
                .similarity(similarity)
                .reasonCode(reasonCode)
                .reason(requireText(result, "reason", "AI similarity check"))
                .message(requireText(result, "message", "AI similarity check"))
                .build();
    }

    private boolean requireBoolean(Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value instanceof Boolean booleanValue) {
            return booleanValue;
        }
        throw invalidCheckResult(context, field + " must be boolean");
    }

    private double requireSimilarity(Map<String, Object> result, String context) {
        Object value = result.get("similarity");
        if (value instanceof Number number) {
            double similarity = number.doubleValue();
            if (Double.isFinite(similarity) && similarity >= 0.0 && similarity <= 1.0) {
                return similarity;
            }
        }
        throw invalidCheckResult(context, "similarity must be a number from 0 to 1");
    }

    private String requireText(Map<String, Object> result, String field, String context) {
        String value = optionalString(result, field, context);
        if (value != null && !value.isBlank()) {
            return value;
        }
        throw invalidCheckResult(context, field + " must be non-blank text");
    }

    private String optionalString(Map<String, Object> result, String field, String context) {
        Object value = result.get(field);
        if (value == null) {
            return null;
        }
        if (value instanceof String text) {
            return text;
        }
        throw invalidCheckResult(context, field + " must be text or null");
    }

    private BaseException invalidCheckResult(String context, String detail) {
        String message = context + " returned an incomplete result: " + detail;
        return context.startsWith("AI")
                ? new BadGatewayException(message)
                : new InternalServerException(message);
    }
}
