package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.model.ModelRequestParser;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.fix.FaultLocalizationResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunSummaryDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import com.fasterxml.jackson.databind.JsonNode;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * 验证控制器
 */
@Validated
@RestController
@RequestMapping("/api/verify")
@RequiredArgsConstructor
public class VerificationController {

    private final VerificationService verificationService;
    private final FixService fixService;
    private final ModelRequestParser modelRequestParser;

    /**
     * 同步验证（立即返回结果）
     */
    @PostMapping
    public Result<VerificationResultDto> verify(
            @CurrentUser Long userId,
            @RequestBody JsonNode body) {

        VerificationRequestDto request = modelRequestParser.parseVerification(body);
        VerificationResultDto result = verificationService.verify(userId, request);

        return Result.success(result);
    }

    /** Create an asynchronous run and return the authoritative task snapshot. */
    @PostMapping("/async")
    public Result<VerificationTaskDto> verifyAsync(
            @CurrentUser Long userId,
            @RequestBody JsonNode body) {

        VerificationRequestDto request = modelRequestParser.parseVerification(body);
        Long taskId = verificationService.submitVerification(userId, request);

        return Result.success(verificationService.getTask(userId, taskId));
    }

    /**
     * 获取当前用户的异步验证任务列表
     */
    @GetMapping("/tasks")
    public Result<List<VerificationTaskSummaryDto>> getTasks(
            @CurrentUser Long userId,
            @RequestParam(name = "excludeTaskIds", required = false) List<Long> excludeTaskIds) {
        return Result.success(verificationService.getTasks(userId, excludeTaskIds));
    }

    /**
     * 获取任务状态
     */
    @GetMapping("/tasks/{id}")
    public Result<VerificationTaskDto> getTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.getTask(userId, id));
    }

    @DeleteMapping("/tasks/{id}")
    public Result<Void> deleteTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        verificationService.deleteTask(userId, id);
        return Result.success();
    }

    /** List completed verification results. Completed runs are not task-inbox rows. */
    @GetMapping("/runs")
    public Result<List<VerificationRunSummaryDto>> getRuns(@CurrentUser Long userId) {
        return Result.success(verificationService.getRuns(userId));
    }

    @GetMapping("/runs/{id}")
    public Result<VerificationRunDto> getRun(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.getRun(userId, id));
    }

    @GetMapping("/runs/{id}/traces")
    public Result<List<TraceDto>> getRunTraces(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.getRunTraces(userId, id));
    }

    @DeleteMapping("/runs/{id}")
    public Result<Void> deleteRun(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        verificationService.deleteRun(userId, id);
        return Result.success();
    }

    /**
     * 获取用户的所有 Trace
     */
    @GetMapping("/traces")
    public Result<List<TraceDto>> getTraces(@CurrentUser Long userId) {
        return Result.success(verificationService.getUserTraces(userId));
    }

    /**
     * 获取某个验证任务产生的反例 Trace（按 task 维度过滤）
     */
    @GetMapping("/tasks/{id}/traces")
    public Result<List<TraceDto>> getTaskTraces(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.getTracesByTask(userId, id));
    }

    /**
     * 获取单个 Trace
     */
    @GetMapping("/traces/{id}")
    public Result<TraceDto> getTrace(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.getTrace(userId, id));
    }

    @DeleteMapping("/traces/{id}")
    public Result<Void> deleteTrace(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        verificationService.deleteTrace(userId, id);
        return Result.success();
    }

    @PostMapping("/tasks/{id}/cancel")
    public Result<TaskCancellationResultDto> cancelTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(verificationService.cancelTask(userId, id));
    }

    @GetMapping("/tasks/{id}/progress")
    public Result<Integer> getTaskProgress(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        int progress = verificationService.getTaskProgress(userId, id);
        return Result.success(progress);
    }

    /**
     * 故障定位：识别反例轨迹中被触发的规则
     */
    @GetMapping("/traces/{id}/fault-rules")
    public Result<FaultLocalizationResultDto> localizeFault(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(fixService.localizeFault(userId, id));
    }

    /**
     * 修复建议：定位故障规则并尝试修复策略
     */
    @PostMapping("/traces/{id}/fix")
    public Result<FixResultDto> fix(
            @CurrentUser Long userId,
            @PathVariable Long id,
            @Valid @RequestBody(required = false) FixRequestDto request) {
        List<String> strategies = (request != null) ? request.getStrategies() : null;
        var preferredRanges = (request != null) ? preferredRangesFromRequest(request) : null;
        return Result.success(fixService.fix(userId, id, strategies, preferredRanges));
    }

    /**
     * 应用修复建议：把用户所见的（已验证的）修复建议落库到其规则集。
     */
    @PostMapping("/traces/{id}/fix/apply")
    public Result<FixApplyResultDto> applyFix(
            @CurrentUser Long userId,
            @PathVariable Long id,
            @Valid @RequestBody FixApplyRequestDto request) {
        FixApplyResultDto result = fixService.applyFix(
                userId, id, request.getStrategy(),
                preferredRangesFromRequest(request));
        return Result.success(result);
    }

    private Map<String, PreferredRange> preferredRangesFromRequest(FixRequestDto request) {
        return preferredRangesFromSelections(request.getPreferredRangeSelections());
    }

    private Map<String, PreferredRange> preferredRangesFromRequest(FixApplyRequestDto request) {
        return preferredRangesFromSelections(request.getPreferredRangeSelections());
    }

    private Map<String, PreferredRange> preferredRangesFromSelections(List<PreferredRangeSelection> selections) {
        if (selections == null || selections.isEmpty()) {
            return null;
        }
        Map<String, PreferredRange> ranges = new LinkedHashMap<>();
        for (int i = 0; i < selections.size(); i++) {
            PreferredRangeSelection selection = selections.get(i);
            if (selection == null) {
                throw new BadRequestException("preferredRangeSelections[" + i + "] must not be null");
            }
            if (selection.getTargetId() == null || selection.getTargetId().isBlank()) {
                throw new BadRequestException("preferredRangeSelections[" + i
                        + "] must include targetId");
            }
            if (selection.getLower() == null || selection.getUpper() == null) {
                throw new BadRequestException("preferredRangeSelections[" + i
                        + "] must include lower and upper");
            }
            if (selection.getLower() > selection.getUpper()) {
                throw new BadRequestException("preferredRangeSelections[" + i
                        + "] lower(" + selection.getLower() + ") > upper(" + selection.getUpper() + ")");
            }
            String targetId = selection.getTargetId();
            if (!PreferredRangeSelection.isValidTargetId(targetId)) {
                throw new BadRequestException("preferredRangeSelections[" + i
                        + "] targetId is not a valid parameter-adjustment selector");
            }
            if (ranges.containsKey(targetId)) {
                throw new BadRequestException("Duplicate preferred range target in preferredRangeSelections[" + i
                        + "]");
            }
            ranges.put(targetId, selection.toPreferredRange());
        }
        return ranges;
    }
}
