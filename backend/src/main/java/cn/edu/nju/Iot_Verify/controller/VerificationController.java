package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.List;

/**
 * 验证控制器
 */
@Slf4j
@Validated
@RestController
@RequestMapping("/api/verify")
@RequiredArgsConstructor
public class VerificationController {

    private final VerificationService verificationService;
    private final FixService fixService;

    /**
     * 同步验证（立即返回结果）
     */
    @PostMapping
    public Result<VerificationResultDto> verify(
            @CurrentUser Long userId,
            @Valid @RequestBody VerificationRequestDto request) {

        VerificationResultDto result = verificationService.verify(userId, request);

        return Result.success(result);
    }

    /**
     * 异步验证（后端创建任务，返回任务ID）
     */
    @PostMapping("/async")
    public Result<Long> verifyAsync(
            @CurrentUser Long userId,
            @Valid @RequestBody VerificationRequestDto request) {

        Long taskId = verificationService.createTask(userId);

        try {
            verificationService.verifyAsync(userId, taskId, request);
        } catch (TaskRejectedException e) {
            log.warn("Verification task {} rejected: thread pool full", taskId);
            verificationService.failTaskById(taskId, "Server busy, please try again later");
            throw new ServiceUnavailableException("Server busy, please try again later");
        }

        return Result.success(taskId);
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

    /**
     * 获取用户的所有 Trace
     */
    @GetMapping("/traces")
    public Result<List<TraceDto>> getTraces(@CurrentUser Long userId) {
        return Result.success(verificationService.getUserTraces(userId));
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
    public Result<Boolean> cancelTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        boolean cancelled = verificationService.cancelTask(userId, id);
        return Result.success(cancelled);
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
    public Result<List<FaultRuleDto>> localizeFault(
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
        var preferredRanges = (request != null) ? request.getPreferredRanges() : null;
        return Result.success(fixService.fix(userId, id, strategies, preferredRanges));
    }
}
