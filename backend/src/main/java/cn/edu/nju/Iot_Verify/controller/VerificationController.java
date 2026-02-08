package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.service.impl.VerificationServiceImpl;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.web.bind.annotation.*;

import java.util.List;

/**
 * 验证控制器
 */
@RestController
@RequestMapping("/api/verify")
@RequiredArgsConstructor
public class VerificationController {
    
    private final VerificationService verificationService;
    
    /**
     * 同步验证（立即返回结果）
     */
    @PostMapping
    public Result<VerificationResultDto> verify(
            @CurrentUser Long userId,
            @Valid @RequestBody VerificationRequestDto request) {
        
        VerificationResultDto result = verificationService.verify(
                userId,
                request.getDevices(),
                request.getRules(),
                request.getSpecs(),
                request.isAttack(),
                request.getIntensity()
        );
        
        return Result.success(result);
    }
    
    /**
     * 异步验证（通过任务ID回调）
     */
    @PostMapping("/async")
    public Result<Long> verifyAsync(
            @CurrentUser Long userId,
            @Valid @RequestBody VerificationRequestDto request,
            @RequestParam Long taskId) {
        
        verificationService.verifyAsync(
                userId,
                taskId,
                request.getDevices(),
                request.getRules(),
                request.getSpecs(),
                request.isAttack(),
                request.getIntensity()
        );
        
        return Result.success(taskId);
    }
    
    /**
     * 获取任务状态
     */
    @GetMapping("/tasks/{id}")
    public Result<VerificationTaskPo> getTask(
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
        int progress = ((VerificationServiceImpl) verificationService).getTaskProgress(id);
        return Result.success(progress);
    }
}
