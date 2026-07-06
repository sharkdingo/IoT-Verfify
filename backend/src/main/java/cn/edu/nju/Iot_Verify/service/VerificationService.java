package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import java.util.List;

/**
 * 验证服务接口
 *
 * 提供 NuSMV 验证的同步和异步方法
 *
 * 注意：Trace 会自动保存（当检测到违规时），无需传入 saveTrace 参数
 */
public interface VerificationService {

    /**
     * 同步验证（立即返回结果）
     */
    VerificationResultDto verify(Long userId, VerificationRequestDto request);

    /**
     * 低层异步验证入口（兼容旧调用）：调用方必须先创建任务并传入非空 taskId。
     * 新调用应优先使用 submitVerification，让服务统一完成校验、建任务和入队。
     */
    void verifyAsync(Long userId, Long taskId, VerificationRequestDto request);

    /**
     * 校验请求、创建任务并提交异步验证。请求非法时不会创建任务；队列拒绝时会
     * 将已创建任务标记为失败并抛出 ServiceUnavailableException。
     *
     * @param userId 用户ID
     * @param request 验证请求
     * @return 任务ID
     */
    Long submitVerification(Long userId, VerificationRequestDto request);
    
    /**
     * 获取任务状态
     *
     * @param userId 用户ID
     * @param taskId 任务ID
     * @return 任务状态DTO
     */
    VerificationTaskDto getTask(Long userId, Long taskId);

    /**
     * 获取用户的验证任务收件箱（轻量列表，不含 NuSMV 输出和逐条规约详情）。
     *
     * @param userId 用户ID
     * @param excludedTaskIds 需要从列表中排除的任务ID（通常是前端正在专门轮询的任务）
     * @return 按创建时间倒序排列的任务摘要
     */
    List<VerificationTaskSummaryDto> getTasks(Long userId, List<Long> excludedTaskIds);
    
    /**
     * 获取用户的所有 Trace
     * 
     * @param userId 用户ID
     * @return Trace 列表
     */
    List<TraceDto> getUserTraces(Long userId);

    /**
     * 获取某个验证任务产生的反例 Trace（按 task 维度过滤，避免拿到旧任务/并发任务的反例）。
     *
     * @param userId 当前用户
     * @param taskId 验证任务 id
     * @return 该任务的 Trace 列表
     */
    List<TraceDto> getTracesByTask(Long userId, Long taskId);

    /**
     * 获取单个 Trace
     * 
     * @param userId 用户ID
     * @param traceId Trace ID
     * @return Trace
     */
    TraceDto getTrace(Long userId, Long traceId);
    
    /**
     * 删除 Trace
     *
     * @param userId 用户ID
     * @param traceId Trace ID
     */
    void deleteTrace(Long userId, Long traceId);

    /**
     * 取消验证任务
     *
     * @param userId 用户ID
     * @param taskId 任务ID
     * @return 是否成功取消
     */
    boolean cancelTask(Long userId, Long taskId);

    /**
     * 更新任务进度
     *
     * @param taskId 任务ID
     * @param progress 进度 (0-100)
     * @param message 进度消息
     */
    void updateTaskProgress(Long taskId, int progress, String message);

    /**
     * 获取任务进度
     *
     * @param userId 用户ID
     * @param taskId 任务ID
     * @return 进度 (0-100)
     */
    int getTaskProgress(Long userId, Long taskId);

    /**
     * 创建验证任务（异步验证前调用）
     *
     * @param userId 用户ID
     * @return 任务ID
     */
    Long createTask(Long userId);

    /**
     * 按任务ID标记失败（无需userId校验，仅供内部/Controller拒绝时使用）
     *
     * @param taskId 任务ID
     * @param errorMessage 错误信息
     */
    void failTaskById(Long taskId, String errorMessage);
}
