package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
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
     *
     * @param userId 用户ID
     * @param devices 设备节点列表
     * @param rules 规则列表
     * @param specs 规格列表
     * @param isAttack 是否启用攻击模式
     * @param intensity 攻击强度 0-50
     * @return 验证结果
     */
    VerificationResultDto verify(Long userId, 
                                  List<DeviceNodeDto> devices,
                                  List<RuleDto> rules,
                                  List<SpecificationDto> specs,
                                  boolean isAttack,
                                  int intensity);
    
    /**
     * 异步验证（通过任务ID回调）
     *
     * @param userId 用户ID
     * @param taskId 任务ID（用于回调）
     * @param devices 设备节点列表
     * @param rules 规则列表
     * @param specs 规格列表
     * @param isAttack 是否启用攻击模式
     * @param intensity 攻击强度 0-50
     */
    void verifyAsync(Long userId, Long taskId,
                      List<DeviceNodeDto> devices,
                      List<RuleDto> rules,
                      List<SpecificationDto> specs,
                      boolean isAttack,
                      int intensity);
    
    /**
     * 获取任务状态
     *
     * @param userId 用户ID
     * @param taskId 任务ID
     * @return 任务状态DTO
     */
    VerificationTaskDto getTask(Long userId, Long taskId);
    
    /**
     * 获取用户的所有 Trace
     * 
     * @param userId 用户ID
     * @return Trace 列表
     */
    List<TraceDto> getUserTraces(Long userId);
    
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
}
