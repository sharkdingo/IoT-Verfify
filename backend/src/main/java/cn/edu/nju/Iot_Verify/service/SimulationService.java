package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;

import java.util.List;

/**
 * 模拟服务接口
 */
public interface SimulationService {

    /**
     * 执行模拟（不落库）
     */
    SimulationResultDto simulate(Long userId,
                                  List<DeviceVerificationDto> devices,
                                  List<RuleDto> rules,
                                  int steps,
                                  boolean isAttack,
                                  int intensity,
                                  boolean enablePrivacy);

    Long createTask(Long userId, int requestedSteps);

    void failTaskById(Long taskId, String errorMessage);

    void simulateAsync(Long userId, Long taskId,
                       List<DeviceVerificationDto> devices,
                       List<RuleDto> rules,
                       int steps,
                       boolean isAttack,
                       int intensity,
                       boolean enablePrivacy);

    SimulationTaskDto getTask(Long userId, Long taskId);

    int getTaskProgress(Long userId, Long taskId);

    boolean cancelTask(Long userId, Long taskId);

    /**
     * 执行模拟并持久化
     */
    SimulationTraceDto simulateAndSave(Long userId, SimulationRequestDto request);

    /**
     * 获取用户的所有模拟记录
     */
    List<SimulationTraceSummaryDto> getUserSimulations(Long userId);

    /**
     * 获取单条模拟记录
     */
    SimulationTraceDto getSimulation(Long userId, Long id);

    /**
     * 删除单条模拟记录
     */
    void deleteSimulation(Long userId, Long id);
}
