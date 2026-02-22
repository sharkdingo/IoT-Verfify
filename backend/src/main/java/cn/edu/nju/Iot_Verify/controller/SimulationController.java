package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.web.bind.annotation.*;

import java.util.List;

/**
 * 模拟控制器
 */
@RestController
@RequestMapping("/api/verify")
@RequiredArgsConstructor
public class SimulationController {

    private final SimulationService simulationService;

    /**
     * 随机模拟 N 步（同步，不落库）
     */
    @PostMapping("/simulate")
    public Result<SimulationResultDto> simulate(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        SimulationResultDto result = simulationService.simulate(
                userId,
                request.getDevices(),
                request.getRules(),
                request.getSteps(),
                request.isAttack(),
                request.getIntensity(),
                request.isEnablePrivacy());
        return Result.success(result);
    }

    /**
     * 执行模拟并持久化
     */
    @PostMapping("/simulations")
    public Result<SimulationTraceDto> simulateAndSave(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        return Result.success(simulationService.simulateAndSave(userId, request));
    }

    /**
     * 获取当前用户模拟记录列表
     */
    @GetMapping("/simulations")
    public Result<List<SimulationTraceSummaryDto>> getSimulations(@CurrentUser Long userId) {
        return Result.success(simulationService.getUserSimulations(userId));
    }

    /**
     * 获取单条模拟记录
     */
    @GetMapping("/simulations/{id}")
    public Result<SimulationTraceDto> getSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getSimulation(userId, id));
    }

    /**
     * 删除单条模拟记录
     */
    @DeleteMapping("/simulations/{id}")
    public Result<Void> deleteSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        simulationService.deleteSimulation(userId, id);
        return Result.success();
    }
}
