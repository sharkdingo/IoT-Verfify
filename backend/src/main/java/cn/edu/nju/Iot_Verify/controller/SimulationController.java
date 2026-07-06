package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.List;

@Validated
@RestController
@RequestMapping("/api/simulate")
@RequiredArgsConstructor
public class SimulationController {

    private final SimulationService simulationService;

    @PostMapping
    public Result<SimulationResultDto> simulate(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        SimulationResultDto result = simulationService.simulate(userId, request);
        return Result.success(result);
    }

    @PostMapping("/async")
    public Result<Long> simulateAsync(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        Long taskId = simulationService.submitSimulation(userId, request);
        return Result.success(taskId);
    }

    @GetMapping("/tasks")
    public Result<List<SimulationTaskSummaryDto>> getTasks(
            @CurrentUser Long userId,
            @RequestParam(name = "excludeTaskIds", required = false) List<Long> excludeTaskIds) {
        return Result.success(simulationService.getTasks(userId, excludeTaskIds));
    }

    @GetMapping("/tasks/{id}")
    public Result<SimulationTaskDto> getTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTask(userId, id));
    }

    @GetMapping("/tasks/{id}/progress")
    public Result<Integer> getTaskProgress(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTaskProgress(userId, id));
    }

    @PostMapping("/tasks/{id}/cancel")
    public Result<Boolean> cancelTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.cancelTask(userId, id));
    }

    @PostMapping("/traces")
    public Result<SimulationTraceDto> simulateAndSave(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        return Result.success(simulationService.simulateAndSave(userId, request));
    }

    @GetMapping("/traces")
    public Result<List<SimulationTraceSummaryDto>> getSimulations(@CurrentUser Long userId) {
        return Result.success(simulationService.getUserSimulations(userId));
    }

    @GetMapping("/traces/{id}")
    public Result<SimulationTraceDto> getSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getSimulation(userId, id));
    }

    @DeleteMapping("/traces/{id}")
    public Result<Void> deleteSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        simulationService.deleteSimulation(userId, id);
        return Result.success();
    }
}
