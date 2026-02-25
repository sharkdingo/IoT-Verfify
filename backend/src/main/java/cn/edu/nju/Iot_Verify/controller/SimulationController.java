package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.*;

import java.util.List;

@Slf4j
@RestController
@RequestMapping("/api/verify")
@RequiredArgsConstructor
public class SimulationController {

    private final SimulationService simulationService;

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

    @PostMapping("/simulate/async")
    public ResponseEntity<Result<Long>> simulateAsync(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        Long taskId = simulationService.createTask(userId, request.getSteps());

        try {
            simulationService.simulateAsync(
                    userId,
                    taskId,
                    request.getDevices(),
                    request.getRules(),
                    request.getSteps(),
                    request.isAttack(),
                    request.getIntensity(),
                    request.isEnablePrivacy());
        } catch (TaskRejectedException e) {
            log.warn("Simulation task {} rejected: thread pool full", taskId);
            simulationService.failTaskById(taskId, "Server busy, please try again later");
            return ResponseEntity.status(HttpStatus.SERVICE_UNAVAILABLE)
                    .body(Result.error(503, "Server busy, please try again later"));
        }

        return ResponseEntity.ok(Result.success(taskId));
    }

    @GetMapping("/simulations/tasks/{id}")
    public Result<SimulationTaskDto> getTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTask(userId, id));
    }

    @GetMapping("/simulations/tasks/{id}/progress")
    public Result<Integer> getTaskProgress(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTaskProgress(userId, id));
    }

    @PostMapping("/simulations/tasks/{id}/cancel")
    public Result<Boolean> cancelTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.cancelTask(userId, id));
    }

    @PostMapping("/simulations")
    public Result<SimulationTraceDto> simulateAndSave(
            @CurrentUser Long userId,
            @Valid @RequestBody SimulationRequestDto request) {
        return Result.success(simulationService.simulateAndSave(userId, request));
    }

    @GetMapping("/simulations")
    public Result<List<SimulationTraceSummaryDto>> getSimulations(@CurrentUser Long userId) {
        return Result.success(simulationService.getUserSimulations(userId));
    }

    @GetMapping("/simulations/{id}")
    public Result<SimulationTraceDto> getSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getSimulation(userId, id));
    }

    @DeleteMapping("/simulations/{id}")
    public Result<Void> deleteSimulation(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        simulationService.deleteSimulation(userId, id);
        return Result.success();
    }
}
