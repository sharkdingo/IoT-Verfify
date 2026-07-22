package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.model.ModelRequestParser;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import com.fasterxml.jackson.databind.JsonNode;
import lombok.RequiredArgsConstructor;
import jakarta.validation.constraints.Positive;
import jakarta.validation.constraints.Size;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.List;

@Validated
@RestController
@RequestMapping("/api/simulate")
@RequiredArgsConstructor
public class SimulationController {

    private final SimulationService simulationService;
    private final ModelRequestParser modelRequestParser;

    @PostMapping
    public Result<SimulationResultDto> simulate(
            @CurrentUser Long userId,
            @RequestBody JsonNode body) {
        SimulationRequestDto request = modelRequestParser.parseSimulation(body);
        return Result.success(simulationService.simulate(userId, request));
    }

    @PostMapping("/async")
    public Result<SimulationTaskDto> simulateAsync(
            @CurrentUser Long userId,
            @RequestBody JsonNode body) {
        SimulationRequestDto request = modelRequestParser.parseSimulation(body);
        Long taskId = simulationService.submitSimulation(userId, request);
        return Result.success(simulationService.getTask(userId, taskId));
    }

    @GetMapping("/tasks")
    public Result<List<SimulationTaskSummaryDto>> getTasks(
            @CurrentUser Long userId,
            @RequestParam(name = "excludeTaskIds", required = false)
            @Size(max = RequestLimits.MAX_TASK_EXCLUSIONS, message = "At most 100 task IDs can be excluded")
            List<@Positive(message = "Excluded task IDs must be positive") Long> excludeTaskIds) {
        return Result.success(simulationService.getTasks(userId, excludeTaskIds));
    }

    @GetMapping("/tasks/{id}")
    public Result<SimulationTaskDto> getTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTask(userId, id));
    }

    @DeleteMapping("/tasks/{id}")
    public Result<Void> deleteTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        simulationService.deleteTask(userId, id);
        return Result.success();
    }

    @GetMapping("/tasks/{id}/progress")
    public Result<Integer> getTaskProgress(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.getTaskProgress(userId, id));
    }

    @PostMapping("/tasks/{id}/cancel")
    public Result<TaskCancellationResultDto> cancelTask(
            @CurrentUser Long userId,
            @PathVariable Long id) {
        return Result.success(simulationService.cancelTask(userId, id));
    }

    @PostMapping("/traces")
    public Result<SimulationTraceDto> simulateAndSave(
            @CurrentUser Long userId,
            @RequestBody JsonNode body) {
        SimulationRequestDto request = modelRequestParser.parseSimulation(body);
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
