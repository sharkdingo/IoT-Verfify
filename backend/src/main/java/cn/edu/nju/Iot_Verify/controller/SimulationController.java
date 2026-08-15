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

    /**
     * Download the exact SMV model executed for this saved trajectory.
     *
     * <p>Mirrors {@code VerificationController#downloadTraceSmvModel}, including why an absent model
     * is {@code 404} rather than {@code 500}: a trajectory saved before the model was persisted has
     * none, and that is a fact about the record, not a fault in the server.
     */
    @GetMapping(value = "/traces/{id}/smv", produces = "text/plain;charset=UTF-8")
    public org.springframework.http.ResponseEntity<String> downloadSimulationTraceSmvModel(
            @CurrentUser Long userId,
            @PathVariable @Positive Long id) {
        SimulationTraceDto trace = simulationService.getSimulation(userId, id);

        if (!trace.hasSmvModel()) {
            throw new cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException(
                    "SMV model for simulation trace", id);
        }
        String smvModelContent = trace.getSmvModelContent();

        org.springframework.http.HttpHeaders headers = new org.springframework.http.HttpHeaders();
        headers.setContentType(org.springframework.http.MediaType.TEXT_PLAIN);
        // Pure-ASCII filename, so no charset overload; see VerificationController#smvAttachment for the
        // encoded-word this avoids.
        headers.setContentDisposition(
                org.springframework.http.ContentDisposition.attachment()
                        .filename("simulation-trace-" + id + ".smv")
                        .build());

        return org.springframework.http.ResponseEntity.ok().headers(headers).body(smvModelContent);
    }
}
