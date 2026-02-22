package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SimulationOutput;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.*;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTraceMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import jakarta.annotation.PreDestroy;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * 模拟服务实现类
 *
 * 管理 NuSMV 随机模拟的执行与持久化
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class SimulationServiceImpl implements SimulationService {

    private final SmvGenerator smvGenerator;
    private final SmvTraceParser smvTraceParser;
    private final NusmvExecutor nusmvExecutor;
    private final NusmvConfig nusmvConfig;
    private final SimulationTraceRepository simulationTraceRepository;
    private final SimulationTraceMapper simulationTraceMapper;

    private static final int MAX_OUTPUT_LENGTH = 10000;
    private static final AtomicInteger THREAD_COUNTER = new AtomicInteger(1);

    private final ExecutorService simulationExecutor = Executors.newFixedThreadPool(
            4, r -> new Thread(r, "simulation-" + THREAD_COUNTER.getAndIncrement()));

    @PreDestroy
    void shutdown() {
        simulationExecutor.shutdownNow();
    }

    // ==================== 执行（不落库） ====================

    @Override
    public SimulationResultDto simulate(Long userId,
                                         List<DeviceVerificationDto> devices,
                                         List<RuleDto> rules,
                                         int steps,
                                         boolean isAttack,
                                         int intensity,
                                         boolean enablePrivacy) {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
        if (devices == null || devices.isEmpty()) {
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Error: devices list cannot be empty")).build();
        }

        log.info("Starting simulation: userId={}, devices={}, steps={}, attack={}, intensity={}",
                userId, devices.size(), steps, isAttack, intensity);

        long timeoutMs = nusmvConfig.getTimeoutMs() * 2;
        Future<SimulationResultDto> future = simulationExecutor.submit(() ->
                doSimulate(userId, devices, safeRules, steps, isAttack, intensity, enablePrivacy));

        try {
            return future.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            future.cancel(true);
            log.warn("Simulation timed out after {}ms", timeoutMs);
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Simulation timed out")).build();
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof InternalServerException ise) throw ise;
            log.error("Simulation failed", cause);
            throw new InternalServerException("Simulation failed: " + cause.getMessage());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps)
                    .logs(List.of("Simulation interrupted")).build();
        }
    }

    // ==================== 执行 + 持久化 ====================

    @Override
    @Transactional
    public SimulationTraceDto simulateAndSave(Long userId, SimulationRequestDto request) {
        SimulationResultDto result = simulate(userId,
                request.getDevices(), request.getRules(), request.getSteps(),
                request.isAttack(), request.getIntensity(), request.isEnablePrivacy());

        if (result.getStates() == null || result.getStates().isEmpty()) {
            throw new InternalServerException("Simulation produced no states, nothing to save");
        }

        SimulationTracePo po = SimulationTracePo.builder()
                .userId(userId)
                .requestedSteps(result.getRequestedSteps())
                .steps(result.getSteps())
                .statesJson(JsonUtils.toJson(result.getStates()))
                .logsJson(JsonUtils.toJsonOrEmpty(result.getLogs()))
                .nusmvOutput(result.getNusmvOutput())
                .requestJson(JsonUtils.toJson(request))
                .build();

        simulationTraceRepository.save(po);
        log.info("Saved simulation trace: id={}, userId={}, steps={}", po.getId(), userId, po.getSteps());

        return simulationTraceMapper.toDto(po);
    }

    // ==================== CRUD ====================

    @Override
    public List<SimulationTraceSummaryDto> getUserSimulations(Long userId) {
        return simulationTraceMapper.toSummaryDtoList(
                simulationTraceRepository.findByUserIdOrderByCreatedAtDesc(userId));
    }

    @Override
    public SimulationTraceDto getSimulation(Long userId, Long id) {
        return simulationTraceRepository.findByIdAndUserId(id, userId)
                .map(simulationTraceMapper::toDto)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTrace", id));
    }

    @Override
    @Transactional
    public void deleteSimulation(Long userId, Long id) {
        SimulationTracePo po = simulationTraceRepository.findByIdAndUserId(id, userId)
                .orElseThrow(() -> new ResourceNotFoundException("SimulationTrace", id));
        simulationTraceRepository.delete(po);
    }
    // ==================== 内部方法 ====================

    private SimulationResultDto doSimulate(Long userId,
                                            List<DeviceVerificationDto> devices,
                                            List<RuleDto> rules,
                                            int steps,
                                            boolean isAttack, int intensity,
                                            boolean enablePrivacy) {
        List<String> logs = new ArrayList<>();
        File smvFile = null;

        try {
            logs.add("Generating NuSMV model (simulation mode)...");
            SmvGenerator.GenerateResult genResult = smvGenerator.generate(
                    userId, devices, rules, List.of(), isAttack, intensity, enablePrivacy);
            smvFile = genResult.smvFile();
            Map<String, DeviceSmvData> deviceSmvMap = genResult.deviceSmvMap();

            if (smvFile == null || !smvFile.exists()) {
                logs.add("Failed to generate NuSMV model file");
                return SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
            }
            logs.add("Model generated: " + smvFile.getAbsolutePath());

            logs.add("Executing NuSMV interactive simulation (" + steps + " steps)...");
            SimulationOutput simOutput = nusmvExecutor.executeInteractiveSimulation(smvFile, steps);

            if (!simOutput.isSuccess()) {
                logs.add("Simulation failed: " + simOutput.getErrorMessage());
                return SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps).logs(logs)
                        .nusmvOutput(truncateOutput(simOutput.getErrorMessage())).build();
            }
            logs.add("Simulation completed.");

            List<TraceStateDto> states = smvTraceParser.parseCounterexampleStates(
                    simOutput.getTraceText(), deviceSmvMap);
            logs.add("Parsed " + states.size() + " states from simulation trace.");

            if (states.isEmpty()) {
                logs.add("No valid states parsed from simulation trace.");
                return SimulationResultDto.builder()
                        .states(List.of()).steps(0).requestedSteps(steps)
                        .nusmvOutput(truncateOutput(simOutput.getRawOutput()))
                        .logs(logs).build();
            }

            int actualSteps = Math.max(states.size() - 1, 0);

            return SimulationResultDto.builder()
                    .states(states)
                    .steps(actualSteps)
                    .requestedSteps(steps)
                    .nusmvOutput(truncateOutput(simOutput.getRawOutput()))
                    .logs(logs)
                    .build();

        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) Thread.currentThread().interrupt();
            log.error("Simulation error", e);
            logs.add("Error: " + e.getMessage());
            return SimulationResultDto.builder()
                    .states(List.of()).steps(0).requestedSteps(steps).logs(logs).build();
        } catch (Exception e) {
            log.error("Simulation failed", e);
            throw new InternalServerException("Simulation failed: " + e.getMessage());
        } finally {
            cleanupTempFile(smvFile);
        }
    }

    private void cleanupTempFile(File file) {
        if (file != null && file.exists()) {
            log.info("Keeping NuSMV model file for review: {}", file.getAbsolutePath());
        }
    }

    private String truncateOutput(String output) {
        if (output == null) return null;
        return output.length() > MAX_OUTPUT_LENGTH
                ? output.substring(0, MAX_OUTPUT_LENGTH) + "\n... (output truncated)" : output;
    }
}
