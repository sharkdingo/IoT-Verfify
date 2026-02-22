package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SimulationOutput;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.util.mapper.SimulationTraceMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.File;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Tests for SimulationServiceImpl.
 */
@ExtendWith(MockitoExtension.class)
class SimulationServiceImplTest {

    @Mock private SmvGenerator smvGenerator;
    @Mock private SmvTraceParser smvTraceParser;
    @Mock private NusmvExecutor nusmvExecutor;
    @Mock private NusmvConfig nusmvConfig;
    @Mock private SimulationTraceRepository simulationTraceRepository;
    @Mock private SimulationTraceMapper simulationTraceMapper;

    private SimulationServiceImpl service;
    private Method doSimulate;

    @BeforeEach
    void setUp() throws Exception {
        service = new SimulationServiceImpl(
                smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig,
                simulationTraceRepository, simulationTraceMapper);

        doSimulate = SimulationServiceImpl.class.getDeclaredMethod(
                "doSimulate", Long.class, List.class, List.class,
                int.class, boolean.class, int.class, boolean.class);
        doSimulate.setAccessible(true);
    }

    private List<DeviceVerificationDto> singleDevice() {
        DeviceVerificationDto d = new DeviceVerificationDto();
        d.setVarName("testDevice");
        d.setTemplateName("light");
        return List.of(d);
    }

    // ==================== doSimulate tests ====================

    @Test
    void doSimulate_executorFails_returnsErrorResult() throws Exception {
        File fakeFile = File.createTempFile("test", ".smv");
        fakeFile.deleteOnExit();
        SmvGenerator.GenerateResult genResult = new SmvGenerator.GenerateResult(fakeFile, Map.of());
        when(smvGenerator.generate(any(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(genResult);
        when(nusmvExecutor.executeInteractiveSimulation(any(), anyInt()))
                .thenReturn(SimulationOutput.error("NuSMV exited with code 1."));

        SimulationResultDto result = (SimulationResultDto) doSimulate.invoke(
                service, 1L, singleDevice(), List.of(), 10, false, 3, false);

        assertTrue(result.getStates().isEmpty());
        assertEquals(0, result.getSteps());
        assertEquals(10, result.getRequestedSteps());
        assertTrue(result.getLogs().stream().anyMatch(l -> l.contains("failed")));
    }

    @Test
    void doSimulate_emptyStates_returnsZeroSteps() throws Exception {
        File fakeFile = File.createTempFile("test", ".smv");
        fakeFile.deleteOnExit();
        SmvGenerator.GenerateResult genResult = new SmvGenerator.GenerateResult(fakeFile, Map.of());
        when(smvGenerator.generate(any(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(genResult);
        when(nusmvExecutor.executeInteractiveSimulation(any(), anyInt()))
                .thenReturn(SimulationOutput.success("-> State: 1.1 <-\n", "raw"));
        when(smvTraceParser.parseCounterexampleStates(any(), any()))
                .thenReturn(List.of());

        SimulationResultDto result = (SimulationResultDto) doSimulate.invoke(
                service, 1L, singleDevice(), List.of(), 10, false, 3, false);

        assertTrue(result.getStates().isEmpty());
        assertEquals(0, result.getSteps());
        assertEquals(10, result.getRequestedSteps());
        assertTrue(result.getLogs().stream().anyMatch(l -> l.contains("No valid states")));
    }

    @Test
    void doSimulate_success_stepsEqualsStatesMinusOne() throws Exception {
        File fakeFile = File.createTempFile("test", ".smv");
        fakeFile.deleteOnExit();
        SmvGenerator.GenerateResult genResult = new SmvGenerator.GenerateResult(fakeFile, Map.of());
        when(smvGenerator.generate(any(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(genResult);
        when(nusmvExecutor.executeInteractiveSimulation(any(), anyInt()))
                .thenReturn(SimulationOutput.success("trace", "raw"));

        // 4 states = initial + 3 steps
        List<TraceStateDto> states = List.of(
                new TraceStateDto(), new TraceStateDto(),
                new TraceStateDto(), new TraceStateDto());
        when(smvTraceParser.parseCounterexampleStates(any(), any()))
                .thenReturn(states);

        SimulationResultDto result = (SimulationResultDto) doSimulate.invoke(
                service, 1L, singleDevice(), List.of(), 10, false, 3, false);

        assertEquals(4, result.getStates().size());
        assertEquals(3, result.getSteps());
        assertEquals(10, result.getRequestedSteps());
    }

    // ==================== simulate (public) tests ====================

    @Test
    void simulate_nullDevices_returnsError() {
        SimulationResultDto result = service.simulate(1L, null, List.of(), 10, false, 3, false);

        assertTrue(result.getStates().isEmpty());
        assertEquals(0, result.getSteps());
        assertTrue(result.getLogs().stream().anyMatch(l -> l.contains("empty")));
    }

    @Test
    void simulate_emptyDevices_returnsError() {
        SimulationResultDto result = service.simulate(1L, List.of(), List.of(), 10, false, 3, false);

        assertTrue(result.getStates().isEmpty());
        assertEquals(0, result.getSteps());
    }

    // ==================== simulateAndSave tests ====================

    @Test
    void simulateAndSave_success_savesPoAndReturnsDto() throws Exception {
        // Arrange: make simulate() produce a valid result via doSimulate
        when(nusmvConfig.getTimeoutMs()).thenReturn(1000L);
        File fakeFile = File.createTempFile("test", ".smv");
        fakeFile.deleteOnExit();
        SmvGenerator.GenerateResult genResult = new SmvGenerator.GenerateResult(fakeFile, Map.of());
        when(smvGenerator.generate(any(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(genResult);
        when(nusmvExecutor.executeInteractiveSimulation(any(), anyInt()))
                .thenReturn(SimulationOutput.success("trace", "raw"));
        List<TraceStateDto> states = List.of(new TraceStateDto(), new TraceStateDto());
        when(smvTraceParser.parseCounterexampleStates(any(), any()))
                .thenReturn(states);

        SimulationTraceDto expectedDto = SimulationTraceDto.builder()
                .id(1L).steps(1).requestedSteps(5).build();
        when(simulationTraceRepository.save(any())).thenAnswer(inv -> {
            SimulationTracePo po = inv.getArgument(0);
            po.setId(1L);
            return po;
        });
        when(simulationTraceMapper.toDto(any())).thenReturn(expectedDto);

        SimulationRequestDto request = new SimulationRequestDto();
        request.setDevices(singleDevice());
        request.setSteps(5);

        // Act
        SimulationTraceDto result = service.simulateAndSave(1L, request);

        // Assert
        assertEquals(expectedDto, result);
        ArgumentCaptor<SimulationTracePo> captor = ArgumentCaptor.forClass(SimulationTracePo.class);
        verify(simulationTraceRepository).save(captor.capture());
        SimulationTracePo savedPo = captor.getValue();
        assertEquals(1L, savedPo.getUserId());
        assertEquals(5, savedPo.getRequestedSteps());
        assertEquals(1, savedPo.getSteps());
    }

    @Test
    void simulateAndSave_emptyStates_throwsException() {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setDevices(null); // will trigger empty-devices path → empty states

        assertThrows(InternalServerException.class,
                () -> service.simulateAndSave(1L, request));
    }

    // ==================== CRUD tests ====================

    @Test
    void getUserSimulations_delegatesToMapperAndRepo() {
        SimulationTracePo po = SimulationTracePo.builder().id(1L).userId(1L).steps(3).build();
        when(simulationTraceRepository.findByUserIdOrderByCreatedAtDesc(1L))
                .thenReturn(List.of(po));
        SimulationTraceSummaryDto summary = SimulationTraceSummaryDto.builder().id(1L).steps(3).build();
        when(simulationTraceMapper.toSummaryDtoList(List.of(po)))
                .thenReturn(List.of(summary));

        List<SimulationTraceSummaryDto> result = service.getUserSimulations(1L);

        assertEquals(1, result.size());
        assertEquals(1L, result.get(0).getId());
    }

    @Test
    void getSimulation_found_returnsDto() {
        SimulationTracePo po = SimulationTracePo.builder().id(5L).userId(1L).build();
        SimulationTraceDto dto = SimulationTraceDto.builder().id(5L).build();
        when(simulationTraceRepository.findByIdAndUserId(5L, 1L))
                .thenReturn(Optional.of(po));
        when(simulationTraceMapper.toDto(po)).thenReturn(dto);

        SimulationTraceDto result = service.getSimulation(1L, 5L);

        assertEquals(5L, result.getId());
    }

    @Test
    void getSimulation_notFound_throwsResourceNotFound() {
        when(simulationTraceRepository.findByIdAndUserId(99L, 1L))
                .thenReturn(Optional.empty());

        assertThrows(ResourceNotFoundException.class,
                () -> service.getSimulation(1L, 99L));
    }

    @Test
    void deleteSimulation_found_deletes() {
        SimulationTracePo po = SimulationTracePo.builder().id(5L).userId(1L).build();
        when(simulationTraceRepository.findByIdAndUserId(5L, 1L))
                .thenReturn(Optional.of(po));

        service.deleteSimulation(1L, 5L);

        verify(simulationTraceRepository).delete(po);
    }

    @Test
    void deleteSimulation_notFound_throwsResourceNotFound() {
        when(simulationTraceRepository.findByIdAndUserId(99L, 1L))
                .thenReturn(Optional.empty());

        assertThrows(ResourceNotFoundException.class,
                () -> service.deleteSimulation(1L, 99L));
    }
}
