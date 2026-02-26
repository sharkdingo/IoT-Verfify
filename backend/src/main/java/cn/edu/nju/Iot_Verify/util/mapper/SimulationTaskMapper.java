package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import org.springframework.stereotype.Component;

@Component
public class SimulationTaskMapper {

    public SimulationTaskDto toDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        return SimulationTaskDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .simulationTraceId(po.getSimulationTraceId())
                .checkLogs(po.getCheckLogs())
                .errorMessage(po.getErrorMessage())
                .build();
    }
}

