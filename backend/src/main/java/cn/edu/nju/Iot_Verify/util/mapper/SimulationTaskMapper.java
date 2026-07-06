package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

import java.util.List;

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
                .checkLogs(po.getCheckLogs() != null ? po.getCheckLogs() : JsonUtils.fromJsonToStringList(po.getCheckLogsJson()))
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .build();
    }

    public SimulationTaskSummaryDto toSummaryDto(SimulationTaskPo po) {
        if (po == null) {
            return null;
        }
        return SimulationTaskSummaryDto.builder()
                .id(po.getId())
                .status(po.getStatus() != null ? po.getStatus().name() : null)
                .createdAt(po.getCreatedAt())
                .startedAt(po.getStartedAt())
                .completedAt(po.getCompletedAt())
                .processingTimeMs(po.getProcessingTimeMs())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .simulationTraceId(po.getSimulationTraceId())
                .errorMessage(po.getErrorMessage())
                .progress(po.getProgress())
                .build();
    }

    public List<SimulationTaskSummaryDto> toSummaryDtoList(List<SimulationTaskPo> poList) {
        if (poList == null) {
            return List.of();
        }
        return poList.stream()
                .map(this::toSummaryDto)
                .toList();
    }
}

