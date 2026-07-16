package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;

import java.util.List;

public record FuzzFinding(
        SpecificationDto specification,
        int firstViolationStep,
        List<TraceStateDto> states,
        List<FuzzInputEvent> inputEvents) {

    public FuzzFinding {
        states = states == null ? List.of() : List.copyOf(states);
        inputEvents = inputEvents == null ? List.of() : List.copyOf(inputEvents);
    }
}
