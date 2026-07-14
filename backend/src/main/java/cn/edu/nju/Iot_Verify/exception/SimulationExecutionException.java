package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import lombok.Getter;

import java.util.List;

/** A synchronous simulation attempt that produced no usable model trace. */
@Getter
public class SimulationExecutionException extends BaseException {

    private final String reasonCode;
    private final List<String> logs;

    private SimulationExecutionException(int status, String reasonCode, String message, List<String> logs) {
        super(status, message);
        this.reasonCode = reasonCode;
        this.logs = logs != null ? List.copyOf(logs) : List.of();
    }

    public static SimulationExecutionException timedOut() {
        return new SimulationExecutionException(
                504, "TIMED_OUT", "Simulation timed out before a model trace was produced.", List.of());
    }

    public static SimulationExecutionException interrupted() {
        return new SimulationExecutionException(
                503, "INTERRUPTED", "Simulation was interrupted before a model trace was produced.", List.of());
    }

    public static SimulationExecutionException fromResult(SimulationResultDto result) {
        List<String> logs = result != null && result.getLogs() != null ? result.getLogs() : List.of();
        String lastLog = logs.isEmpty() ? "No usable model trace was produced." : logs.get(logs.size() - 1);
        String reasonCode = lastLog != null && lastLog.contains("No valid states")
                ? "NO_TRACE_STATES"
                : "EXECUTION_FAILED";
        String detail = lastLog == null || lastLog.isBlank()
                ? "No usable model trace was produced."
                : lastLog;
        return new SimulationExecutionException(
                500, reasonCode, "Simulation did not produce a model trace: " + detail, logs);
    }
}
