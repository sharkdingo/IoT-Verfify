package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * The affected state on one side of a reversible device edit.
 *
 * <p>Both sides name the same device ids. A side contains the devices, cascaded rules, and
 * specifications that must exist in that state, plus the complete Environment Pool. Using the
 * same shape for before and after makes create/delete undo and redo symmetric and gives drift
 * detection an authoritative expected state.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceJournalSnapshot {
    @Builder.Default
    private List<String> deviceIds = List.of();
    @Builder.Default
    private List<DeviceWithPosition> devices = List.of();
    @Builder.Default
    private List<RuleWithPosition> rules = List.of();
    @Builder.Default
    private List<SpecWithPosition> specs = List.of();
    @Builder.Default
    private List<BoardEnvironmentVariableDto> environmentVariables = List.of();

    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceWithPosition {
        private DeviceNodeDto device;
        private int position;
    }

    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class RuleWithPosition {
        private RuleDto rule;
        private int position;
    }

    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class SpecWithPosition {
        private SpecificationDto spec;
        private int position;
    }
}
