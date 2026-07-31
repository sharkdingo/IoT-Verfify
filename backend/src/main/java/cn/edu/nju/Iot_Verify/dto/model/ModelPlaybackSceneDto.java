package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.List;

/** Frozen visual scene used to replay one historical model run without touching the live board. */
public record ModelPlaybackSceneDto(List<DeviceNodeDto> nodes, List<RuleDto> rules) {

    public ModelPlaybackSceneDto {
        nodes = nodes == null ? List.of() : List.copyOf(nodes);
        rules = rules == null ? List.of() : List.copyOf(rules);
    }
}
