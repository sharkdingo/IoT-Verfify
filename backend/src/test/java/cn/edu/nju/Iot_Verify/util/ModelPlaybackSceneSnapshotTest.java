package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ModelPlaybackSceneSnapshotTest {

    @Test
    void canonicalize_emptySceneStillCopiesAndValidatesRules() {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("missing")
                        .attribute("state")
                        .targetType("state")
                        .build()))
                .command(RuleDto.Command.builder().deviceName("missing").action("on").build())
                .build();

        assertThrows(IllegalArgumentException.class,
                () -> ModelPlaybackSceneSnapshot.canonicalize(List.of(), List.of(), List.of(rule)));
    }

    @Test
    void canonicalize_rejectsNullNestedRuntimeValues() {
        DeviceNodeDto node = node("switch", "Switch");
        node.setVariables(Collections.<VariableStateDto>singletonList(null));
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("switch");
        device.setTemplateName("Switch");
        device.setDeviceLabel("Switch");

        assertThrows(IllegalArgumentException.class,
                () -> ModelPlaybackSceneSnapshot.canonicalize(List.of(node), List.of(device), List.of()));
    }

    @Test
    void canonicalize_copiesAndNormalizesPlaybackNodesWithoutMutatingTheRequest() {
        DeviceNodeDto node = node("Hall Light", " Hall light display ");
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("hall_light");
        device.setTemplateName("Switch");
        device.setDeviceLabel("Hall light display");

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("hall_light")
                        .attribute("state")
                        .targetType(" STATE ")
                        .relation("=")
                        .value("off")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("hall_light")
                        .action("on")
                        .build())
                .build();

        ModelPlaybackSceneDto scene = ModelPlaybackSceneSnapshot.canonicalize(
                List.of(node), List.of(device), List.of(rule));

        assertEquals("Hall Light", node.getId());
        assertEquals(" Hall light display ", node.getLabel());
        assertEquals("hall_light", scene.nodes().get(0).getId());
        assertEquals("Hall light display", scene.nodes().get(0).getLabel());
        assertEquals("state", scene.rules().get(0).getConditions().get(0).getTargetType());
        assertNotSame(node, scene.nodes().get(0));
        assertNotSame(node.getPosition(), scene.nodes().get(0).getPosition());
    }

    @Test
    void canonicalize_usesAnEmptyDisplayStateForAStatelessNode() {
        DeviceNodeDto node = node("button", "Button");
        node.setState(null);
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("button");
        device.setTemplateName("Switch");
        device.setDeviceLabel("Button");

        ModelPlaybackSceneDto scene = ModelPlaybackSceneSnapshot.canonicalize(
                List.of(node), List.of(device), List.of());

        assertEquals("", scene.nodes().get(0).getState());
    }

    private DeviceNodeDto node(String id, String label) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setTemplateName("Switch");
        node.setLabel(label);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(10.0);
        position.setY(20.0);
        node.setPosition(position);
        node.setState("off");
        node.setWidth(160);
        node.setHeight(120);
        return node;
    }
}
