package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RecommendationCapabilityViewTest {

    @Test
    void fromManifestKeepsBehaviorRelevantFields() {
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Sensor")
                .description("A test sensor")
                .modes(List.of("Mode"))
                .initState("idle")
                .impactedVariables(List.of("temperature"))
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("reading")
                        .description("Measured value")
                        .isInside(false)
                        .falsifiableWhenCompromised(true)
                        .trust("untrusted")
                        .privacy("public")
                        .lowerBound(0)
                        .upperBound(100)
                        .naturalChangeRate("[-1, 1]")
                        .build()))
                .workingStates(List.of(DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                        .name("idle")
                        .description("Waiting")
                        .trust("trusted")
                        .privacy("public")
                        .dynamics(List.of(DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                                .variableName("reading")
                                .changeRate("1")
                                .build()))
                        .build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("send")
                        .signal(true)
                        .acceptsContent(true)
                        .startState("idle")
                        .endState("idle")
                        .build()))
                .contents(List.of(DeviceTemplateDto.DeviceManifest.Content.builder()
                        .name("measurement")
                        .description("Measured data")
                        .privacy("private")
                        .build()))
                .build();

        Map<String, Object> view = RecommendationCapabilityView.fromManifest(manifest);

        assertEquals("Sensor", view.get("manifestName"));
        assertEquals(List.of("temperature"), view.get("impactedVariables"));
        Map<?, ?> variable = (Map<?, ?>) ((List<?>) view.get("variables")).get(0);
        assertEquals(true, variable.get("falsifiableWhenCompromised"));
        assertEquals("[-1, 1]", variable.get("naturalChangeRate"));
        Map<?, ?> dynamic = (Map<?, ?>) ((List<?>) ((Map<?, ?>) ((List<?>) view.get("workingStates")).get(0))
                .get("dynamics")).get(0);
        assertEquals("reading", dynamic.get("variableName"));
        Map<?, ?> api = (Map<?, ?>) ((List<?>) view.get("apis")).get(0);
        assertEquals(true, api.get("acceptsContent"));
        assertEquals("derived", api.get("descriptionSource"));
        assertTrue(String.valueOf(api.get("description")).contains("start state idle"));
        Map<?, ?> content = (Map<?, ?>) ((List<?>) view.get("contents")).get(0);
        assertEquals("Measured data", content.get("description"));
        assertEquals("declared", content.get("descriptionSource"));
        assertTrue(view.containsKey("transitions"));
    }

    @Test
    void fromManifestExposesValuesForEveryModeInMultiModeStates() {
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Washer")
                .modes(List.of("WashMode", "MachineState"))
                .workingStates(List.of(
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                                .name("regular;idle")
                                .trust("trusted")
                                .privacy("public")
                                .build(),
                        DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                                .name("heavy;run")
                                .trust("trusted")
                                .privacy("public")
                                .build()))
                .build();

        Map<String, Object> view = RecommendationCapabilityView.fromManifest(manifest);
        Map<?, ?> modeValues = (Map<?, ?>) view.get("modeValues");

        assertEquals(List.of("regular", "heavy"), modeValues.get("WashMode"));
        assertEquals(List.of("idle", "run"), modeValues.get("MachineState"));
        assertEquals("derived", view.get("descriptionSource"));
        assertTrue(String.valueOf(view.get("description")).contains("Stateful device template"));
    }
}
