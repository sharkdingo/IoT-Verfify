package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDomainPreviewDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDomainPreviewRequestDto;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import jakarta.validation.Validation;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class FuzzPaperDomainPreviewerTest {

    private final FuzzPaperDomainPreviewer previewer = new FuzzPaperDomainPreviewer();

    @Test
    void previewUsesExecutablePaperDomainWithoutMaterializingAnInitialState() {
        String fingerprint = "a".repeat(64);
        FuzzPaperDomainPreviewDto preview = previewer.preview(snapshot(), 4, fingerprint);

        assertEquals(4, preview.getPathLength());
        assertEquals(FuzzPaperSemantics.INITIALIZATION_POLICY,
                preview.getInitializationPolicy());
        assertEquals(fingerprint, preview.getModelFingerprint());
        assertEquals(FuzzPaperSemantics.limitationCodes(), preview.getPaperSemanticsCodes());
        assertEquals(8, preview.getPaperSemanticsCodes().size());

        assertEquals(1, preview.getDeviceDomains().size());
        assertEquals("switch_1", preview.getDeviceDomains().get(0).getTargetId());
        assertEquals("Hall switch", preview.getDeviceDomains().get(0).getLabel());
        assertEquals("state", preview.getDeviceDomains().get(0).getProperty());
        assertEquals(List.of("off", "on"),
                preview.getDeviceDomains().get(0).getLegalValues());

        assertEquals(2, preview.getLocalVariableDomains().size());
        var firmware = preview.getLocalVariableDomains().stream()
                .filter(domain -> "firmware".equals(domain.getProperty()))
                .findFirst().orElseThrow();
        assertEquals("switch_1", firmware.getTargetId());
        assertEquals("Hall switch", firmware.getLabel());
        assertEquals(List.of("stable", "beta"),
                firmware.getLegalValues());
        var battery = preview.getLocalVariableDomains().stream()
                .filter(domain -> "battery".equals(domain.getProperty()))
                .findFirst().orElseThrow();
        assertEquals(List.of(), battery.getLegalValues());
        assertEquals(0, battery.getLowerBound());
        assertEquals(2_000, battery.getUpperBound());

        assertEquals(2, preview.getEnvironmentDomains().size());
        var temperature = preview.getEnvironmentDomains().stream()
                .filter(domain -> "temperature".equals(domain.getName()))
                .findFirst().orElseThrow();
        assertEquals(FuzzPaperSemantics.CHANGE_RATE, temperature.getEventValueKind());
        assertEquals(List.of(), temperature.getInitialValues());
        assertEquals(List.of(), temperature.getEventValues());
        assertEquals(0, temperature.getInitialLowerBound());
        assertEquals(2, temperature.getInitialUpperBound());
        assertEquals(-1, temperature.getEventRateLowerBound());
        assertEquals(1, temperature.getEventRateUpperBound());

        var weather = preview.getEnvironmentDomains().stream()
                .filter(domain -> "weather".equals(domain.getName()))
                .findFirst().orElseThrow();
        assertEquals(FuzzPaperSemantics.DIRECT_VALUE_EXTENSION, weather.getEventValueKind());
        assertEquals(List.of("calm", "rain"), weather.getInitialValues());
        assertEquals(weather.getInitialValues(), weather.getEventValues());

        assertFalse(java.util.Arrays.stream(FuzzPaperDomainPreviewDto.class.getDeclaredFields())
                .anyMatch(field -> field.getName().toLowerCase().contains("nonce")
                        || field.getName().toLowerCase().contains("actualinitial")));
    }

    @Test
    void previewRequestUsesTheSamePathLengthBoundsAsExecution() {
        var validator = Validation.buildDefaultValidatorFactory().getValidator();
        FuzzPaperDomainPreviewRequestDto tooShort =
                FuzzPaperDomainPreviewRequestDto.builder().pathLength(0).build();
        FuzzPaperDomainPreviewRequestDto tooLong =
                FuzzPaperDomainPreviewRequestDto.builder().pathLength(51).build();

        assertEquals(1, validator.validate(tooShort).size());
        assertEquals(1, validator.validate(tooLong).size());
        assertEquals(20, new FuzzPaperDomainPreviewRequestDto().getPathLength());
    }

    private ModelInputSnapshot snapshot() {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("switch_1");
        device.setDeviceLabel("Hall switch");
        device.setTemplateName("Switch");
        device.setState("off");
        device.setVariables(List.of(
                new VariableStateDto("firmware", "stable", "trusted"),
                new VariableStateDto("battery", "1", "trusted")));
        device.setPrivacies(List.of());

        DeviceManifest.InternalVariable weather = DeviceManifest.InternalVariable.builder()
                .name("weather")
                .isInside(false)
                .values(List.of("calm", "rain"))
                .build();
        DeviceManifest.InternalVariable temperature = DeviceManifest.InternalVariable.builder()
                .name("temperature")
                .isInside(false)
                .lowerBound(0)
                .upperBound(2)
                .naturalChangeRate("[-1,1]")
                .build();
        DeviceManifest.InternalVariable firmware = DeviceManifest.InternalVariable.builder()
                .name("firmware")
                .isInside(true)
                .values(List.of("stable", "beta"))
                .build();
        DeviceManifest.InternalVariable battery = DeviceManifest.InternalVariable.builder()
                .name("battery")
                .isInside(true)
                .lowerBound(0)
                .upperBound(2_000)
                .build();
        DeviceManifest.WorkingState off = DeviceManifest.WorkingState.builder()
                .name("off")
                .dynamics(List.of())
                .build();
        DeviceManifest.WorkingState on = DeviceManifest.WorkingState.builder()
                .name("on")
                .dynamics(List.of())
                .build();
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Switch")
                .modes(List.of("PowerMode"))
                .internalVariables(List.of(weather, temperature, firmware, battery))
                .initState("off")
                .workingStates(List.of(off, on))
                .build();

        return new ModelInputSnapshot(
                List.of(),
                List.of(device),
                List.of(
                        new BoardEnvironmentVariableDto("weather", "calm", "trusted", "public"),
                        new BoardEnvironmentVariableDto("temperature", "1", "trusted", "public")),
                List.of(),
                List.of(),
                Map.of("Switch", manifest));
    }
}
