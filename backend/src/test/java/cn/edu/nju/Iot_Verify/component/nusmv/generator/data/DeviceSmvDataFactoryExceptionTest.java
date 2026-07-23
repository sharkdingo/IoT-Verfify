package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvModelValidator;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.verifyNoInteractions;

@ExtendWith(MockitoExtension.class)
class DeviceSmvDataFactoryExceptionTest {

    @Mock
    private DeviceTemplateService deviceTemplateService;

    private DeviceSmvDataFactory factory;

    @BeforeEach
    void setUp() {
        ObjectMapper objectMapper = new ObjectMapper();
        factory = new DeviceSmvDataFactory(objectMapper, deviceTemplateService, new SmvModelValidator(),
                new DeviceTemplateSchemaValidator(objectMapper));
    }

    @Test
    void buildDeviceSmvMap_invalidManifestJson_throwsManifestParseError() {
        DeviceVerificationDto device = buildDevice("dev_1", "DemoTpl");
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("DemoTpl")
                .manifestJson("{invalid-json")
                .build();
        when(deviceTemplateService.findTemplateByName(1L, "DemoTpl"))
                .thenReturn(Optional.of(templatePo));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertEquals("MANIFEST_PARSE_ERROR", ex.getErrorCategory());
        assertTrue(ex.getMessage().contains("DemoTpl"));
    }

    @Test
    void buildDeviceSmvMap_templateLookupFails_throwsTemplateLoadError() {
        DeviceVerificationDto device = buildDevice("dev_1", "DemoTpl");
        when(deviceTemplateService.findTemplateByName(1L, "DemoTpl"))
                .thenThrow(new RuntimeException("db unavailable"));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertEquals("TEMPLATE_LOAD_ERROR", ex.getErrorCategory());
        assertTrue(ex.getMessage().contains("DemoTpl"));
    }

    @Test
    void buildDeviceSmvMap_rejectsUnknownRawManifestFieldBeforeDtoConversion() {
        DeviceVerificationDto device = buildDevice("dev_1", "DemoTpl");
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("DemoTpl")
                .manifestJson("{\"Name\":\"DemoTpl\",\"FutureSecurityMeaning\":true}")
                .build();
        when(deviceTemplateService.findTemplateByName(1L, "DemoTpl"))
                .thenReturn(Optional.of(templatePo));

        BadRequestException exception = assertThrows(BadRequestException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertTrue(exception.getMessage().contains("FutureSecurityMeaning"));
        assertTrue(exception.getMessage().contains("backend/device-template-schema.json"));
    }

    @Test
    void buildDeviceSmvMap_rejectsMissingContentPrivacyInsteadOfDefaultingPublic() {
        DeviceVerificationDto device = buildDevice("camera_1", "Camera");
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("Camera")
                .manifestJson("{\"Name\":\"Camera\",\"Contents\":[{\"Name\":\"photo\"}]}")
                .build();
        when(deviceTemplateService.findTemplateByName(1L, "Camera"))
                .thenReturn(Optional.of(templatePo));

        BadRequestException exception = assertThrows(BadRequestException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertTrue(exception.getMessage().contains("Privacy"));
    }

    @Test
    void buildDeviceSmvMap_rejectsNonCanonicalVarNameAtGeneratorBoundary() throws Exception {
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Light")
                .internalVariables(List.of())
                .build();
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("Light")
                .manifestJson(new ObjectMapper().writeValueAsString(manifest))
                .build();
        DeviceVerificationDto device = buildDevice("1Lamp", "Light");
        when(deviceTemplateService.findTemplateByName(1L, "Light"))
                .thenReturn(Optional.of(templatePo));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertEquals("SMV_GENERATION_ERROR", ex.getErrorCategory());
        assertTrue(ex.getMessage().contains("normalizes to '_1lamp'"));
    }

    @Test
    void buildDeviceSmvMap_doesNotUseVariablesAsModeOverrides() throws Exception {
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Light")
                .modes(List.of("SwitchState"))
                .initState("off")
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("off").trust("trusted").privacy("public").build(),
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").privacy("public").build()))
                .internalVariables(List.of())
                .build();
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("Light")
                .manifestJson(new ObjectMapper().writeValueAsString(manifest))
                .build();
        DeviceVerificationDto device = buildDevice("lamp_1", "Light");
        device.setState("off");
        device.setVariables(List.of(new VariableStateDto("SwitchState", "on", "trusted")));
        when(deviceTemplateService.findTemplateByName(1L, "Light"))
                .thenReturn(Optional.of(templatePo));

        Map<String, DeviceSmvData> map = factory.buildDeviceSmvMap(1L, List.of(device));

        assertEquals("off", map.get("lamp_1").getCurrentModeStates().get("SwitchState"));
    }

    @Test
    void buildDeviceSmvMapFromTemplateSnapshots_neverReloadsMutableRepository() {
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Light")
                .internalVariables(List.of())
                .build();
        DeviceVerificationDto device = buildDevice("lamp_1", "Light");

        Map<String, DeviceSmvData> result = factory.buildDeviceSmvMapFromTemplateSnapshots(
                List.of(device), Map.of("Light", manifest));

        assertEquals(manifest, result.get("lamp_1").getManifest());
        verifyNoInteractions(deviceTemplateService);
    }

    @Test
    void buildDeviceSmvMap_capturesRepositoryTemplateProvenanceForDirectRequests() throws Exception {
        DeviceManifest manifest = DeviceManifest.builder().name("Light").internalVariables(List.of()).build();
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("Light")
                .defaultTemplate(true)
                .manifestJson(new ObjectMapper().writeValueAsString(manifest))
                .build();
        DeviceVerificationDto device = buildDevice("lamp_1", "Light");
        when(deviceTemplateService.findTemplateByName(1L, "Light"))
                .thenReturn(Optional.of(templatePo));

        DeviceSmvData resolved = factory.buildDeviceSmvMap(1L, List.of(device)).get("lamp_1");

        assertEquals(ModelTokenSource.BUNDLED, resolved.getModelTokenSource());
        assertEquals(ModelTokenSource.BUNDLED, device.getModelTokenSource());
    }

    @Test
    void buildDeviceSmvMapFromTemplateSnapshots_missingReferencedTemplateFailsWithoutFallback() {
        DeviceVerificationDto device = buildDevice("lamp_1", "Light");

        SmvGenerationException exception = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMapFromTemplateSnapshots(List.of(device), Map.of()));

        assertTrue(exception.getMessage().contains("Light"));
        verifyNoInteractions(deviceTemplateService);
    }

    private DeviceVerificationDto buildDevice(String varName, String templateName) {
        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName(varName);
        dto.setTemplateName(templateName);
        return dto;
    }
}
