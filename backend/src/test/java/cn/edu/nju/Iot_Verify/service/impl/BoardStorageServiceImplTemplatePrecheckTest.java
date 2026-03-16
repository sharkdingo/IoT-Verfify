package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.BoardActiveRepository;
import cn.edu.nju.Iot_Verify.repository.BoardLayoutRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceEdgeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.util.mapper.BoardActiveMapper;
import cn.edu.nju.Iot_Verify.util.mapper.BoardLayoutMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.lang.NonNull;
import org.springframework.transaction.support.TransactionTemplate;

import java.io.File;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyBoolean;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplTemplatePrecheckTest {

    @Mock
    private DeviceNodeRepository nodeRepo;
    @Mock
    private DeviceEdgeRepository edgeRepo;
    @Mock
    private SpecificationRepository specRepo;
    @Mock
    private RuleRepository ruleRepo;
    @Mock
    private BoardLayoutRepository layoutRepo;
    @Mock
    private BoardActiveRepository activeRepo;
    @Mock
    private DeviceTemplateRepository deviceTemplateRepo;
    @Mock
    private DeviceTemplateService deviceTemplateService;
    @Mock
    private SmvGenerator smvGenerator;
    @Mock
    private SpecificationMapper specificationMapper;
    @Mock
    private RuleMapper ruleMapper;
    @Mock
    private DeviceNodeMapper deviceNodeMapper;
    @Mock
    private DeviceEdgeMapper deviceEdgeMapper;
    @Mock
    private BoardLayoutMapper boardLayoutMapper;
    @Mock
    private BoardActiveMapper boardActiveMapper;
    @Mock
    private DeviceTemplateMapper deviceTemplateMapper;
    @Mock
    private TransactionTemplate transactionTemplate;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        // Use a real DeviceTemplateMapper so toDto() works in addDeviceTemplate tests
        deviceTemplateMapper = new DeviceTemplateMapper();
        service = new BoardStorageServiceImpl(
                nodeRepo,
                edgeRepo,
                specRepo,
                ruleRepo,
                layoutRepo,
                activeRepo,
                deviceTemplateRepo,
                deviceTemplateService,
                transactionTemplate,
                smvGenerator,
                specificationMapper,
                ruleMapper,
                deviceNodeMapper,
                deviceEdgeMapper,
                boardLayoutMapper,
                boardActiveMapper,
                deviceTemplateMapper
        );
    }

    @Test
    void addDeviceTemplate_whenMissingWorkingStates_shouldFailFastBeforePrecheck() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", false);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        verify(smvGenerator, never()).generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class));
        verify(deviceTemplateRepo, never()).saveAndFlush(anyTemplatePo());
    }

    @Test
    void addDeviceTemplate_whenNuSmvPrecheckFails_shouldReturnBadRequest() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", true);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Demo")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(100L);
            return po;
        });
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenThrow(SmvGenerationException.smvGenerationError("invalid transition"));

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        verify(smvGenerator).generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class));
    }

    @Test
    void addDeviceTemplate_whenNuSmvPrecheckInfraFails_shouldReturnInternalServerError() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", true);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Demo")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(102L);
            return po;
        });
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenThrow(new java.io.IOException("disk io failed"));

        InternalServerException ex = assertThrows(InternalServerException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(500, ex.getCode());
    }

    @Test
    void addDeviceTemplate_whenNuSmvTemplateLoadError_shouldReturnInternalServerError() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", true);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Demo")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(103L);
            return po;
        });
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenThrow(SmvGenerationException.templateLoadError("Demo", new RuntimeException("db down")));

        InternalServerException ex = assertThrows(InternalServerException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(500, ex.getCode());
    }

    @Test
    void addDeviceTemplate_whenNuSmvTemplateLookupMissing_shouldReturnInternalServerError() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", true);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Demo")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(104L);
            return po;
        });
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenThrow(SmvGenerationException.multipleDevicesFailed("__template_probe_device__(template=Demo)"));

        InternalServerException ex = assertThrows(InternalServerException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(500, ex.getCode());
    }

    @Test
    void addDeviceTemplate_whenNuSmvPrecheckSucceeds_shouldSaveAndReturnTemplate() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", true);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Demo")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(101L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        DeviceTemplateDto result = service.addDeviceTemplate(1L, dto);

        assertEquals(101L, result.getId());
        assertEquals("Demo", result.getName());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_noModeDevice_shouldPassValidationAndSave() throws Exception {
        DeviceTemplateDto dto = buildNoModeTemplate("WeatherSensor");

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "WeatherSensor")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(200L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        DeviceTemplateDto result = service.addDeviceTemplate(1L, dto);

        assertEquals(200L, result.getId());
        assertEquals("WeatherSensor", result.getName());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_partialModeFields_shouldReject() {
        // Has Modes and InitState but no WorkingStates — incomplete mode config
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of("SwitchState"));
        manifest.setInitState("Off");
        manifest.setWorkingStates(List.of());

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Partial");
        dto.setManifest(manifest);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        verify(deviceTemplateRepo, never()).saveAndFlush(anyTemplatePo());
    }

    @SuppressWarnings("all")
    @NonNull
    private DeviceTemplatePo anyTemplatePo() {
        return (DeviceTemplatePo) any(DeviceTemplatePo.class);
    }

    private DeviceTemplateDto buildTemplate(String name, boolean withWorkingStates) {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of("SwitchState"));
        manifest.setInitState("Off");
        if (withWorkingStates) {
            DeviceManifest.WorkingState off = new DeviceManifest.WorkingState();
            off.setName("Off");
            DeviceManifest.WorkingState on = new DeviceManifest.WorkingState();
            on.setName("On");
            manifest.setWorkingStates(List.of(off, on));
        }

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName(name);
        dto.setManifest(manifest);
        return dto;
    }

    private DeviceTemplateDto buildNoModeTemplate(String name) {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName(name);
        dto.setManifest(manifest);
        return dto;
    }

    // ======================== FIX-1: validateSmvIdentifier + checkVariableCollisions ========================

    @Test
    void addDeviceTemplate_internalVarWithInvalidChars_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "temp-value", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("invalid characters");
        verify(deviceTemplateRepo, never()).saveAndFlush(anyTemplatePo());
    }

    @Test
    void addDeviceTemplate_internalVarWithDigitPrefix_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "3temp", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("invalid characters");
    }

    @Test
    void addDeviceTemplate_internalVarWithReservedWord_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "MODULE", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("reserved word");
    }

    @Test
    void addDeviceTemplate_internalVarReservedWordCaseInsensitive_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "Define", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("reserved word");
    }

    @Test
    void addDeviceTemplate_impactedVarWithInvalidChars_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", null, "humidity!");

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("invalid characters");
    }

    @Test
    void addDeviceTemplate_impactedVarReservedWord_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", null, "NEXT");

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("reserved word");
    }

    @Test
    void addDeviceTemplate_internalVarCollidesWithMode_shouldReject() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of("Power"));
        manifest.setInitState("on");
        DeviceManifest.WorkingState on = new DeviceManifest.WorkingState();
        on.setName("on");
        DeviceManifest.WorkingState off = new DeviceManifest.WorkingState();
        off.setName("off");
        manifest.setWorkingStates(List.of(on, off));
        // InternalVariable name "power" collides with mode "Power" (case-insensitive)
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("power").isInside(true).lowerBound(0).upperBound(100).build()));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Collider");
        dto.setManifest(manifest);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("collides with mode name");
    }

    @Test
    void addDeviceTemplate_impactedVarCollidesWithInternalVar_shouldAllow() throws Exception {
        // CHANGED: InternalVariable and ImpactedVariable with same name is now ALLOWED
        // This is a common pattern (e.g., Thermostat, Water Heater, Window, Garage Door)
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "temperature", null);
        dto.getManifest().setImpactedVariables(List.of("Temperature"));

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "T1")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(300L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        // Should succeed now
        DeviceTemplateDto result = service.addDeviceTemplate(1L, dto);
        assertNotNull(result);
        assertEquals(300L, result.getId());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_noModeWithImpactedVarCollision_shouldAllow() throws Exception {
        // CHANGED: InternalVariable and ImpactedVariable with same name is now ALLOWED
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("humidity").isInside(false).lowerBound(0).upperBound(100).build()));
        manifest.setImpactedVariables(List.of("Humidity"));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Sensor");
        dto.setManifest(manifest);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "Sensor")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(301L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        // Should succeed now
        DeviceTemplateDto result = service.addDeviceTemplate(1L, dto);
        assertNotNull(result);
        assertEquals(301L, result.getId());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_blankInternalVarName_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "  ", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("must not be blank");
    }

    @Test
    void addDeviceTemplate_internalVarWithSpace_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "temp value", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("whitespace");
    }

    @Test
    void addDeviceTemplate_impactedVarWithSpace_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", null, "humidity bad");

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("whitespace");
    }

    /**
     * Helper: build a no-mode template with an optional InternalVariable and/or ImpactedVariable.
     */
    private DeviceTemplateDto buildTemplateWithVar(String name, String internalVarName, String impactedVarName) {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        if (internalVarName != null) {
            manifest.setInternalVariables(List.of(
                    DeviceManifest.InternalVariable.builder()
                            .name(internalVarName).isInside(true).lowerBound(0).upperBound(100).build()));
        }
        if (impactedVarName != null) {
            manifest.setImpactedVariables(List.of(impactedVarName));
        }
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName(name);
        dto.setManifest(manifest);
        return dto;
    }
}
