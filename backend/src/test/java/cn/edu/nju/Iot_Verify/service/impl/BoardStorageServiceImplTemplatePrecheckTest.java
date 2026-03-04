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
import cn.edu.nju.Iot_Verify.util.mapper.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.lang.NonNull;

import java.io.File;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new BoardStorageServiceImpl(
                nodeRepo,
                edgeRepo,
                specRepo,
                ruleRepo,
                layoutRepo,
                activeRepo,
                deviceTemplateRepo,
                deviceTemplateService,
                smvGenerator,
                specificationMapper,
                ruleMapper,
                deviceNodeMapper,
                deviceEdgeMapper
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

        assertEquals("101", result.getId());
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

        assertEquals("200", result.getId());
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
}
