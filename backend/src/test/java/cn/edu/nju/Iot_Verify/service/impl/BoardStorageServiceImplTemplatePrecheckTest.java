package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetChangeDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.exception.TemplateDeletionConflictException;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.BoardLayoutRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateNuSmvValidator;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.board.BoardEditHistoryState;
import cn.edu.nju.Iot_Verify.service.board.BoardEditJournal;
import cn.edu.nju.Iot_Verify.service.board.BoardUndoAvailability;
import cn.edu.nju.Iot_Verify.util.mapper.BoardLayoutMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.lang.NonNull;
import org.springframework.transaction.support.TransactionCallback;
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
import static org.mockito.Mockito.lenient;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplTemplatePrecheckTest {

    @Mock
    private DeviceNodeRepository nodeRepo;
    @Mock
    private SpecificationRepository specRepo;
    @Mock
    private RuleRepository ruleRepo;
    @Mock
    private BoardLayoutRepository layoutRepo;
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
    private BoardLayoutMapper boardLayoutMapper;
    @Mock
    private DeviceTemplateMapper deviceTemplateMapper;
    @Mock
    private DeviceTemplateSchemaValidator deviceTemplateSchemaValidator;
    @Mock
    private TransactionTemplate transactionTemplate;
    @Mock
    private UserRepository userRepository;
    @Mock
    private BoardEditJournal editJournal;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        // Use a real DeviceTemplateMapper so toDto() works in addDeviceTemplate tests
        deviceTemplateMapper = new DeviceTemplateMapper();
        deviceNodeMapper = new DeviceNodeMapper();
        // The NuSMV template validation moved to its own component; use a real one over the
        // mocked generator so these tests still exercise validation through the service API.
        DeviceTemplateNuSmvValidator templateNuSmvValidator =
                new DeviceTemplateNuSmvValidator(smvGenerator);
        service = new BoardStorageServiceImpl(
                nodeRepo,
                null,
                specRepo,
                ruleRepo,
                layoutRepo,
                deviceTemplateRepo,
                deviceTemplateService,
                transactionTemplate,
                templateNuSmvValidator,
                specificationMapper,
                ruleMapper,
                deviceNodeMapper,
                boardLayoutMapper,
                deviceTemplateMapper,
                deviceTemplateSchemaValidator,
                userRepository,
                editJournal
        );
        lenient().when(userRepository.findByIdForUpdate(anyLong())).thenReturn(java.util.Optional.of(new UserPo()));
        lenient().when(userRepository.findById(anyLong())).thenReturn(java.util.Optional.of(new UserPo()));
        lenient().when(deviceTemplateSchemaValidator.toCanonicalJson(any(DeviceManifest.class)))
                .thenAnswer(inv -> JsonUtils.toJson(inv.getArgument(0)));
        lenient().when(transactionTemplate.execute(any())).thenAnswer(inv ->
                ((TransactionCallback<?>) inv.getArgument(0)).doInTransaction(null));
        lenient().when(editJournal.historyState(anyLong()))
                .thenReturn(historyState(0, "0"));
    }

    @Test
    void getDeviceTemplates_whenEmpty_isSideEffectFree() {
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of());

        List<DeviceTemplateDto> result = service.getDeviceTemplates(1L);

        assertEquals(List.of(), result);
        verify(deviceTemplateService, never()).initDefaultTemplates(1L);
    }

    @Test
    void previewDefaultTemplateReset_returnsExactImpactWithoutWriting() {
        DeviceTemplatePo bundled = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[],"ImpactedVariables":[],
                 "Transitions":[],"APIs":[],"Contents":[]}
                """);
        bundled.setId(null);
        bundled.setDefaultTemplate(true);
        DeviceTemplatePo current = templatePo("Sensor", bundled.getManifestJson());
        current.setDefaultTemplate(true);

        when(deviceTemplateService.getDefaultTemplateDefinitions(1L)).thenReturn(List.of(bundled));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(current));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        DefaultTemplateResetResultDto preview = service.previewDefaultTemplateReset(1L);

        assertEquals("preview", preview.getOperation());
        assertFalse(preview.getImpactToken().isBlank());
        assertEquals(true, preview.isCanApply());
        assertEquals(DefaultTemplateResetChangeDto.ChangeType.REFRESH_DEFAULT,
                preview.getTemplateChanges().get(0).getChangeType());
        assertFalse(preview.getTemplateChanges().get(0).isSemanticsChanged());
        assertEquals(0, preview.getEditHistoryEntryCount());
        verify(deviceTemplateRepo, never()).deleteDefaultsForReset(anyLong(), anyList());
        verify(deviceTemplateRepo, never()).saveAllAndFlush(anyList());
    }

    @Test
    void resetDefaultTemplates_rejectsWhenOnlyUndoHistoryChanged() {
        DeviceTemplatePo bundled = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[],"ImpactedVariables":[],
                 "Transitions":[],"APIs":[],"Contents":[]}
                """);
        bundled.setId(null);
        bundled.setDefaultTemplate(true);
        DeviceTemplatePo current = templatePo("Sensor", bundled.getManifestJson());
        current.setDefaultTemplate(true);
        when(deviceTemplateService.getDefaultTemplateDefinitions(1L)).thenReturn(List.of(bundled));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(current));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());
        when(editJournal.historyState(1L))
                .thenReturn(historyState(1, "a"), historyState(2, "b"));

        DefaultTemplateResetResultDto preview = service.previewDefaultTemplateReset(1L);
        ConflictException error = assertThrows(ConflictException.class,
                () -> service.resetDefaultTemplates(1L, preview.getImpactToken()));

        assertEquals(1, preview.getEditHistoryEntryCount());
        org.assertj.core.api.Assertions.assertThat(error.getMessage()).contains("undo history changed");
        verify(deviceTemplateRepo, never()).deleteDefaultsForReset(anyLong(), anyList());
        verify(editJournal, never()).clear(anyLong());
    }

    @Test
    void resetDefaultTemplates_clearsThePreviewedUndoHistoryAfterCommit() {
        DeviceTemplatePo bundled = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[],"ImpactedVariables":[],
                 "Transitions":[],"APIs":[],"Contents":[]}
                """);
        bundled.setId(null);
        bundled.setDefaultTemplate(true);
        DeviceTemplatePo current = templatePo("Sensor", bundled.getManifestJson());
        current.setDefaultTemplate(true);
        when(deviceTemplateService.getDefaultTemplateDefinitions(1L)).thenReturn(List.of(bundled));
        when(deviceTemplateRepo.findByUserId(1L))
                .thenReturn(List.of(current), List.of(current), List.of(bundled));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());
        when(deviceTemplateRepo.deleteDefaultsForReset(anyLong(), anyList())).thenReturn(1);
        when(deviceTemplateRepo.saveAllAndFlush(anyList())).thenAnswer(invocation -> invocation.getArgument(0));
        when(editJournal.historyState(1L)).thenReturn(historyState(3, "c"));

        DefaultTemplateResetResultDto preview = service.previewDefaultTemplateReset(1L);
        DefaultTemplateResetResultDto result = service.resetDefaultTemplates(1L, preview.getImpactToken());

        assertEquals("reset", result.getOperation());
        assertEquals(3, result.getEditHistoryEntryCount());
        verify(editJournal).clear(1L);
    }

    @Test
    void previewDefaultTemplateReset_marksBundledEnvironmentAdditionsForSafeLocalization() {
        String manifestJson = """
                {"Name":"Weather Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[{"Name":"weather","IsInside":false,"Reads":true,
                 "Values":["sunny","rainy"],"Trust":"trusted","Privacy":"public"}],
                 "ImpactedVariables":[],"Transitions":[],"APIs":[],"Contents":[]}
                """;
        DeviceTemplatePo bundled = templatePo("Weather Sensor", manifestJson);
        bundled.setId(null);
        bundled.setDefaultTemplate(true);
        DeviceTemplatePo current = templatePo("Weather Sensor", manifestJson);
        current.setDefaultTemplate(true);
        DeviceNodeDto node = buildNode("weather_1", "Weather Sensor");
        node.setState("Working");

        when(deviceTemplateService.getDefaultTemplateDefinitions(1L)).thenReturn(List.of(bundled));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(current));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(deviceNodeMapper.toEntity(node, 1L)));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        DefaultTemplateResetResultDto preview = service.previewDefaultTemplateReset(1L);

        assertEquals(1, preview.getEnvironmentChanges().size());
        assertEquals("weather", preview.getEnvironmentChanges().get(0).getName());
        assertEquals(ModelTokenSource.UNKNOWN,
                preview.getEnvironmentChanges().get(0).getPreviousModelTokenSource());
        assertEquals(ModelTokenSource.BUNDLED,
                preview.getEnvironmentChanges().get(0).getCurrentModelTokenSource());
    }

    @Test
    void environmentModelTokenSources_requiresEveryProviderToBeBundled() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setInternalVariables(List.of(DeviceManifest.InternalVariable.builder()
                .name("weather")
                .isInside(false).reads(true)
                .values(List.of("sunny", "rainy"))
                .build()));

        DeviceTemplateDto bundled = new DeviceTemplateDto();
        bundled.setName("Bundled Weather");
        bundled.setManifest(manifest);
        bundled.setDefaultTemplate(true);
        DeviceTemplateDto custom = new DeviceTemplateDto();
        custom.setName("Custom Weather");
        custom.setManifest(manifest);
        custom.setDefaultTemplate(false);

        DeviceNodeDto bundledNode = buildNode("bundled_1", bundled.getName());
        DeviceNodeDto customNode = buildNode("custom_1", custom.getName());

        assertEquals(ModelTokenSource.BUNDLED,
                service.environmentModelTokenSources(
                        List.of(bundledNode), List.of(bundled, custom)).get("weather"));
        assertEquals(ModelTokenSource.CUSTOM,
                service.environmentModelTokenSources(
                        List.of(bundledNode, customNode), List.of(bundled, custom)).get("weather"));
    }

    @Test
    void previewDefaultTemplateReset_reportsObsoleteTypeAsBlockingUsedDevice() {
        DeviceTemplatePo bundled = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[],"ImpactedVariables":[],
                 "Transitions":[],"APIs":[],"Contents":[]}
                """);
        bundled.setId(null);
        bundled.setDefaultTemplate(true);
        DeviceTemplatePo obsolete = templatePo("Legacy Sensor", """
                {"Name":"Legacy Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[],"ImpactedVariables":[],
                 "Transitions":[],"APIs":[],"Contents":[]}
                """);
        obsolete.setDefaultTemplate(true);
        DeviceNodeDto node = buildNode("legacy_1", "Legacy Sensor");
        node.setState(null);

        when(deviceTemplateService.getDefaultTemplateDefinitions(1L)).thenReturn(List.of(bundled));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(obsolete));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(deviceNodeMapper.toEntity(node, 1L)));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        DefaultTemplateResetResultDto preview = service.previewDefaultTemplateReset(1L);

        assertFalse(preview.isCanApply());
        assertEquals("legacy_1", preview.getAffectedDevices().get(0).getDeviceLabel());
        org.assertj.core.api.Assertions.assertThat(preview.getBlockers())
                .anySatisfy(blocker -> {
                    org.assertj.core.api.Assertions.assertThat(blocker.getItemLabel()).contains("legacy_1");
                    org.assertj.core.api.Assertions.assertThat(blocker.getReasonCode())
                            .isEqualTo("DEVICE_INSTANCE_INCOMPATIBLE");
                    org.assertj.core.api.Assertions.assertThat(blocker.getReason()).contains("Unknown device template");
                });
    }

    @Test
    void saveNodes_whenTemplateMissing_shouldRejectBeforeReplacingNodes() {
        DeviceNodeDto node = buildNode("lamp1", "Missing Template");

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        assertEquals(422, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].templateName", "Unknown device template: Missing Template");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenTemplateNameStartsWithVariablePrefix_shouldTreatAsNormalDevice() {
        DeviceTemplatePo template = templatePo("variable_power", """
                {"Name":"variable_power","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[{"Name":"reading","LowerBound":0,"UpperBound":100,"IsInside":true}]}
                """);
        DeviceNodeDto node = buildNode("lamp1_power", "variable_power");
        node.setState(null);

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(nodeRepo.saveAll(anyList())).thenAnswer(inv -> inv.getArgument(0));

        List<DeviceNodeDto> saved = service.saveNodes(1L, List.of(node));

        assertEquals(1, saved.size());
        assertEquals("variable_power", saved.get(0).getTemplateName());
    }

    @Test
    void saveNodes_whenTemplateNameCaseDiffers_shouldPersistCanonicalTemplateName() {
        DeviceTemplatePo template = templatePo("Window Shade", """
                {"Name":"Window Shade","Modes":["ShadeMode"],"InitState":"open",
                 "WorkingStates":[{"Name":"open"},{"Name":"closed"}],"InternalVariables":[]}
                """);
        DeviceNodeDto node = buildNode("shade1", "window shade");
        node.setState("open");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(nodeRepo.saveAll(anyList())).thenAnswer(inv -> inv.getArgument(0));

        List<DeviceNodeDto> saved = service.saveNodes(1L, List.of(node));

        assertEquals(1, saved.size());
        assertEquals("Window Shade", saved.get(0).getTemplateName());
    }

    @Test
    void saveNodes_whenRuntimeStateIsIllegal_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Light", "{\"Name\":\"Light\",\"Modes\":[\"SwitchState\"],\"InitState\":\"Off\",\"WorkingStates\":[{\"Name\":\"Off\"},{\"Name\":\"On\"}],\"InternalVariables\":[]}");
        DeviceNodeDto node = buildNode("lamp1", "Light");
        node.setState("broken");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].state", "Illegal state value for device template: broken");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenModeDeviceStateIsBlank_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Light", "{\"Name\":\"Light\",\"Modes\":[\"SwitchState\"],\"InitState\":\"Off\",\"WorkingStates\":[{\"Name\":\"Off\"},{\"Name\":\"On\"}],\"InternalVariables\":[]}");
        DeviceNodeDto node = buildNode("lamp1", "Light");
        node.setState("");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].state", "State is required for device templates with modes");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenRuntimeVariableIsIllegal_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Thermostat", """
                {"Name":"Thermostat","Modes":["ThermostatMode"],"InitState":"auto",
                 "WorkingStates":[{"Name":"auto"},{"Name":"cool"}],
                 "InternalVariables":[{"Name":"temperature","IsInside":true,"LowerBound":0,"UpperBound":50}]}
                """);
        DeviceNodeDto node = buildNode("thermostat1", "Thermostat");
        node.setState("auto");
        node.setVariables(List.of(new VariableStateDto("temperature", "80", "trusted")));

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].variables[0].value",
                        "Variable value out of range for 'temperature': 80 (allowed 0..50)");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenRuntimeVariableNamesMode_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Light", """
                {"Name":"Light","Modes":["SwitchState"],"InitState":"Off",
                 "WorkingStates":[{"Name":"Off"},{"Name":"On"}],
                 "InternalVariables":[]}
                """);
        DeviceNodeDto node = buildNode("lamp1", "Light");
        node.setState("Off");
        node.setVariables(List.of(new VariableStateDto("SwitchState", "On", "trusted")));

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].variables[0].name",
                        "Unknown runtime variable for device template: SwitchState");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenRuntimePrivacyIsIllegal_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                "InternalVariables":[{"Name":"motion","Values":["active","inactive"],"Privacy":"public"}]}
                """);
        DeviceNodeDto node = buildNode("sensor1", "Sensor");
        node.setState("Working");
        node.setPrivacies(List.of(new PrivacyStateDto("missing", "secret")));

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].privacies[0].privacy", "Value must be public or private: secret")
                .containsEntry("nodes[0].privacies[0].name", "Unknown device-local variable privacy target: missing");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenNoModeDeviceHasStateTrust_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[{"Name":"motion","Values":["active","inactive"],"Privacy":"public"}]}
                """);
        DeviceNodeDto node = buildNode("sensor1", "Sensor");
        node.setState("Working");
        node.setCurrentStateTrust("trusted");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].currentStateTrust",
                        "currentStateTrust is only valid for device templates with modes");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenNoModeDeviceHasNonPlaceholderState_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Sensor", """
                {"Name":"Sensor","Modes":[],"InitState":"","WorkingStates":[],
                 "InternalVariables":[{"Name":"motion","Values":["active","inactive"],"Privacy":"public"}]}
                """);
        DeviceNodeDto node = buildNode("sensor1", "Sensor");
        node.setState("off");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(node)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[0].state",
                        "No-mode device state must be omitted or the UI placeholder 'Working'");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveNodes_whenIdsCollideAfterNuSmvNormalization_shouldRejectBeforeReplacingNodes() {
        DeviceTemplatePo template = templatePo("Light", "{\"Name\":\"Light\",\"Modes\":[\"SwitchState\"],\"InitState\":\"Off\",\"WorkingStates\":[{\"Name\":\"Off\"},{\"Name\":\"On\"}],\"InternalVariables\":[]}");
        DeviceNodeDto first = buildNode("AC 1", "Light");
        first.setState("Off");
        DeviceNodeDto second = buildNode("ac_1", "Light");
        second.setState("Off");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException ex = assertThrows(ValidationException.class, () ->
                service.saveNodes(1L, List.of(first, second)));

        org.assertj.core.api.Assertions.assertThat(ex.getErrors())
                .containsEntry("nodes[1].id", "Device ID collides after NuSMV normalization: ac_1 -> ac_1");
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void deleteDeviceTemplate_whenTemplateIsUsedByCanvasDevice_shouldReject() {
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .id(10L)
                .userId(1L)
                .name("Light")
                .manifestJson("{\"Name\":\"Light\"}")
                .defaultTemplate(false)
                .build();
        DeviceNodePo node = DeviceNodePo.builder()
                .id("living_light")
                .userId(1L)
                .templateName("Light")
                .label("living_light")
                .posX(0.0)
                .posY(0.0)
                .state("off")
                .width(110)
                .height(90)
                .build();

        when(deviceTemplateRepo.findByIdAndUserId(10L, 1L)).thenReturn(java.util.Optional.of(template));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(node));

        var preview = service.previewDeviceTemplateDeletion(1L, 10L);
        TemplateDeletionConflictException ex = assertThrows(TemplateDeletionConflictException.class, () ->
                service.deleteDeviceTemplate(1L, 10L, preview.getImpactToken()));

        assertEquals(409, ex.getCode());
        assertEquals("TEMPLATE_DELETION_BLOCKED", ex.getReasonCode());
        assertFalse(ex.getCurrentPreview().isCanDelete());
        assertEquals("living_light", ex.getCurrentPreview().getBlockers().get(0).getItemId());
        verify(deviceTemplateRepo, never()).delete(any());
    }

    @Test
    void deleteDeviceTemplate_clearsThePreviewedUndoHistoryAfterCommit() {
        DeviceTemplatePo template = templatePo("Light", "{\"Name\":\"Light\"}");
        template.setId(10L);
        template.setDefaultTemplate(false);
        when(deviceTemplateRepo.findByIdAndUserId(10L, 1L)).thenReturn(java.util.Optional.of(template));
        when(deviceTemplateRepo.findByUserId(1L))
                .thenReturn(List.of(template), List.of(template), List.of());
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(editJournal.historyState(1L)).thenReturn(historyState(4, "d"));

        var preview = service.previewDeviceTemplateDeletion(1L, 10L);
        var result = service.deleteDeviceTemplate(1L, 10L, preview.getImpactToken());

        assertEquals("deleted", result.getOperation());
        assertEquals(4, result.getEditHistoryEntryCount());
        verify(deviceTemplateRepo).delete(template);
        verify(editJournal).clear(1L);
    }

    @Test
    void deleteDeviceTemplate_rejectsWhenOnlyUndoHistoryChanged() {
        DeviceTemplatePo template = templatePo("Light", "{\"Name\":\"Light\"}");
        template.setId(10L);
        template.setDefaultTemplate(false);
        when(deviceTemplateRepo.findByIdAndUserId(10L, 1L)).thenReturn(java.util.Optional.of(template));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(editJournal.historyState(1L))
                .thenReturn(historyState(1, "a"), historyState(2, "b"));

        var preview = service.previewDeviceTemplateDeletion(1L, 10L);
        TemplateDeletionConflictException error = assertThrows(
                TemplateDeletionConflictException.class,
                () -> service.deleteDeviceTemplate(1L, 10L, preview.getImpactToken()));

        assertEquals("TEMPLATE_DELETION_PREVIEW_STALE", error.getReasonCode());
        assertEquals(2, error.getCurrentPreview().getEditHistoryEntryCount());
        verify(deviceTemplateRepo, never()).delete(any());
        verify(editJournal, never()).clear(anyLong());
    }

    @Test
    void templateDeletionDoesNotRevealWhetherAnotherUsersTemplateExists() {
        when(deviceTemplateRepo.findByIdAndUserId(10L, 1L)).thenReturn(java.util.Optional.empty());

        ResourceNotFoundException previewError = assertThrows(ResourceNotFoundException.class,
                () -> service.previewDeviceTemplateDeletion(1L, 10L));
        ResourceNotFoundException deleteError = assertThrows(ResourceNotFoundException.class,
                () -> service.deleteDeviceTemplate(1L, 10L, "confirmed-impact-token"));

        assertEquals(404, previewError.getCode());
        assertEquals(previewError.getMessage(), deleteError.getMessage());
        verify(deviceTemplateRepo, times(2)).findByIdAndUserId(10L, 1L);
        verify(deviceTemplateRepo, never()).findById(anyLong());
        verify(deviceTemplateRepo, never()).delete(any());
    }

    @Test
    void addDeviceTemplate_whenMissingWorkingStates_shouldFailFastBeforePrecheck() throws Exception {
        DeviceTemplateDto dto = buildTemplate("Demo", false);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        verify(smvGenerator, never()).generate(
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenThrow(SmvGenerationException.smvGenerationError("invalid transition"));

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        verify(smvGenerator).generate(
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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

    private DeviceNodeDto buildNode(String id, String templateName) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setTemplateName(templateName);
        node.setLabel(id);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(0.0);
        position.setY(0.0);
        node.setPosition(position);
        node.setState("off");
        node.setWidth(176);
        node.setHeight(128);
        return node;
    }

    private DeviceTemplatePo templatePo(String name, String manifestJson) {
        return DeviceTemplatePo.builder()
                .id(500L)
                .userId(1L)
                .name(name)
                .manifestJson(manifestJson)
                .defaultTemplate(false)
                .build();
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

    /*
     * Modes are compared on the token generation emits, not on the name the user typed.
     *
     * `sanitizeSmvToken` rescues a NuSMV reserved word by prefixing `_`, so mode `next` becomes `_next`. The
     * collision check used to compare raw names, which made `next` and `_next` look distinct — and the generated
     * model then declared the same enum constant twice. Verified against NuSMV 2.7.1: "TYPE ERROR: duplicate
     * constants in the enum type of variable", i.e. the user's verification failed with an engine type error
     * instead of a message naming the template field to rename.
     *
     * Modes and working states are the only identifier kinds that skip the reserved-word rejection variables get,
     * precisely because generation rescues them; that makes comparing pre-rescue names the bug.
     */
    @Test
    void addDeviceTemplate_modesCollidingAfterReservedWordRescue_shouldReject() {
        DeviceTemplateDto dto = buildTemplate("T1", true);
        dto.getManifest().setModes(List.of("next", "_next"));

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("collides with another mode")
                .contains("_next");
    }

    /*
     * The same fix closes a second collision the raw comparison missed, and this one is worse.
     *
     * A mode named `next` is rescued to `_next`; an InternalVariable literally named `_next` is legal and needs no
     * rescue. Raw comparison saw `next` vs `_next` and passed them. The generated model then declares `_next`
     * both as an enum constant of the mode variable and as a variable name — and NuSMV 2.7.1 does not report a
     * type error for that, it **terminates by a signal** with "Aborting batch mode" and no diagnosable message,
     * where the control model differing only in the constant name verifies normally. That is the worst possible
     * failure shape for a verification product: no verdict and nothing to act on.
     */
    @Test
    void addDeviceTemplate_modeCollidingWithInternalVariableAfterRescue_shouldReject() {
        // A complete manifest, so validation reaches the collision check rather than stopping on a missing
        // InitState — my first version of this test used a fixture without one and asserted on the wrong message.
        DeviceTemplateDto dto = buildTemplate("T1", true);
        dto.getManifest().setModes(List.of("next"));
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("_next");
        iv.setIsInside(true);
        iv.setValues(List.of("a", "b"));
        iv.setTrust("trusted");
        iv.setPrivacy("public");
        iv.setFalsifiableWhenCompromised(false);
        dto.getManifest().setInternalVariables(List.of(iv));

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage()).contains("collides with mode name");
    }

    @Test
    void addDeviceTemplate_modesDistinctAfterNormalization_shouldBeAccepted() {
        // The boundary: a single reserved-word mode is legal, because generation renames it unambiguously.
        DeviceTemplateDto dto = buildTemplate("T1", true);
        dto.getManifest().setModes(List.of("next"));

        org.assertj.core.api.Assertions.assertThatCode(() -> service.addDeviceTemplate(1L, dto))
                .doesNotThrowAnyException();
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
    void addDeviceTemplate_impactedVarCollidesWithLocalInternalVar_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("T1", "temperature", null);
        dto.getManifest().setImpactedVariables(List.of("Temperature"));

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        assertEquals(400, ex.getCode());
        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("cannot share a name with a local InternalVariable");
    }

    @Test
    void addDeviceTemplate_impactedVarCollidesWithEnvironmentInternalVar_shouldAllow() throws Exception {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(false).reads(true).trust("untrusted").privacy("public")
                        .lowerBound(0).upperBound(100).naturalChangeRate("0").build()));
        manifest.setImpactedVariables(List.of("temperature"));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("ThermostatLike");
        dto.setManifest(manifest);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "ThermostatLike")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(300L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        DeviceTemplateDto result = service.addDeviceTemplate(1L, dto);
        assertNotNull(result);
        assertEquals(300L, result.getId());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_noModeWithImpactedVarCollision_shouldAllow() throws Exception {
        // Environment InternalVariable + ImpactedVariable with the same name is allowed.
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("humidity").isInside(false).reads(true).trust("untrusted").privacy("public")
                        .lowerBound(0).upperBound(100).naturalChangeRate("0").build()));
        manifest.setImpactedVariables(List.of("humidity"));

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
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
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

    @Test
    void addDeviceTemplate_generatedTrustIdentifierCollision_shouldReject() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(true).lowerBound(0).upperBound(100).build(),
                DeviceManifest.InternalVariable.builder()
                        .name("trust_temperature").isInside(true).lowerBound(0).upperBound(100).build()));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("TrustCollision");
        dto.setManifest(manifest);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("generated NuSMV identifier 'trust_temperature'")
                .contains("collides");
    }

    @Test
    void addDeviceTemplate_generatedRateIdentifierCollision_shouldReject() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(false).reads(true).trust("untrusted").privacy("public")
                        .lowerBound(0).upperBound(100).naturalChangeRate("0").build(),
                DeviceManifest.InternalVariable.builder()
                        .name("temperature_rate").isInside(true).lowerBound(-10).upperBound(10).build()));
        manifest.setImpactedVariables(List.of("temperature"));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("RateCollision");
        dto.setManifest(manifest);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("generated NuSMV identifier 'temperature_rate'")
                .contains("collides");
    }

    @Test
    void addDeviceTemplate_generatedApiSignalIdentifierCollision_shouldReject() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of("Power"));
        manifest.setInitState("off");
        manifest.setWorkingStates(List.of(
                DeviceManifest.WorkingState.builder().name("off").build(),
                DeviceManifest.WorkingState.builder().name("on").build()));
        manifest.setInternalVariables(List.of(
                DeviceManifest.InternalVariable.builder()
                        .name("press_a").isInside(true).lowerBound(0).upperBound(1).build()));
        manifest.setApis(List.of(DeviceManifest.API.builder()
                .name("press")
                .signal(true)
                .startState("off")
                .endState("on")
                .build()));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("ApiSignalCollision");
        dto.setManifest(manifest);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("generated NuSMV identifier 'press_a'")
                .contains("collides");
    }

    @Test
    void addDeviceTemplate_attackFlagIdentifierCollision_shouldReject() {
        DeviceTemplateDto dto = buildTemplateWithVar("AttackCollision", "is_attack", null);

        BadRequestException ex = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("generated NuSMV identifier 'is_attack'")
                .contains("collides");
    }

    @Test
    void addDeviceTemplate_prefixedBusinessVariableWithoutGeneratedCollision_shouldAllow() throws Exception {
        DeviceTemplateDto dto = buildTemplateWithVar("PrefixedBusinessVariable", "trust_temperature", null);

        when(deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(1L, "PrefixedBusinessVariable")).thenReturn(false);
        when(deviceTemplateRepo.saveAndFlush(anyTemplatePo())).thenAnswer(inv -> {
            DeviceTemplatePo po = Objects.requireNonNull(inv.getArgument(0, DeviceTemplatePo.class));
            po.setId(302L);
            return po;
        });
        File precheckFile = File.createTempFile("template-precheck-", ".smv");
        when(smvGenerator.generate(
                anyLong(), anyList(), anyList(), anyList(), any(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class)))
                .thenReturn(new SmvGenerator.GenerateResult(precheckFile, Map.of()));

        DeviceTemplateDto saved = service.addDeviceTemplate(1L, dto);

        assertEquals(302L, saved.getId());
        assertFalse(precheckFile.exists());
    }

    @Test
    void addDeviceTemplate_impactedVariableWithoutOwnDomain_shouldReject() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setModes(List.of());
        manifest.setInitState("");
        manifest.setWorkingStates(List.of());
        manifest.setInternalVariables(List.of());
        manifest.setImpactedVariables(List.of("temperature"));

        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("Incomplete Actuator");
        dto.setManifest(manifest);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                service.addDeviceTemplate(1L, dto));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("has no domain in this manifest")
                // The remedy must name a field that still exists. This assertion used to require the
                // message to say "EnvironmentDomains", so it actively pinned advice the schema rejects.
                .contains("IsInside=false")
                .contains("Reads=false")
                .doesNotContain("EnvironmentDomains");
        verify(deviceTemplateRepo, never()).saveAndFlush(anyTemplatePo());
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

    private static BoardEditHistoryState historyState(int entryCount, String tokenCharacter) {
        return new BoardEditHistoryState(
                entryCount,
                new BoardUndoAvailability(entryCount > 0, false),
                tokenCharacter.repeat(64));
    }
}
