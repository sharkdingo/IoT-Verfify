package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeUpdateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceUpdateResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BoardReplacementStaleException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariablePo;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.po.RulePo;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.BoardEnvironmentVariableRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.SmvConstants;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.ArgumentCaptor;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.transaction.support.TransactionCallback;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.test.util.ReflectionTestUtils;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.lenient;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.when;

/**
 * Verifies saveBoardBatch composes a complete board semantic replacement inside one transaction
 * and rejects stale destructive confirmations before any write.
 */
@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplBatchTest {

    @Mock private DeviceNodeRepository nodeRepo;
    @Mock private BoardEnvironmentVariableRepository environmentRepo;
    @Mock private RuleRepository ruleRepo;
    @Mock private SpecificationRepository specRepo;
    @Mock private DeviceTemplateRepository deviceTemplateRepo;
    @Mock private TransactionTemplate transactionTemplate;
    @Mock private DeviceNodeMapper deviceNodeMapper;
    @Mock private RuleMapper ruleMapper;
    @Mock private SpecificationMapper specificationMapper;
    @Mock private UserRepository userRepository;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        // Execute the transaction callback inline.
        lenient().when(transactionTemplate.execute(any())).thenAnswer(inv ->
                ((TransactionCallback<?>) inv.getArgument(0)).doInTransaction(null));
        lenient().when(userRepository.findByIdForUpdate(1L)).thenReturn(Optional.of(new UserPo()));
    }

    @Test
    void saveBoardBatch_savesAllThreeCollections() {
        DeviceNodeDto node = boardNode("node-1", null, "Device");
        RuleDto rule = RuleDto.builder().conditions(List.of()).build();
        SpecificationDto spec = new SpecificationDto();

        // node save path
        when(deviceNodeMapper.toEntity(any(), anyLong())).thenReturn(new DeviceNodePo());
        when(nodeRepo.saveAll(any())).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(new DeviceNodeDto());
        // rule save path (identity-preserving full-list save reads existing first)
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleMapper.toEntity(any(), anyLong())).thenReturn(new RulePo());
        // spec save path
        when(specificationMapper.toEntity(any(), anyLong())).thenReturn(new SpecificationPo());
        when(specRepo.saveAll(any())).thenReturn(List.of());

        BoardBatchDto result = service.saveBoardBatch(1L,
                confirmedBatch(service, new BoardBatchDto(List.of(node), List.of(rule), List.of(spec))));

        assertTrue(result != null);
        // All three replaced within the single transaction.
        verify(nodeRepo).deleteByUserId(1L);
        verify(specRepo).deleteByUserId(1L);
        verify(transactionTemplate, times(2)).execute(any());
    }

    @Test
    void saveBoardBatch_missingCollectionsRejectInsteadOfImplicitlyPreservingThem() {
        ValidationException error = assertThrows(ValidationException.class,
                () -> service.saveBoardBatch(1L, new BoardBatchDto(null, List.of(), null)));

        assertTrue(error.getErrors().containsKey("nodes"));
        assertTrue(error.getErrors().containsKey("specs"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(specRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void saveBoardBatch_rechecksCollectionLimitsInsideTheServiceBoundary() {
        BoardBatchDto oversized = new BoardBatchDto(
                java.util.Collections.nCopies(101, new DeviceNodeDto()), List.of(), List.of(), List.of());

        ValidationException error = assertThrows(
                ValidationException.class, () -> service.saveBoardBatch(1L, oversized));

        assertTrue(error.getErrors().containsKey("nodes"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void addNodes_rejectsWhenThePersistedBoardIsAlreadyAtCapacity() {
        when(nodeRepo.findByUserId(1L))
                .thenReturn(java.util.Collections.nCopies(100, new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(new DeviceNodeDto());

        BadRequestException error = assertThrows(BadRequestException.class,
                () -> service.addNodes(1L, List.of(new DeviceNodeDto()), List.of()));

        assertTrue(error.getMessage().contains("at most 100 devices"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void renameNode_rejectsAStaleDialogBeforeWriting() {
        DeviceNodePo stored = DeviceNodePo.builder()
                .id("device-1")
                .userId(1L)
                .label("Renamed elsewhere")
                .build();
        DeviceNodeDto current = boardNode("device-1", "Sensor", "Renamed elsewhere");
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(stored));
        when(deviceNodeMapper.toDto(stored)).thenReturn(current);

        ConflictException error = assertThrows(ConflictException.class,
                () -> service.renameNode(1L, "device-1", "My new name", "Original name"));

        assertTrue(error.getMessage().contains("changed after the rename dialog was opened"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(nodeRepo, never()).save(any());
    }

    @Test
    void renameNode_returnsConflictWhenAnotherTabClaimedTheRequestedLabel() {
        DeviceNodePo targetStored = DeviceNodePo.builder()
                .id("device-1")
                .userId(1L)
                .label("Original name")
                .build();
        DeviceNodePo competingStored = DeviceNodePo.builder()
                .id("device-2")
                .userId(1L)
                .label("Claimed name")
                .build();
        DeviceNodeDto target = boardNode("device-1", "Sensor", "Original name");
        DeviceNodeDto competing = boardNode("device-2", "Sensor", "Claimed name");
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(targetStored, competingStored));
        when(deviceNodeMapper.toDto(targetStored)).thenReturn(target);
        when(deviceNodeMapper.toDto(competingStored)).thenReturn(competing);

        ConflictException error = assertThrows(ConflictException.class,
                () -> service.renameNode(1L, "device-1", "claimed NAME", "Original name"));

        assertTrue(error.getMessage().contains("now used by another device"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(nodeRepo, never()).save(any());
        verify(nodeRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(anyLong());
        verify(specRepo, never()).saveAll(any());
    }

    @Test
    void addRule_rejectsWhenThePersistedBoardIsAlreadyAtCapacity() {
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L))
                .thenReturn(java.util.Collections.nCopies(100, new RulePo()));
        when(ruleMapper.toDto(any())).thenReturn(new RuleDto());

        BadRequestException error = assertThrows(
                BadRequestException.class, () -> service.addRule(1L, new RuleDto()));

        assertTrue(error.getMessage().contains("at most 100 rules"));
        verify(ruleRepo, never()).save(any());
    }

    @Test
    void addSpec_rejectsWhenThePersistedBoardIsAlreadyAtCapacity() {
        when(specRepo.findByUserId(1L))
                .thenReturn(java.util.Collections.nCopies(100, new SpecificationPo()));
        when(specificationMapper.toDto(any())).thenReturn(new SpecificationDto());

        BadRequestException error = assertThrows(
                BadRequestException.class, () -> service.addSpec(1L, new SpecificationDto()));

        assertTrue(error.getMessage().contains("at most 100 specifications"));
        verify(specRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void saveBoardBatch_staleConfirmationReturnsFreshImpactAndWritesNothing() {
        DeviceNodePo stored = new DeviceNodePo();
        DeviceNodeDto first = boardNode("device-1", "Sensor", "Hall sensor");
        DeviceNodeDto second = boardNode("device-2", "Sensor", "Kitchen sensor");
        when(nodeRepo.findByUserId(1L))
                .thenReturn(List.of(stored), List.of(stored, new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(first, first, second);

        var preview = service.previewBoardReplacement(1L);
        assertEquals(1, preview.getDeviceCount());
        assertTrue(preview.getImpactToken() != null && !preview.getImpactToken().isBlank());

        BoardBatchDto replacement = new BoardBatchDto(List.of(), List.of(), List.of(), List.of());
        replacement.setImpactToken(preview.getImpactToken());
        BoardReplacementStaleException error = assertThrows(
                BoardReplacementStaleException.class,
                () -> service.saveBoardBatch(1L, replacement));

        assertEquals(2, error.getCurrentPreview().getDeviceCount());
        assertTrue(!preview.getImpactToken().equals(error.getCurrentPreview().getImpactToken()));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(environmentRepo, never()).deleteByUserId(anyLong());
        verify(ruleRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void saveSpecsInternal_persistsAndReturnsTheSubmittedSpecificationOrder() {
        SpecificationDto first = new SpecificationDto();
        first.setId("spec-b");
        first.setTemplateId("1");
        first.setAConditions(List.of());
        first.setIfConditions(List.of());
        first.setThenConditions(List.of());
        SpecificationDto second = new SpecificationDto();
        second.setId("spec-a");
        second.setTemplateId("2");
        second.setAConditions(List.of());
        second.setIfConditions(List.of());
        second.setThenConditions(List.of());

        when(specificationMapper.toEntity(any(), anyLong())).thenAnswer(invocation -> {
            SpecificationDto dto = invocation.getArgument(0);
            return SpecificationPo.builder().id(dto.getId()).userId(1L).build();
        });
        when(specRepo.saveAll(any())).thenReturn(List.of());
        when(specificationMapper.toDto(any())).thenAnswer(invocation -> {
            SpecificationPo po = invocation.getArgument(0);
            SpecificationDto dto = new SpecificationDto();
            dto.setId(po.getId());
            return dto;
        });

        @SuppressWarnings("unchecked")
        List<SpecificationDto> saved = ReflectionTestUtils.invokeMethod(
                service, "saveSpecsInternal", 1L, List.of(first, second), List.of());

        ArgumentCaptor<List<SpecificationPo>> captor = ArgumentCaptor.forClass(List.class);
        verify(specRepo).saveAll(captor.capture());
        assertEquals(List.of(0, 1), captor.getValue().stream()
                .map(SpecificationPo::getListOrder).toList());
        assertEquals(List.of("spec-b", "spec-a"), saved.stream().map(SpecificationDto::getId).toList());
    }

    @Test
    void saveBoardBatch_canonicalizesRuleAndSpecRelationsAndTargetTypesBeforePersistence() {
        DeviceNodeDto node = boardNode("sensor1", "Temperature Sensor", "Living Sensor");

        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Temperature Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Temperature Sensor")
                        .internalVariables(List.of(
                                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                                        .name("temperature")
                                        .isInside(false)
                                        .lowerBound(0)
                                        .upperBound(100)
                                        .trust("untrusted")
                                        .privacy("public")
                                        .build()))
                        .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                                .name("cool")
                                .signal(false)
                                .build()))
                        .build()))
                .build();

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor1")
                        .attribute("temperature")
                        .targetType("Variable")
                        .relation(" GTE ")
                        .value("28")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor1")
                        .action("cool")
                        .build())
                .build();

        SpecConditionDto condition = new SpecConditionDto();
        condition.setId("c1");
        condition.setSide("a");
        condition.setDeviceId("sensor1");
        condition.setDeviceLabel("Stale internal label");
        condition.setTargetType("PRIVACY");
        condition.setKey("temperature");
        condition.setPropertyScope("VARIABLE");
        condition.setRelation(" NOT_IN ");
        condition.setValue("PUBLIC,PRIVATE");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec1");
        spec.setTemplateId("3");
        spec.setTemplateLabel("Misleading caller label");
        spec.setAConditions(List.of(condition));
        spec.setFormula("LTLSPEC FALSE -- caller supplied cache");
        spec.setDevices(List.of(new SpecificationDto.DeviceRefDto(
                "other-device", "Wrong device", List.of("wrong API"))));

        when(deviceNodeMapper.toEntity(any(), anyLong())).thenReturn(new DeviceNodePo());
        when(nodeRepo.saveAll(any())).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleMapper.toEntity(any(), anyLong())).thenReturn(new RulePo());
        when(specificationMapper.toEntity(any(), anyLong())).thenReturn(new SpecificationPo());
        when(specRepo.saveAll(any())).thenReturn(List.of());

        service.saveBoardBatch(1L,
                confirmedBatch(service, new BoardBatchDto(List.of(node), List.of(rule), List.of(spec))));

        verify(ruleMapper).toEntity(argThat(savedRule ->
                ">=".equals(savedRule.getConditions().get(0).getRelation())
                        && "variable".equals(savedRule.getConditions().get(0).getTargetType())), anyLong());
        verify(specificationMapper).toEntity(argThat(savedSpec ->
                "not in".equals(savedSpec.getAConditions().get(0).getRelation())
                        && "privacy".equals(savedSpec.getAConditions().get(0).getTargetType())
                        && "variable".equals(savedSpec.getAConditions().get(0).getPropertyScope())
                        && "public, private".equals(savedSpec.getAConditions().get(0).getValue())
                        && "Living Sensor".equals(savedSpec.getAConditions().get(0).getDeviceLabel())
                        && "Never".equals(savedSpec.getTemplateLabel())
                        && savedSpec.getFormula().contains("not in {public, private}")
                        && savedSpec.getDevices().size() == 1
                        && "sensor1".equals(savedSpec.getDevices().get(0).getDeviceId())
                        && savedSpec.getDevices().get(0).getSelectedApis().isEmpty()), anyLong());
    }

    @Test
    void apiEventConditionWithoutRelationIsNotTreatedAsAnAdjustableParameter() {
        RuleDto.Condition apiEvent = RuleDto.Condition.builder()
                .deviceName("camera_1")
                .attribute("take photo")
                .targetType("api")
                .build();

        Boolean parameterizable = ReflectionTestUtils.invokeMethod(
                service,
                "isParameterizableBoardCondition",
                apiEvent,
                java.util.Map.of(),
                java.util.Map.of());

        assertEquals(Boolean.FALSE, parameterizable);
    }

    @Test
    void saveBoardBatch_savesEnvironmentVariablesWithImportedNodes() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Thermostat")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .lowerBound(0)
                        .upperBound(50)
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Thermostat")
                .manifestJson(JsonUtils.toJson(manifest))
                .defaultTemplate(true)
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("thermostat_1");
        node.setTemplateName("Thermostat");
        node.setLabel("Living Thermostat");
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(10.0);
        position.setY(20.0);
        node.setPosition(position);
        node.setState("Working");
        node.setWidth(176);
        node.setHeight(128);

        BoardEnvironmentVariableDto importedEnvironment =
                new BoardEnvironmentVariableDto("temperature", "26", "untrusted", "private");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(deviceNodeMapper.toEntity(any(), anyLong())).thenReturn(new DeviceNodePo());
        when(nodeRepo.saveAll(any())).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of());
        when(environmentRepo.saveAll(any())).thenAnswer(inv -> inv.getArgument(0));
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(specRepo.saveAll(any())).thenReturn(List.of());

        BoardBatchDto result = serviceWithEnvironment.saveBoardBatch(1L,
                confirmedBatch(serviceWithEnvironment,
                        new BoardBatchDto(List.of(node), List.of(importedEnvironment), List.of(), List.of())));

        assertEquals(1, result.getEnvironmentVariables().size());
        BoardEnvironmentVariableDto savedEnvironment = result.getEnvironmentVariables().get(0);
        assertEquals("temperature", savedEnvironment.getName());
        assertEquals("26", savedEnvironment.getValue());
        assertEquals("untrusted", savedEnvironment.getTrust());
        assertEquals("private", savedEnvironment.getPrivacy());
        verify(environmentRepo, atLeastOnce()).deleteByUserId(1L);
        verify(environmentRepo, atLeastOnce()).saveAll(argThat(saved -> {
            for (BoardEnvironmentVariablePo po : saved) {
                if ("temperature".equals(po.getName())
                        && "26".equals(po.getValue())
                        && "untrusted".equals(po.getTrust())
                        && "private".equals(po.getPrivacy())) {
                    return true;
                }
            }
            return false;
        }));
    }

    @Test
    void saveBoardBatch_rejectsActiveDevicesWithConflictingEnvironmentSemantics() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest.InternalVariable slowTemperature =
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(false)
                        .lowerBound(0).upperBound(100).naturalChangeRate("[-1,1]")
                        .trust("untrusted").privacy("public").build();
        DeviceTemplateDto.DeviceManifest.InternalVariable fastTemperature =
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(false)
                        .lowerBound(0).upperBound(100).naturalChangeRate("[-5,5]")
                        .trust("untrusted").privacy("public").build();
        DeviceTemplatePo firstTemplate = DeviceTemplatePo.builder()
                .userId(1L).name("Indoor Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Indoor Sensor").internalVariables(List.of(slowTemperature)).build()))
                .build();
        DeviceTemplatePo secondTemplate = DeviceTemplatePo.builder()
                .userId(1L).name("Outdoor Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Outdoor Sensor").internalVariables(List.of(fastTemperature)).build()))
                .build();
        DeviceNodeDto indoor = boardNode("indoor_1", "Indoor Sensor", "Hallway sensor");
        DeviceNodeDto outdoor = boardNode("outdoor_1", "Outdoor Sensor", "Patio sensor");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(firstTemplate, secondTemplate));

        ValidationException exception = assertThrows(ValidationException.class, () ->
                serviceWithTemplates.saveBoardBatch(1L, confirmedBatch(serviceWithTemplates, new BoardBatchDto(
                        List.of(indoor, outdoor),
                        List.of(new BoardEnvironmentVariableDto("temperature", "20", "untrusted", "public")),
                        List.of(), List.of()))));

        String message = String.join(" ", exception.getErrors().values());
        assertTrue(message.contains("natural-change-rate mismatch"), message);
        assertTrue(message.contains("Hallway sensor"), message);
        assertTrue(message.contains("Patio sensor"), message);
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_rejectsDeviceReferenceThatCollidesWithGeneratedEnvironmentName() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Sensor")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature").isInside(false)
                        .lowerBound(0).upperBound(50)
                        .trust("trusted").privacy("public")
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L).name("Sensor").manifestJson(JsonUtils.toJson(manifest)).build();
        DeviceNodeDto node = boardNode("a_temperature", "Sensor", "Living-room sensor");
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException error = assertThrows(ValidationException.class, () ->
                serviceWithTemplates.saveBoardBatch(1L, confirmedBatch(serviceWithTemplates, new BoardBatchDto(
                        List.of(node),
                        List.of(new BoardEnvironmentVariableDto("temperature", "20", "trusted", "public")),
                        List.of(), List.of()))));

        String reason = error.getErrors().get("nodes[0].id");
        assertTrue(reason.contains("Living-room sensor"), reason);
        assertTrue(reason.contains("shared environment value 'temperature'"), reason);
        assertTrue(reason.contains("display name may stay unchanged"), reason);
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_rejectsDeviceReferenceThatWouldDisableRulePlaybackAndAttackAnalysis() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Switch")
                .modes(List.of("Power"))
                .initState("off")
                .workingStates(List.of(workingState("off"), workingState("on")))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("turnOn").signal(false).build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L).name("Switch").manifestJson(JsonUtils.toJson(manifest)).build();
        String nodeId = SmvConstants.RULE_EXECUTION_PROBE_PREFIX + "0";
        DeviceNodeDto node = boardNode(nodeId, "Switch", "Hall switch");
        node.setState("off");
        RuleDto rule = RuleDto.builder()
                .ruleString("Turn on the hall switch when it is off")
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName(nodeId).attribute("state").targetType("state")
                        .relation("=").value("off").build()))
                .command(RuleDto.Command.builder().deviceName(nodeId).action("turnOn").build())
                .build();
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        ValidationException error = assertThrows(ValidationException.class, () ->
                serviceWithTemplates.saveBoardBatch(1L, confirmedBatch(serviceWithTemplates, new BoardBatchDto(
                        List.of(node), List.of(), List.of(rule), List.of()))));

        String reason = error.getErrors().get("nodes[0].id");
        assertTrue(reason.contains("rule playback tracking"), reason);
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    private static DeviceNodeDto boardNode(String id, String templateName, String label) {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId(id);
        node.setTemplateName(templateName);
        node.setLabel(label);
        node.setWidth(176);
        node.setHeight(128);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(0.0);
        position.setY(0.0);
        node.setPosition(position);
        return node;
    }

    private static BoardBatchDto confirmedBatch(BoardStorageServiceImpl target, BoardBatchDto batch) {
        batch.setImpactToken(target.previewBoardReplacement(1L).getImpactToken());
        return batch;
    }

    @Test
    void saveBoardBatch_sceneImportRejectsMissingEnvironmentValuesBeforeBoardMutation() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Thermostat")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .lowerBound(0)
                        .upperBound(50)
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Thermostat")
                .manifestJson(JsonUtils.toJson(manifest))
                .defaultTemplate(true)
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("thermostat_1");
        node.setTemplateName("Thermostat");
        node.setLabel("Living Thermostat");
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(10.0);
        position.setY(20.0);
        node.setPosition(position);
        node.setState("Working");
        node.setWidth(176);
        node.setHeight(128);

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));

        BoardBatchDto batch = new BoardBatchDto(List.of(node), List.of(), List.of(), List.of());
        DeviceTemplateDto snapshot = new DeviceTemplateDto();
        snapshot.setName("Thermostat");
        snapshot.setManifest(manifest);
        snapshot.setDefaultTemplate(true);
        batch.setTemplateSnapshots(List.of(snapshot));
        ValidationException error = assertThrows(
                ValidationException.class,
                () -> serviceWithEnvironment.saveBoardBatch(
                        1L, confirmedBatch(serviceWithEnvironment, batch)));

        assertTrue(error.getErrors().values().stream()
                .anyMatch(message -> message.contains("missing required environment variables")));
        verify(nodeRepo, never()).deleteByUserId(1L);

        batch.setEnvironmentVariables(List.of(
                new BoardEnvironmentVariableDto("temperature", null, "trusted", "public")));
        ValidationException missingValue = assertThrows(
                ValidationException.class,
                () -> serviceWithEnvironment.saveBoardBatch(1L, batch));
        assertTrue(missingValue.getErrors().get("environmentVariables[0].value")
                .contains("explicit and non-blank"));
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void updateEnvironmentVariables_resetsOneVariableToTemplateDefaultsInsideAtomicMutation() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Thermostat")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .lowerBound(0)
                        .upperBound(50)
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Thermostat")
                .manifestJson(JsonUtils.toJson(manifest))
                .defaultTemplate(true)
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("thermostat_1");
        node.setTemplateName("Thermostat");
        BoardEnvironmentVariablePo previous = BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("27")
                .trust("untrusted")
                .privacy("private")
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of(previous));
        when(environmentRepo.saveAll(any())).thenAnswer(inv -> inv.getArgument(0));

        List<BoardEnvironmentVariableDto> result = serviceWithEnvironment.updateEnvironmentVariables(
                1L,
                current -> List.of(new BoardEnvironmentVariableDto(
                        current.get(0).getName(), null, null, null)));

        assertEquals(1, result.size());
        assertEquals("temperature", result.get(0).getName());
        assertEquals("0", result.get(0).getValue());
        assertEquals("trusted", result.get(0).getTrust());
        assertEquals("public", result.get(0).getPrivacy());
        verify(transactionTemplate).execute(any());
    }

    @Test
    void saveEnvironmentVariables_preservesEveryFieldNotPresentInThePatch() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Thermostat")
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .lowerBound(0)
                        .upperBound(50)
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Thermostat")
                .manifestJson(JsonUtils.toJson(manifest))
                .defaultTemplate(true)
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("thermostat_1");
        node.setTemplateName("Thermostat");
        BoardEnvironmentVariablePo previous = BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("27")
                .trust("untrusted")
                .privacy("private")
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of(previous));
        when(environmentRepo.saveAll(any())).thenAnswer(inv -> inv.getArgument(0));

        EnvironmentMutationResultDto result = serviceWithEnvironment.saveEnvironmentVariables(
                1L,
                List.of(new BoardEnvironmentVariableDto(
                        "temperature", null, "trusted", null)));

        assertEquals("updated", result.getOperation());
        assertEquals(1, result.getCurrentCount());
        assertEquals(List.of(new BoardEnvironmentVariableDto(
                "temperature", "27", "trusted", "private")), result.getEnvironmentVariables());
        assertEquals(1, result.getPatchResults().size());
        assertEquals(List.of("trust"), result.getPatchResults().get(0).getSuppliedFields());
        assertEquals(List.of("trust"), result.getPatchResults().get(0).getChangedFields());
        assertEquals(List.of("value", "privacy"), result.getPatchResults().get(0).getPreservedFields());
        assertEquals("27", result.getPatchResults().get(0).getPreviousValue().getValue());
        assertEquals("private", result.getPatchResults().get(0).getCurrentValue().getPrivacy());
        assertEquals(1, result.getEnvironmentChanges().size());
        assertEquals(EnvironmentVariableChangeDto.ChangeType.UPDATED,
                result.getEnvironmentChanges().get(0).getChangeType());
        verify(environmentRepo).saveAll(argThat(saved -> {
            for (BoardEnvironmentVariablePo variable : saved) {
                if ("temperature".equals(variable.getName())
                        && "27".equals(variable.getValue())
                        && "trusted".equals(variable.getTrust())
                        && "private".equals(variable.getPrivacy())) {
                    return true;
                }
            }
            return false;
        }));
    }

    @Test
    void updateNodeLayout_changesOnlyCanvasFields() {
        DeviceNodeMapper realMapper = new DeviceNodeMapper();
        BoardStorageServiceImpl serviceWithRealMapper = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, realMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        DeviceNodePo stored = DeviceNodePo.builder()
                .id("switch_1")
                .userId(1L)
                .templateName("Switch")
                .label("Hall switch")
                .posX(10.0)
                .posY(20.0)
                .state("on")
                .width(176)
                .height(128)
                .currentStateTrust("trusted")
                .currentStatePrivacy("private")
                .variablesJson("[{\"name\":\"level\",\"value\":\"2\",\"trust\":\"trusted\"}]")
                .privaciesJson("[{\"name\":\"level\",\"privacy\":\"private\"}]")
                .build();
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(35.0);
        position.setY(45.0);

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(stored));
        when(nodeRepo.findById(new cn.edu.nju.Iot_Verify.po.DeviceNodeId("switch_1", 1L)))
                .thenReturn(Optional.of(stored));
        when(nodeRepo.save(any())).thenAnswer(inv -> inv.getArgument(0));

        DeviceUpdateResultDto result = serviceWithRealMapper.updateNodeLayout(
                1L, "switch_1", new DeviceLayoutDto(position, 190, 140));

        assertEquals("layout", result.getMutationType());
        assertEquals("updated", result.getOperation());
        assertEquals(List.of("position.x", "position.y", "width", "height"), result.getChangedFields());
        assertEquals("on", result.getCurrentDevice().getState());
        assertEquals("trusted", result.getCurrentDevice().getCurrentStateTrust());
        assertEquals("private", result.getCurrentDevice().getCurrentStatePrivacy());
        assertEquals("2", result.getCurrentDevice().getVariables().get(0).getValue());
        assertEquals("private", result.getCurrentDevice().getPrivacies().get(0).getPrivacy());
        assertEquals("Hall switch", result.getCurrentDevice().getLabel());
        assertEquals(35.0, result.getCurrentDevice().getPosition().getX());
        assertEquals(190, result.getCurrentDevice().getWidth());
    }

    @Test
    void saveNodes_acceptsPortableSceneLayoutBoundaries() {
        DeviceNodeDto node = boardNode("device-1", null, "Device");
        node.setWidth(DeviceLayoutDto.MAX_WIDTH);
        node.setHeight(DeviceLayoutDto.MIN_HEIGHT);

        when(deviceNodeMapper.toEntity(any(), anyLong())).thenReturn(new DeviceNodePo());
        when(nodeRepo.saveAll(any())).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);

        List<DeviceNodeDto> saved = service.saveNodes(1L, List.of(node));

        assertEquals(DeviceLayoutDto.MAX_WIDTH, saved.get(0).getWidth());
        assertEquals(DeviceLayoutDto.MIN_HEIGHT, saved.get(0).getHeight());
        verify(nodeRepo).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_rejectsLayoutOutsidePortableSceneRangeBeforeMutation() {
        DeviceNodeDto node = boardNode("device-1", null, "Device");
        node.setWidth(DeviceLayoutDto.MAX_WIDTH + 1);

        ValidationException error = assertThrows(ValidationException.class, () ->
                service.saveBoardBatch(1L,
                        confirmedBatch(service, new BoardBatchDto(List.of(node), List.of(), List.of()))));

        assertEquals("Width must be within 80..2000", error.getErrors().get("nodes[0].width"));
        verify(nodeRepo, never()).deleteByUserId(1L);
    }

    @Test
    void updateNodeRuntime_changesOnlyDeviceLocalRuntimeFields() {
        DeviceNodeMapper realMapper = new DeviceNodeMapper();
        BoardStorageServiceImpl serviceWithRealMapper = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, realMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        DeviceNodePo stored = DeviceNodePo.builder()
                .id("switch_1")
                .userId(1L)
                .templateName("Switch")
                .label("Hall switch")
                .posX(10.0)
                .posY(20.0)
                .state("off")
                .width(176)
                .height(128)
                .currentStateTrust("trusted")
                .currentStatePrivacy("public")
                .build();
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Switch")
                .modes(List.of("Power"))
                .initState("off")
                .workingStates(List.of(workingState("off"), workingState("on")))
                .apis(List.of())
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Switch")
                .manifestJson(JsonUtils.toJson(manifest))
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(stored));
        when(nodeRepo.findById(new cn.edu.nju.Iot_Verify.po.DeviceNodeId("switch_1", 1L)))
                .thenReturn(Optional.of(stored));
        when(nodeRepo.save(any())).thenAnswer(inv -> inv.getArgument(0));
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        DeviceUpdateResultDto result = serviceWithRealMapper.updateNodeRuntime(
                1L, "switch_1", new DeviceRuntimeUpdateDto(
                        "on", "trusted", "public", null, null));

        assertEquals("runtime", result.getMutationType());
        assertEquals("updated", result.getOperation());
        assertEquals(List.of("state"), result.getChangedFields());
        assertEquals("on", result.getCurrentDevice().getState());
        assertEquals("Hall switch", result.getCurrentDevice().getLabel());
        assertEquals("Switch", result.getCurrentDevice().getTemplateName());
        assertEquals(10.0, result.getCurrentDevice().getPosition().getX());
        assertEquals(20.0, result.getCurrentDevice().getPosition().getY());
        assertEquals(176, result.getCurrentDevice().getWidth());
        assertEquals(128, result.getCurrentDevice().getHeight());
    }

    @Test
    void addSpec_rejectsUntrustedSourceSafetyApiWithoutModeledEndState() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);
        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Notification Service")
                .modes(List.of("Status"))
                .initState("idle")
                .workingStates(List.of(workingState("idle")))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("notify")
                        .signal(true)
                        .build()))
                .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Notification Service")
                .manifestJson(JsonUtils.toJson(manifest))
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("service_1");
        node.setLabel("Notification Service");
        node.setTemplateName("Notification Service");
        SpecConditionDto condition = new SpecConditionDto();
        condition.setId("condition-1");
        condition.setSide("a");
        condition.setDeviceId("service_1");
        condition.setTargetType("api");
        condition.setKey("notify");
        condition.setRelation("=");
        condition.setValue("TRUE");
        SpecificationDto spec = new SpecificationDto();
        spec.setId("safety-1");
        spec.setTemplateId("7");
        spec.setAConditions(List.of(condition));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        ValidationException error = assertThrows(
                ValidationException.class,
                () -> serviceWithTemplates.addSpec(1L, spec));

        assertTrue(error.getErrors().values().stream().anyMatch(message -> message.contains("has no EndState")));
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_sceneTemplateMismatchRejectsBeforeBoardMutation() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest existingManifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Sensor")
                .description("Existing sensor")
                .build();
        DeviceTemplatePo existing = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Sensor")
                .manifestJson(JsonUtils.toJson(existingManifest))
                .build();
        DeviceTemplateDto.DeviceManifest importedManifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Sensor")
                .description("Different sensor semantics")
                .build();
        DeviceTemplateDto importedSnapshot = new DeviceTemplateDto();
        importedSnapshot.setName("Sensor");
        importedSnapshot.setManifest(importedManifest);
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("sensor_1");
        node.setTemplateName("Sensor");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(existing));
        BoardBatchDto batch = new BoardBatchDto(List.of(node), List.of(), List.of());
        batch.setEnvironmentVariables(List.of());
        batch.setTemplateSnapshots(List.of(importedSnapshot));

        assertThrows(ConflictException.class, () -> serviceWithTemplates.saveBoardBatch(
                1L, confirmedBatch(serviceWithTemplates, batch)));
        verify(nodeRepo, never()).deleteByUserId(1L);
        verify(ruleRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_sceneSnapshotNameMismatchRejectsBeforeBoardMutation() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Original Sensor")
                .description("Portable sensor semantics")
                .build();
        DeviceTemplateDto snapshot = new DeviceTemplateDto();
        snapshot.setName("Renamed Sensor");
        snapshot.setManifest(manifest);
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("sensor_1");
        node.setTemplateName("Renamed Sensor");

        BoardBatchDto batch = new BoardBatchDto(List.of(node), List.of(), List.of());
        batch.setEnvironmentVariables(List.of());
        batch.setTemplateSnapshots(List.of(snapshot));

        BadRequestException error = assertThrows(
                BadRequestException.class,
                () -> serviceWithTemplates.saveBoardBatch(
                        1L, confirmedBatch(serviceWithTemplates, batch)));

        assertTrue(error.getMessage().contains("must exactly match manifest.Name"));
        assertTrue(error.getMessage().contains("cannot rename"));
        verifyNoInteractions(deviceTemplateRepo);
        verify(nodeRepo, never()).deleteByUserId(1L);
        verify(ruleRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_sceneReplacementRequiresEverySemanticCollection() {
        BoardBatchDto batch = new BoardBatchDto(List.of(), null, List.of(), List.of());
        batch.setTemplateSnapshots(List.of());

        ValidationException error = assertThrows(
                ValidationException.class,
                () -> service.saveBoardBatch(1L, batch));

        assertTrue(error.getErrors().containsKey("environmentVariables"));
        verify(nodeRepo, never()).deleteByUserId(1L);
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_missingTemplateSnapshotRejectsEvenWhenTemplateAlreadyExists() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Sensor")
                .description("Portable sensor semantics")
                .build();
        DeviceTemplatePo existing = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Sensor")
                .manifestJson(JsonUtils.toJson(manifest))
                .build();
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("sensor_1");
        node.setTemplateName("Sensor");

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(existing));
        BoardBatchDto batch = new BoardBatchDto(List.of(node), List.of(), List.of());
        batch.setEnvironmentVariables(List.of());
        batch.setTemplateSnapshots(List.of());

        BadRequestException error = assertThrows(
                BadRequestException.class,
                () -> serviceWithTemplates.saveBoardBatch(
                        1L, confirmedBatch(serviceWithTemplates, batch)));

        assertTrue(error.getMessage().contains("self-contained"));
        verify(nodeRepo, never()).deleteByUserId(1L);
        verify(ruleRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void saveBoardBatch_unreferencedTemplateSnapshotRejectsBeforeBoardMutation() {
        BoardStorageServiceImpl serviceWithTemplates = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Unused Sensor")
                .description("Not referenced by any imported device")
                .build();
        DeviceTemplateDto snapshot = new DeviceTemplateDto();
        snapshot.setName("Unused Sensor");
        snapshot.setManifest(manifest);

        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of());
        BoardBatchDto batch = new BoardBatchDto(List.of(), List.of(), List.of());
        batch.setEnvironmentVariables(List.of());
        batch.setTemplateSnapshots(List.of(snapshot));

        BadRequestException error = assertThrows(
                BadRequestException.class,
                () -> serviceWithTemplates.saveBoardBatch(
                        1L, confirmedBatch(serviceWithTemplates, batch)));

        assertTrue(error.getMessage().contains("unreferenced template snapshot"));
        verify(nodeRepo, never()).deleteByUserId(1L);
        verify(ruleRepo, never()).saveAll(any());
        verify(specRepo, never()).deleteByUserId(1L);
    }

    @Test
    void addRule_canonicalizesRelationAndTargetTypeBeforePersistence() {
        DeviceNodeDto node = boardNode("sensor1", null, "Sensor");

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor1")
                        .attribute("temperature")
                        .targetType("VARIABLE")
                        .relation(" LTE ")
                        .value("20")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor1")
                        .action("heat")
                        .build())
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(node);
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of(), List.of());
        when(ruleMapper.toEntity(any(), anyLong())).thenReturn(new RulePo());
        RulePo savedEntity = new RulePo();
        savedEntity.setId(1L);
        when(ruleRepo.save(any())).thenReturn(savedEntity);

        service.addRule(1L, rule);

        verify(ruleMapper).toEntity(argThat(savedRule ->
                savedRule.getId() == null
                        && "<=".equals(savedRule.getConditions().get(0).getRelation())
                        && "variable".equals(savedRule.getConditions().get(0).getTargetType())), anyLong());
    }

    @Test
    void reorderRules_persistsTheCompleteUserControlledExecutionOrder() {
        RulePo firstPo = RulePo.builder().id(1L).userId(1L).executionOrder(0).build();
        RulePo secondPo = RulePo.builder().id(2L).userId(1L).executionOrder(1).build();
        RuleDto first = RuleDto.builder().id(1L).ruleString("first")
                .conditions(List.of()).command(RuleDto.Command.builder().action("off").build()).build();
        RuleDto second = RuleDto.builder().id(2L).ruleString("second")
                .conditions(List.of()).command(RuleDto.Command.builder().action("on").build()).build();

        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L))
                .thenReturn(List.of(firstPo, secondPo), List.of(secondPo, firstPo));
        when(ruleMapper.toDto(firstPo)).thenReturn(first);
        when(ruleMapper.toDto(secondPo)).thenReturn(second);
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of(firstPo, secondPo));
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleMapper.toEntity(any(), anyLong())).thenAnswer(invocation -> new RulePo());

        List<RuleDto> saved = service.reorderRules(1L, List.of(2L, 1L));

        assertEquals(List.of(2L, 1L), saved.stream().map(RuleDto::getId).toList());
        ArgumentCaptor<RulePo> captor = ArgumentCaptor.forClass(RulePo.class);
        verify(ruleRepo, times(2)).save(captor.capture());
        assertEquals(List.of(0, 1), captor.getAllValues().stream()
                .map(RulePo::getExecutionOrder).toList());
        assertEquals(List.of(2L, 1L), captor.getAllValues().stream()
                .map(RulePo::getId).toList());
    }

    @Test
    void addRule_whenIdenticalRuleAlreadyExists_rejectsInsideWriteLockBeforeSave() {
        RuleDto existing = RuleDto.builder()
                .id(9L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor1")
                        .attribute("temperature")
                        .targetType("variable")
                        .relation(">=")
                        .value("30")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("ac1")
                        .action("cool")
                        .build())
                .build();
        RuleDto duplicate = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor1")
                        .attribute("temperature")
                        .targetType("VARIABLE")
                        .relation("GTE")
                        .value("30")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("ac1")
                        .action("cool")
                        .build())
                .build();
        RulePo existingPo = new RulePo();

        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of(existingPo));
        when(ruleMapper.toDto(existingPo)).thenReturn(existing);
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());

        ConflictException error = assertThrows(ConflictException.class,
                () -> service.addRule(1L, duplicate));

        assertTrue(error.getMessage().contains("identical automation rules"));
        assertTrue(error.getMessage().contains("temperature >= 30"));
        verify(ruleRepo, never()).save(any());
    }

    @Test
    void addSpec_whenSemanticInputsAreIdentical_rejectsBeforeReplacingCollection() {
        SpecConditionDto firstCondition = new SpecConditionDto();
        firstCondition.setId("old-1");
        firstCondition.setSide("a");
        firstCondition.setDeviceId("sensor1");
        firstCondition.setDeviceLabel("Old label");
        firstCondition.setTargetType("variable");
        firstCondition.setKey("temperature");
        firstCondition.setRelation(">=");
        firstCondition.setValue("30");

        SpecConditionDto secondCondition = new SpecConditionDto();
        secondCondition.setId("old-2");
        secondCondition.setSide("a");
        secondCondition.setDeviceId("sensor1");
        secondCondition.setDeviceLabel("Old label");
        secondCondition.setTargetType("mode");
        secondCondition.setKey("Mode");
        secondCondition.setRelation("in");
        secondCondition.setValue("away, home");

        SpecificationDto existing = new SpecificationDto();
        existing.setId("spec-existing");
        existing.setTemplateId("1");
        existing.setTemplateLabel("Always");
        existing.setAConditions(List.of(firstCondition, secondCondition));
        existing.setFormula("display cache one");

        SpecConditionDto duplicateSecond = new SpecConditionDto();
        duplicateSecond.setId("new-2");
        duplicateSecond.setSide("a");
        duplicateSecond.setDeviceId("sensor1");
        duplicateSecond.setDeviceLabel("New label");
        duplicateSecond.setTargetType("mode");
        duplicateSecond.setKey("Mode");
        duplicateSecond.setRelation("IN");
        duplicateSecond.setValue("home|away");

        SpecConditionDto duplicateFirst = new SpecConditionDto();
        duplicateFirst.setId("new-1");
        duplicateFirst.setSide("a");
        duplicateFirst.setDeviceId("sensor1");
        duplicateFirst.setDeviceLabel("New label");
        duplicateFirst.setTargetType("VARIABLE");
        duplicateFirst.setKey("temperature");
        duplicateFirst.setRelation("GTE");
        duplicateFirst.setValue("30");

        SpecificationDto duplicate = new SpecificationDto();
        duplicate.setId("spec-new");
        duplicate.setTemplateId("1");
        duplicate.setTemplateLabel("Different display label");
        duplicate.setAConditions(List.of(duplicateSecond, duplicateFirst));
        duplicate.setFormula("different preview cache");

        SpecificationPo existingPo = new SpecificationPo();
        DeviceNodePo nodePo = new DeviceNodePo();
        DeviceNodeDto node = boardNode("sensor1", null, "Living Sensor");

        when(specRepo.findByUserId(1L)).thenReturn(List.of(existingPo));
        when(specificationMapper.toDto(existingPo)).thenReturn(existing);
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(nodePo));
        when(deviceNodeMapper.toDto(nodePo)).thenReturn(node);

        ConflictException error = assertThrows(ConflictException.class,
                () -> service.addSpec(1L, duplicate));

        assertTrue(error.getMessage().contains("identical specifications"));
        assertTrue(error.getMessage().contains("Living Sensor.temperature >= 30"));
        verify(specRepo, never()).deleteByUserId(anyLong());
        verify(specRepo, never()).saveAll(any());
    }

    @Test
    void deleteNodeCascade_whenConfirmedDependenciesDrift_rejectsBeforeAnyWrite() {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("sensor1");
        DeviceNodePo nodePo = new DeviceNodePo();

        RuleDto relatedRule = RuleDto.builder()
                .id(17L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor1")
                        .attribute("temperature")
                        .relation(">")
                        .value("30")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor1")
                        .action("notify")
                        .build())
                .build();
        RulePo rulePo = new RulePo();

        SpecConditionDto specCondition = new SpecConditionDto();
        specCondition.setDeviceId("sensor1");
        SpecificationDto relatedSpec = new SpecificationDto();
        relatedSpec.setId("spec-1");
        relatedSpec.setAConditions(List.of(specCondition));
        SpecificationPo specPo = new SpecificationPo();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(nodePo));
        when(deviceNodeMapper.toDto(nodePo)).thenReturn(node);
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of(rulePo));
        when(ruleMapper.toDto(rulePo)).thenReturn(relatedRule);
        when(specRepo.findByUserId(1L)).thenReturn(List.of(specPo));
        when(specificationMapper.toDto(specPo)).thenReturn(relatedSpec);

        assertThrows(ConflictException.class,
                () -> service.deleteNodeCascade(1L, "sensor1", "stale-token"));

        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(ruleRepo, never()).deleteById(anyLong());
        verify(ruleRepo, never()).save(any());
        verify(specRepo, never()).deleteByUserId(anyLong());
        verify(specRepo, never()).saveAll(any());
    }

    @Test
    void deleteNodeCascade_acceptsTheExactOpaquePreviewToken() {
        DeviceNodeDto node = boardNode("sensor1", "Sensor", "Hall sensor");
        DeviceNodePo nodePo = new DeviceNodePo();
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(nodePo));
        when(deviceNodeMapper.toDto(nodePo)).thenReturn(node);
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());
        when(nodeRepo.saveAll(any())).thenReturn(List.of());
        when(specRepo.saveAll(any())).thenReturn(List.of());

        var preview = service.previewNodeDeletion(1L, "sensor1");
        var result = service.deleteNodeCascade(1L, "sensor1", preview.getImpactToken());

        assertEquals("deleted", result.getOperation());
        assertEquals("sensor1", result.getDeletedDevice().getId());
        assertEquals(preview.getImpactToken(), result.getImpactToken());
        verify(nodeRepo).deleteByUserId(1L);
        verify(specRepo).deleteByUserId(1L);
    }

    @Test
    void createNode_returnsEnvironmentPoolChangesFromTheSameTransaction() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceTemplateDto.DeviceManifest.InternalVariable temperature =
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .falsifiableWhenCompromised(true)
                        .lowerBound(0)
                        .upperBound(100)
                        .trust("untrusted")
                        .privacy("public")
                        .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Temperature Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Temperature Sensor")
                        .internalVariables(List.of(temperature))
                        .build()))
                .build();
        DeviceNodeDto draft = boardNode("sensor1", "Temperature Sensor", "Hall sensor");
        DeviceNodePo savedNode = new DeviceNodePo();
        BoardEnvironmentVariablePo savedEnvironment = BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("0")
                .trust("untrusted")
                .privacy("public")
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());
        when(deviceNodeMapper.toEntity(draft, 1L)).thenReturn(savedNode);
        when(nodeRepo.saveAll(any())).thenReturn(List.of(savedNode));
        when(deviceNodeMapper.toDto(savedNode)).thenReturn(draft);
        when(environmentRepo.findByUserIdOrderByNameAsc(1L))
                .thenReturn(List.of(), List.of(), List.of(savedEnvironment));
        when(environmentRepo.saveAll(any())).thenReturn(List.of(savedEnvironment));

        var result = serviceWithEnvironment.createNode(1L, current -> {
            assertTrue(current.isEmpty());
            return draft;
        });

        assertEquals(List.of(new BoardEnvironmentVariableDto(
                "temperature", "0", "untrusted", "public")), result.getEnvironmentVariables());
        assertEquals(1, result.getEnvironmentChanges().size());
        assertEquals(EnvironmentVariableChangeDto.ChangeType.ADDED,
                result.getEnvironmentChanges().get(0).getChangeType());
        assertEquals("temperature", result.getEnvironmentChanges().get(0).getName());
        assertEquals("0", result.getEnvironmentChanges().get(0).getCurrentValue().getValue());
        verify(transactionTemplate).execute(any());
    }

    @Test
    void deletionPreviewIncludesEnvironmentRemovalAndConfirmationRejectsEnvironmentDrift() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceNodeDto node = boardNode("sensor1", "Temperature Sensor", "Hall sensor");
        DeviceNodePo nodePo = new DeviceNodePo();
        DeviceTemplateDto.DeviceManifest.InternalVariable temperature =
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .falsifiableWhenCompromised(true)
                        .lowerBound(0)
                        .upperBound(100)
                        .naturalChangeRate("[-1,1]")
                        .trust("untrusted")
                        .privacy("public")
                        .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Temperature Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Temperature Sensor")
                        .internalVariables(List.of(temperature))
                        .build()))
                .build();
        BoardEnvironmentVariablePo environment = BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("20")
                .trust("untrusted")
                .privacy("public")
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(nodePo));
        when(deviceNodeMapper.toDto(nodePo)).thenReturn(node);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of(environment));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        var preview = serviceWithEnvironment.previewNodeDeletion(1L, "sensor1");

        assertEquals(1, preview.getEnvironmentChanges().size());
        assertEquals(EnvironmentVariableChangeDto.ChangeType.REMOVED,
                preview.getEnvironmentChanges().get(0).getChangeType());
        assertEquals("temperature", preview.getEnvironmentChanges().get(0).getName());
        assertEquals("20", preview.getEnvironmentChanges().get(0).getPreviousValue().getValue());

        assertThrows(ConflictException.class, () -> serviceWithEnvironment.deleteNodeCascade(
                1L, "sensor1", "stale-token"));
        verify(nodeRepo, never()).deleteByUserId(anyLong());
    }

    @Test
    void deletionPreviewKeepsEnvironmentRequiredByAnotherDevice() {
        BoardStorageServiceImpl serviceWithEnvironment = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, null, deviceTemplateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, new DeviceTemplateMapper(), null, userRepository);

        DeviceNodeDto target = boardNode("sensor1", "Temperature Sensor", "Hall sensor");
        DeviceNodeDto remaining = boardNode("sensor2", "Temperature Sensor", "Bedroom sensor");
        DeviceNodePo targetPo = new DeviceNodePo();
        targetPo.setId("sensor1");
        targetPo.setUserId(1L);
        DeviceNodePo remainingPo = new DeviceNodePo();
        remainingPo.setId("sensor2");
        remainingPo.setUserId(1L);
        DeviceTemplateDto.DeviceManifest.InternalVariable temperature =
                DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .lowerBound(0)
                        .upperBound(100)
                        .naturalChangeRate("[-1,1]")
                        .trust("untrusted")
                        .privacy("public")
                        .build();
        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("Temperature Sensor")
                .manifestJson(JsonUtils.toJson(DeviceTemplateDto.DeviceManifest.builder()
                        .name("Temperature Sensor")
                        .internalVariables(List.of(temperature))
                        .build()))
                .build();
        BoardEnvironmentVariablePo environment = BoardEnvironmentVariablePo.builder()
                .userId(1L)
                .name("temperature")
                .value("20")
                .trust("untrusted")
                .privacy("public")
                .build();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(targetPo, remainingPo));
        when(deviceNodeMapper.toDto(targetPo)).thenReturn(target);
        when(deviceNodeMapper.toDto(remainingPo)).thenReturn(remaining);
        when(deviceTemplateRepo.findByUserId(1L)).thenReturn(List.of(template));
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of(environment));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        var preview = serviceWithEnvironment.previewNodeDeletion(1L, "sensor1");

        assertTrue(preview.getEnvironmentChanges().isEmpty());
        assertEquals(List.of(new BoardEnvironmentVariableDto(
                "temperature", "20", "untrusted", "public")), preview.getEnvironmentVariables());
    }

    private DeviceTemplateDto.DeviceManifest.WorkingState workingState(String name) {
        return DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                .name(name)
                .trust("trusted")
                .privacy("public")
                .dynamics(List.of())
                .build();
    }
}
