package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardSemanticSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.BoardEnvironmentVariablePo;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.po.RulePo;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.BoardEnvironmentVariableRepository;
import cn.edu.nju.Iot_Verify.repository.BoardLayoutRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.mapper.BoardLayoutMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.transaction.support.TransactionCallback;
import org.springframework.transaction.support.TransactionTemplate;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplSemanticSnapshotTest {

    @Mock private DeviceNodeRepository nodeRepo;
    @Mock private BoardEnvironmentVariableRepository environmentRepo;
    @Mock private SpecificationRepository specRepo;
    @Mock private RuleRepository ruleRepo;
    @Mock private BoardLayoutRepository layoutRepo;
    @Mock private DeviceTemplateRepository templateRepo;
    @Mock private TransactionTemplate transactionTemplate;
    @Mock private SpecificationMapper specificationMapper;
    @Mock private RuleMapper ruleMapper;
    @Mock private DeviceNodeMapper deviceNodeMapper;
    @Mock private BoardLayoutMapper boardLayoutMapper;
    @Mock private DeviceTemplateMapper deviceTemplateMapper;
    @Mock private UserRepository userRepository;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new BoardStorageServiceImpl(
                nodeRepo, environmentRepo, specRepo, ruleRepo, layoutRepo, templateRepo, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                boardLayoutMapper, deviceTemplateMapper, null, userRepository);
        when(transactionTemplate.execute(any())).thenAnswer(invocation ->
                ((TransactionCallback<?>) invocation.getArgument(0)).doInTransaction(null));
        when(userRepository.findByIdForUpdate(1L)).thenReturn(Optional.of(new UserPo()));
    }

    @Test
    void getSemanticSnapshot_readsEveryModelCollectionInsideOneLockedTransaction() {
        DeviceNodePo nodePo = new DeviceNodePo();
        DeviceNodeDto node = new DeviceNodeDto();
        BoardEnvironmentVariablePo environmentPo = BoardEnvironmentVariablePo.builder()
                .name("temperature").value("20").trust("trusted").privacy("public").build();
        RulePo rulePo = new RulePo();
        RuleDto rule = new RuleDto();
        SpecificationPo specPo = new SpecificationPo();
        SpecificationDto spec = new SpecificationDto();
        DeviceTemplatePo templatePo = new DeviceTemplatePo();
        DeviceTemplateDto template = new DeviceTemplateDto();

        when(nodeRepo.findByUserId(1L)).thenReturn(List.of(nodePo));
        when(deviceNodeMapper.toDto(nodePo)).thenReturn(node);
        when(environmentRepo.findByUserIdOrderByNameAsc(1L)).thenReturn(List.of(environmentPo));
        when(ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(1L)).thenReturn(List.of(rulePo));
        when(ruleMapper.toDto(rulePo)).thenReturn(rule);
        when(specRepo.findByUserId(1L)).thenReturn(List.of(specPo));
        when(specificationMapper.toDto(specPo)).thenReturn(spec);
        when(templateRepo.findByUserId(1L)).thenReturn(List.of(templatePo));
        when(deviceTemplateMapper.toDto(templatePo)).thenReturn(template);

        BoardSemanticSnapshotDto snapshot = service.getSemanticSnapshot(1L);

        assertSame(node, snapshot.nodes().get(0));
        assertEquals("20", snapshot.environmentVariables().get(0).getValue());
        assertSame(rule, snapshot.rules().get(0));
        assertSame(spec, snapshot.specifications().get(0));
        assertSame(template, snapshot.deviceTemplates().get(0));
        verify(transactionTemplate).execute(any());
        verify(userRepository).findByIdForUpdate(1L);
        verify(nodeRepo).findByUserId(1L);
        verify(environmentRepo).findByUserIdOrderByNameAsc(1L);
        verify(ruleRepo).findByUserIdOrderByExecutionOrderAscIdAsc(1L);
        verify(specRepo).findByUserId(1L);
        verify(templateRepo).findByUserId(1L);
    }
}
