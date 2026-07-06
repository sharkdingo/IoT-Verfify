package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.RulePo;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

/**
 * Verifies saveBoardBatch composes the three collection saves inside a single transaction,
 * and that a null collection is left unchanged (returned from its current persisted value).
 */
@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplBatchTest {

    @Mock private DeviceNodeRepository nodeRepo;
    @Mock private RuleRepository ruleRepo;
    @Mock private SpecificationRepository specRepo;
    @Mock private TransactionTemplate transactionTemplate;
    @Mock private DeviceNodeMapper deviceNodeMapper;
    @Mock private RuleMapper ruleMapper;
    @Mock private SpecificationMapper specificationMapper;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new BoardStorageServiceImpl(
                nodeRepo, null, specRepo, ruleRepo, null, null, null,
                transactionTemplate, null, specificationMapper, ruleMapper, deviceNodeMapper,
                null, null, null, null);
        // Execute the transaction callback inline.
        when(transactionTemplate.execute(any())).thenAnswer(inv ->
                ((TransactionCallback<?>) inv.getArgument(0)).doInTransaction(null));
    }

    @Test
    void saveBoardBatch_savesAllThreeCollections() {
        DeviceNodeDto node = new DeviceNodeDto();
        RuleDto rule = RuleDto.builder().conditions(List.of()).build();
        SpecificationDto spec = new SpecificationDto();

        // node save path
        when(deviceNodeMapper.toEntity(any(), anyLong())).thenReturn(new DeviceNodePo());
        when(nodeRepo.saveAll(any())).thenReturn(List.of(new DeviceNodePo()));
        when(deviceNodeMapper.toDto(any())).thenReturn(new DeviceNodeDto());
        // rule save path (incremental upsert reads existing first)
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(ruleMapper.toEntity(any(), anyLong())).thenReturn(new RulePo());
        // spec save path
        when(specificationMapper.toEntity(any(), anyLong())).thenReturn(new SpecificationPo());
        when(specRepo.saveAll(any())).thenReturn(List.of());

        BoardBatchDto result = service.saveBoardBatch(1L,
                new BoardBatchDto(List.of(node), List.of(rule), List.of(spec)));

        assertTrue(result != null);
        // All three replaced within the single transaction.
        verify(nodeRepo).deleteByUserId(1L);
        verify(specRepo).deleteByUserId(1L);
        verify(transactionTemplate).execute(any());
    }

    @Test
    void saveBoardBatch_nullCollectionsLeftUnchanged() {
        // Only rules provided; nodes and specs are null → read current, do not delete/replace.
        when(ruleRepo.findByUserId(1L)).thenReturn(List.of());
        when(nodeRepo.findByUserId(1L)).thenReturn(List.of());
        when(specRepo.findByUserId(1L)).thenReturn(List.of());

        BoardBatchDto result = service.saveBoardBatch(1L, new BoardBatchDto(null, List.of(), null));

        assertEquals(0, result.getRules().size());
        // Null collections must NOT trigger a destructive replace.
        verify(nodeRepo, never()).deleteByUserId(anyLong());
        verify(specRepo, never()).deleteByUserId(anyLong());
    }
}
