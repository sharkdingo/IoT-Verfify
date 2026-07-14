package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.BoardLayoutRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.mapper.BoardLayoutMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardStorageServiceImplLayoutTest {

    @Mock
    private BoardLayoutRepository layoutRepo;
    @Mock
    private UserRepository userRepository;

    private BoardStorageServiceImpl service;

    @BeforeEach
    void setUp() {
        service = new BoardStorageServiceImpl(
                null, null, null, null, layoutRepo, null, null, null,
                null, null, null, null, new BoardLayoutMapper(), null, null, userRepository);
    }

    @Test
    void getLayout_createsDefaultInspectorSectionAsDevices() {
        when(userRepository.findByIdForUpdate(7L)).thenReturn(Optional.of(new UserPo()));
        when(layoutRepo.findByUserId(7L)).thenReturn(Optional.empty());
        when(layoutRepo.save(any(BoardLayoutPo.class))).thenAnswer(invocation -> invocation.getArgument(0));

        BoardLayoutDto dto = service.getLayout(7L);

        ArgumentCaptor<BoardLayoutPo> saved = ArgumentCaptor.forClass(BoardLayoutPo.class);
        verify(layoutRepo).save(saved.capture());

        assertEquals("devices", saved.getValue().getInspectorPanelActiveSection());
        assertEquals("devices", dto.getPanels().getInspector().getActiveSection());
    }
}
