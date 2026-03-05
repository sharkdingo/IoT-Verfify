package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class DeviceNodeMapperTest {

    private final DeviceNodeMapper mapper = new DeviceNodeMapper();

    private DeviceNodePo samplePo(String state) {
        return DeviceNodePo.builder()
                .id("node_1")
                .userId(1L)
                .templateName("Light")
                .label("node_1")
                .posX(10.0)
                .posY(20.0)
                .width(100)
                .height(80)
                .state(state)
                .build();
    }

    // --- toDto state fallback ---

    @Test
    void toDto_normalState_preserved() {
        DeviceNodeDto dto = mapper.toDto(samplePo("on"));
        assertEquals("on", dto.getState());
    }

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = {"   ", "\t"})
    void toDto_blankOrNullState_fallsBackToWorking(String state) {
        DeviceNodeDto dto = mapper.toDto(samplePo(state));
        assertEquals("Working", dto.getState());
    }

    @Test
    void toDto_null_returnsNull() {
        assertNull(mapper.toDto(null));
    }

    // --- toDto field mapping ---

    @Test
    void toDto_mapsAllFields() {
        DeviceNodePo po = samplePo("off");
        po.setCurrentStateTrust("trusted");
        DeviceNodeDto dto = mapper.toDto(po);

        assertEquals("node_1", dto.getId());
        assertEquals("Light", dto.getTemplateName());
        assertEquals("node_1", dto.getLabel());
        assertEquals(10.0, dto.getPosition().getX());
        assertEquals(20.0, dto.getPosition().getY());
        assertEquals("off", dto.getState());
        assertEquals(100, dto.getWidth());
        assertEquals(80, dto.getHeight());
        assertEquals("trusted", dto.getCurrentStateTrust());
    }

    // --- toEntity ---

    @Test
    void toEntity_null_returnsNull() {
        assertNull(mapper.toEntity((DeviceNodeDto) null));
    }

    @Test
    void toEntity_withUserId_setsUserId() {
        DeviceNodeDto dto = mapper.toDto(samplePo("on"));
        DeviceNodePo po = mapper.toEntity(dto, 42L);
        assertEquals(42L, po.getUserId());
    }

    // --- toVerificationDto ---

    @Test
    void toVerificationDto_null_returnsNull() {
        assertNull(mapper.toVerificationDto(null));
    }

    @Test
    void toVerificationDto_mapsStateFromDto() {
        // Verify that toVerificationDto picks up the already-sanitized state from DTO
        DeviceNodeDto dto = mapper.toDto(samplePo(null)); // state fallback to "Working"
        DeviceVerificationDto vDto = mapper.toVerificationDto(dto);
        assertEquals("Working", vDto.getState());
        assertEquals("node_1", vDto.getVarName());
        assertEquals("Light", vDto.getTemplateName());
    }
}
