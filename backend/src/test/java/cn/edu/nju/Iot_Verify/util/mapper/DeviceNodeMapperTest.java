package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
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

    // --- toDto state integrity ---

    @Test
    void toDto_normalState_preserved() {
        DeviceNodeDto dto = mapper.toDto(samplePo("on"));
        assertEquals("on", dto.getState());
    }

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = {"   ", "\t"})
    void toDto_blankOrNullState_failsClosed(String state) {
        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(samplePo(state)));
        assertEquals("state", error.getField());
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
        po.setCurrentStatePrivacy("private");
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
        assertEquals("private", dto.getCurrentStatePrivacy());
    }

    @Test
    void toDto_blankPersistedRuntimeJsonFailsClosed() {
        DeviceNodePo po = samplePo("off");
        po.setVariablesJson("  ");

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("variablesJson", error.getField());
    }

    // --- toEntity ---

    @Test
    void toEntity_null_returnsNull() {
        assertNull(mapper.toEntity((DeviceNodeDto) null));
    }

    @Test
    void toEntity_withUserId_setsUserId() {
        DeviceNodePo source = samplePo("on");
        source.setCurrentStateTrust("untrusted");
        source.setCurrentStatePrivacy("private");
        DeviceNodeDto dto = mapper.toDto(source);
        DeviceNodePo po = mapper.toEntity(dto, 42L);
        assertEquals(42L, po.getUserId());
        assertEquals("untrusted", po.getCurrentStateTrust());
        assertEquals("private", po.getCurrentStatePrivacy());
    }

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = {"   ", "\t"})
    void toEntity_blankOrNullState_isCanonicalizedToWorking(String state) {
        DeviceNodeDto dto = mapper.toDto(samplePo("on"));
        dto.setState(state);

        assertEquals("Working", mapper.toEntity(dto).getState());
    }

}
