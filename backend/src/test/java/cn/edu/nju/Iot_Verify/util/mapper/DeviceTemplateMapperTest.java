package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class DeviceTemplateMapperTest {

    private final DeviceTemplateMapper mapper = new DeviceTemplateMapper();

    @Test
    void databaseNameAndManifestNameMustMatchExactly() {
        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("Light")
                .manifestJson("{\"Name\":\"Lamp\"}")
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("manifestJson", error.getField());
    }

    @Test
    void unknownManifestFieldFailsClosed() {
        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .id(2L)
                .userId(1L)
                .name("Light")
                .manifestJson("{\"Name\":\"Light\",\"InternalModeIndex\":0}")
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("manifestJson", error.getField());
    }

    @Test
    void missingTemplateProvenanceFailsClosed() {
        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .id(3L)
                .userId(1L)
                .name("Light")
                .defaultTemplate(null)
                .manifestJson("{\"Name\":\"Light\"}")
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("defaultTemplate", error.getField());
    }
}
