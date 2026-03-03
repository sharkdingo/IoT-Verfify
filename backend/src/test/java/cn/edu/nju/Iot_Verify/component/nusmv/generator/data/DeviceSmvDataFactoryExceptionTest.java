package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvModelValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class DeviceSmvDataFactoryExceptionTest {

    @Mock
    private DeviceTemplateService deviceTemplateService;

    private DeviceSmvDataFactory factory;

    @BeforeEach
    void setUp() {
        factory = new DeviceSmvDataFactory(new ObjectMapper(), deviceTemplateService, new SmvModelValidator());
    }

    @Test
    void buildDeviceSmvMap_invalidManifestJson_throwsManifestParseError() {
        DeviceVerificationDto device = buildDevice("dev_1", "DemoTpl");
        DeviceTemplatePo templatePo = DeviceTemplatePo.builder()
                .id(1L)
                .userId(1L)
                .name("DemoTpl")
                .manifestJson("{invalid-json")
                .build();
        when(deviceTemplateService.findTemplateByName(1L, "DemoTpl"))
                .thenReturn(Optional.of(templatePo));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertEquals("MANIFEST_PARSE_ERROR", ex.getErrorCategory());
        assertTrue(ex.getMessage().contains("DemoTpl"));
    }

    @Test
    void buildDeviceSmvMap_templateLookupFails_throwsTemplateLoadError() {
        DeviceVerificationDto device = buildDevice("dev_1", "DemoTpl");
        when(deviceTemplateService.findTemplateByName(1L, "DemoTpl"))
                .thenThrow(new RuntimeException("db unavailable"));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> factory.buildDeviceSmvMap(1L, List.of(device)));

        assertEquals("TEMPLATE_LOAD_ERROR", ex.getErrorCategory());
        assertTrue(ex.getMessage().contains("DemoTpl"));
    }

    private DeviceVerificationDto buildDevice(String varName, String templateName) {
        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName(varName);
        dto.setTemplateName(templateName);
        return dto;
    }
}
