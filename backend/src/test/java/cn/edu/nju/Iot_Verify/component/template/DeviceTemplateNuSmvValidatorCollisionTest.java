package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

@ExtendWith(MockitoExtension.class)
public class DeviceTemplateNuSmvValidatorCollisionTest {

    @Mock
    private SmvGenerator smvGenerator;

    @InjectMocks
    private DeviceTemplateNuSmvValidator validator;

    // ========== Guard 1: a_ prefix (lines 75-82) ==========

    @Test
    public void testA_Prefix_lowercase_rejected() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("a_temperature");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("must not start with 'a_'"));
    }

    @Test
    public void testA_Prefix_UPPERCASE_bypasses() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("A_temperature");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        // Round 11 fix: now rejected with case-insensitive check
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("must not start with 'a_'"));
    }

    // ========== Guard 2: Reserved word (lines 84-90) ==========

    @Test
    public void testReservedWord_INIT_uppercase_rejected() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("INIT");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("reserved word"));
    }

    @Test
    public void testReservedWord_init_lowercase_rejected() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("init");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("reserved word"));
    }

    // ========== Guard 3: Mode collision (lines 122-141) ==========

    @Test
    public void testModeCollision_exactMatch_rejected() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("Power");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));
        manifest.setModes(List.of("Power", "Fan"));
        manifest.setInitState("off");
        
        DeviceManifest.WorkingState ws = new DeviceManifest.WorkingState();
        ws.setName("off;low");
        manifest.setWorkingStates(List.of(ws));

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("collides with a mode name"));
    }

    @Test
    public void testModeCollision_caseVariation_bypasses() {
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("power");  // lowercase
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));
        manifest.setModes(List.of("Power", "Fan"));  // uppercase P
        manifest.setInitState("off");

        DeviceManifest.WorkingState ws = new DeviceManifest.WorkingState();
        ws.setName("off;low");
        manifest.setWorkingStates(List.of(ws));

        // The early guard at lines 122-141 checks case-insensitively (via generatedToken)
        // So mode "Power" vs variable "power" is detected and rejected
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("collides with mode name"));
    }
}
