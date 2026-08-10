package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test the concrete collision scenario after round 11 fix.
 * Round 11 audit found that the guard checked startsWith("a_") case-sensitively,
 * allowing "A_temperature" to bypass. The fix now uses toLowerCase() before checking.
 *
 * The collision occurs because:
 * - Generator creates pool identifier "a_<name>"
 * - Registration normalizes to lowercase: "a_A_temperature" becomes "a_a_temperature"
 * - Another device's "temperature" pool is also "a_temperature", which after the first device's
 *   registration becomes impossible to register (collision detected)
 *
 * After round 11, both "a_temperature" and "A_temperature" are rejected at admission.
 */
@ExtendWith(MockitoExtension.class)
public class UppercaseAPrefixCollisionTest {

    @Mock
    private SmvGenerator smvGenerator;

    @InjectMocks
    private DeviceTemplateNuSmvValidator validator;

    @Test
    public void testScenario_A_temperature_vs_temperature_pool() {
        // Device 1 template has variable "A_temperature"
        // Round 11 audit found this bypassed the guard (case-sensitive startsWith("a_"))
        // But the collision was real: generator creates "a_A_temperature", registration
        // normalizes to lowercase "a_a_temperature", which collides with another device's
        // "a_temperature" pool identifier.

        // After round 11 fix: now rejected by case-insensitive check

        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("A_temperature");
        iv.setIsInside(false);
        iv.setTrust("trusted");
        iv.setPrivacy("public");
        iv.setReads(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        iv.setNaturalChangeRate("[-1, 1]");
        manifest.setInternalVariables(List.of(iv));

        // After round 11: this is rejected
        cn.edu.nju.Iot_Verify.exception.BadRequestException ex =
                assertThrows(cn.edu.nju.Iot_Verify.exception.BadRequestException.class,
                        () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("must not start with 'a_'"));
    }

    @Test
    public void testActualCollisionScenario_lowercase_a_prefix() {
        // This is what the guard is supposed to catch:
        // User declares "a_temperature", generator would create "a_a_temperature"
        // Another device has "a_temperature", generator creates pool "a_a_temperature"
        // COLLISION!
        
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("a_temperature");
        iv.setIsInside(false);
        iv.setTrust("trusted");
        iv.setPrivacy("public");
        iv.setReads(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        iv.setNaturalChangeRate("[-1, 1]");
        manifest.setInternalVariables(List.of(iv));

        // This should be rejected
        assertThrows(Exception.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
    }
}
