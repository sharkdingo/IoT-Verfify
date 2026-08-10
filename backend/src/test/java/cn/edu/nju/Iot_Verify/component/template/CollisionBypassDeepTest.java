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

/**
 * Deep test: verifies that uppercase "A_" prefix is now correctly rejected.
 * Round 11 audit found the guard at line 78 checked startsWith("a_") case-sensitively,
 * allowing "A_temperature" to bypass. Fixed with toLowerCase() check.
 * These tests now verify the bypass is closed.
 */
@ExtendWith(MockitoExtension.class)
public class CollisionBypassDeepTest {

    @Mock
    private SmvGenerator smvGenerator;

    @InjectMocks
    private DeviceTemplateNuSmvValidator validator;

    @Test
    public void testUppercaseA_BypassesEarlyGuard_ButCaughtByLaterCheck() {
        // Round 11: The guard now checks startsWith("a_") with toLowerCase(), so "A_temperature" is rejected

        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("A_temperature");  // Uppercase A - now rejected
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        // After round 11 fix, this should be rejected by the early guard
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));

        assertTrue(ex.getMessage().contains("must not start with 'a_'"));
        assertTrue(ex.getMessage().contains("reserved for environment pool identifiers"));
    }

    @Test
    public void testSharedEnvironmentVariable_UppercaseA_Prefix() {
        // More dangerous: a shared environment variable with "A_" prefix
        // Round 11: now correctly rejected by case-insensitive check

        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("A_temperature");
        iv.setIsInside(false);  // Shared environment
        iv.setTrust("trusted");
        iv.setPrivacy("public");
        iv.setReads(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        iv.setNaturalChangeRate("[-1, 1]");
        manifest.setInternalVariables(List.of(iv));

        // After round 11 fix, this is rejected
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));

        assertTrue(ex.getMessage().contains("must not start with 'a_'"));
    }

    @Test
    public void testReservedWord_MixedCase_Variations() {
        // The guard checks both name and name.toUpperCase()
        // But what about mixed case like "Init" or "iNiT"?
        
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("Init");  // Mixed case
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));

        // validateSmvIdentifier (line 786-788) checks all three: exact, upper, lower
        // So this should be caught
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("reserved word"));
    }

    @Test
    public void testEmptyModeName_InModeList() {
        // Guard 3: what if modes list contains empty string?
        DeviceManifest manifest = new DeviceManifest();
        DeviceManifest.InternalVariable iv = new DeviceManifest.InternalVariable();
        iv.setName("temp");
        iv.setIsInside(true);
        iv.setLowerBound(0);
        iv.setUpperBound(100);
        manifest.setInternalVariables(List.of(iv));
        
        manifest.setModes(List.of("Power", ""));  // Empty mode name
        manifest.setInitState("off");
        
        DeviceManifest.WorkingState ws = new DeviceManifest.WorkingState();
        ws.setName("off;low");
        manifest.setWorkingStates(List.of(ws));

        // Empty string would be added to modeNames set at line 128
        // Then checked against variable names
        // But validateSmvIdentifier should catch empty mode names earlier
        // Actually, modes skip validateSmvIdentifier! They're validated differently at line 193-199
        
        // Line 194: String cleaned = mode == null ? "" : mode.replace(" ", "");
        // Line 195: if (!SAFE_SMV_TOKEN.matcher(cleaned).matches())
        // Empty string does NOT match [a-zA-Z_][a-zA-Z0-9_]*
        
        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateTemplateManifestForNuSmv("Test", manifest));
        assertTrue(ex.getMessage().contains("invalid characters"));
    }
}
