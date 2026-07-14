package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class SmvGeneratorTempContextTest {

    private final SmvGenerator generator = new SmvGenerator(null, null, null, null, null, null);

    @Test
    void tempDirectoryPrefixIncludesUserAndExecutionContext() throws Exception {
        assertEquals("nusmv_verify_user_42_sync_",
                resolveTempDirPrefix(SmvGenerator.GeneratePurpose.VERIFICATION, 42L,
                        SmvGenerator.TempModelContext.sync()));
        assertEquals("nusmv_sim_user_42_task_7_",
                resolveTempDirPrefix(SmvGenerator.GeneratePurpose.SIMULATION, 42L,
                        SmvGenerator.TempModelContext.task(7L)));
        assertEquals("nusmv_fix_user_42_trace_99_",
                resolveFixTempDirPrefix(42L, SmvGenerator.TempModelContext.fixTrace(99L)));
    }

    @Test
    void tempDirectoryPrefixSanitizesDiagnosticParts() throws Exception {
        assertEquals("nusmv_verify_user_unknown_task_9_",
                resolveTempDirPrefix(SmvGenerator.GeneratePurpose.VERIFICATION, null,
                        new SmvGenerator.TempModelContext("task #", 9L)));
        assertEquals("nusmv_fix_user_42_trace_repair_",
                resolveFixTempDirPrefix(42L,
                        new SmvGenerator.TempModelContext("trace/repair", null)));
        assertEquals("nusmv_fix_user_unknown_direct_",
                resolveFixTempDirPrefix(null, null));
    }

    @Test
    void capturedDeviceModelFromSnapshotUsesOnlyReferencedManifestWithoutRepositoryFallback() {
        DeviceSmvDataFactory factory = mock(DeviceSmvDataFactory.class);
        SmvGenerator snapshotGenerator = new SmvGenerator(factory, null, null, null, null, null);
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("hall_light");
        device.setTemplateName("Light");
        List<DeviceVerificationDto> devices = List.of(device);
        DeviceManifest light = DeviceManifest.builder().name("Light").build();
        DeviceManifest unused = DeviceManifest.builder().name("Unused").build();
        when(factory.buildDeviceSmvMapFromTemplateSnapshots(
                eq(devices), argThat(manifests -> manifests.keySet().equals(java.util.Set.of("Light")))))
                .thenReturn(Map.of());

        SmvGenerator.CapturedDeviceModel captured =
                snapshotGenerator.captureDeviceModelFromTemplateSnapshots(
                        devices, Map.of("Light", light, "Unused", unused));

        assertEquals(Map.of("Light", light), captured.templateManifests());
        verify(factory).buildDeviceSmvMapFromTemplateSnapshots(
                eq(devices), argThat(manifests -> manifests.keySet().equals(java.util.Set.of("Light"))));
    }

    private String resolveTempDirPrefix(SmvGenerator.GeneratePurpose purpose,
                                        Long userId,
                                        SmvGenerator.TempModelContext tempModelContext) throws Exception {
        Method method = SmvGenerator.class.getDeclaredMethod("resolveTempDirPrefix",
                SmvGenerator.GeneratePurpose.class, Long.class, SmvGenerator.TempModelContext.class);
        method.setAccessible(true);
        return (String) method.invoke(generator, purpose, userId, tempModelContext);
    }

    private String resolveFixTempDirPrefix(Long userId,
                                           SmvGenerator.TempModelContext tempModelContext) throws Exception {
        Method method = SmvGenerator.class.getDeclaredMethod("resolveFixTempDirPrefix",
                Long.class, SmvGenerator.TempModelContext.class);
        method.setAccessible(true);
        return (String) method.invoke(generator, userId, tempModelContext);
    }
}
