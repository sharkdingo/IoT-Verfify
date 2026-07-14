package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class DeviceNameNormalizerTest {

    @Test
    void normalize_escapesFullNuSmvReservedWordsUsedByGenerator() {
        assertEquals("_frozenvar", DeviceNameNormalizer.normalize("FROZENVAR"));
        assertEquals("_ctlspec", DeviceNameNormalizer.normalize("CTLSPEC"));
        assertEquals("_compute", DeviceNameNormalizer.normalize("COMPUTE"));
    }

    @Test
    void normalize_keepsRegularDeviceIdsStable() {
        assertEquals("_1lamp", DeviceNameNormalizer.normalize("1Lamp"));
        assertEquals("node_1", DeviceNameNormalizer.normalize("node-1"));
        assertEquals("lamp", DeviceNameNormalizer.normalize("Lamp"));
    }
}
