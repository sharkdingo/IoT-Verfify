package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class BoardSemanticFingerprintTest {

    private DeviceVerificationDto device(String varName, String template) {
        DeviceVerificationDto d = new DeviceVerificationDto();
        d.setVarName(varName);
        d.setTemplateName(template);
        return d;
    }

    private SpecificationDto spec(String id, String value) {
        SpecificationDto s = new SpecificationDto();
        s.setId(id);
        s.setTemplateId("1");
        SpecConditionDto c = new SpecConditionDto();
        c.setDeviceLabel("sensor");
        c.setTargetType("variable");
        c.setKey("temperature");
        c.setRelation(">");
        c.setValue(value);
        s.setIfConditions(new java.util.ArrayList<>(List.of(c)));
        return s;
    }

    private Map<String, DeviceSmvData> deviceMap(String varName) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        return Map.of(varName, smv);
    }

    private Map<String, DeviceSmvData> deviceMap(String key, String varName) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        return Map.of(key, smv);
    }

    @Test
    void identicalBoards_produceEqualFingerprint() {
        List<DeviceVerificationDto> devices = List.of(device("sensor", "t1"));
        List<SpecificationDto> specs = List.of(spec("s0", "30"));
        Map<String, DeviceSmvData> map = Map.of();

        assertEquals(
                BoardSemanticFingerprint.of(devices, specs, map),
                BoardSemanticFingerprint.of(devices, specs, map));
    }

    @Test
    void deviceOrder_doesNotAffectFingerprint() {
        List<DeviceVerificationDto> a = List.of(device("sensor", "t1"), device("lamp", "t2"));
        List<DeviceVerificationDto> b = List.of(device("lamp", "t2"), device("sensor", "t1"));
        assertEquals(
                BoardSemanticFingerprint.of(a, List.of(), Map.of()),
                BoardSemanticFingerprint.of(b, List.of(), Map.of()));
    }

    @Test
    void digitLeadingNameNormalization_snapshotMatchesRawBoard() {
        // Snapshot carries the frontend-transformed name (d_1Lamp); the current board read from storage
        // carries the raw label (1Lamp). Both must canonicalize to the same fingerprint.
        List<DeviceVerificationDto> snapshot = List.of(device("d_1Lamp", "t1"));
        List<DeviceVerificationDto> board = List.of(device("1Lamp", "t1"));
        assertEquals(
                BoardSemanticFingerprint.of(snapshot, List.of(), Map.of()),
                BoardSemanticFingerprint.of(board, List.of(), Map.of()));
    }

    @Test
    void quotedNumericValue_matchesUnquoted() {
        // Frontend strips quotes off numeric values before verifying; the fingerprint must treat "30"
        // and 30 as equal so an untouched board is not flagged.
        List<SpecificationDto> quoted = List.of(spec("s0", "\"30\""));
        List<SpecificationDto> unquoted = List.of(spec("s0", "30"));
        assertEquals(
                BoardSemanticFingerprint.of(List.of(), quoted, Map.of()),
                BoardSemanticFingerprint.of(List.of(), unquoted, Map.of()));
    }

    @Test
    void changedSpecValue_changesFingerprint() {
        assertNotEquals(
                BoardSemanticFingerprint.of(List.of(), List.of(spec("s0", "30")), Map.of()),
                BoardSemanticFingerprint.of(List.of(), List.of(spec("s0", "35")), Map.of()));
    }

    @Test
    void specConditionDeviceIdAndLabel_resolveToSameSemanticDevice() {
        SpecificationDto idBacked = spec("s0", "30");
        idBacked.getIfConditions().get(0).setDeviceId("ac_1");
        idBacked.getIfConditions().get(0).setDeviceLabel("LivingRoomAC");

        SpecificationDto labelBacked = spec("s0", "30");
        labelBacked.getIfConditions().get(0).setDeviceId("LivingRoomAC");
        labelBacked.getIfConditions().get(0).setDeviceLabel("LivingRoomAC");

        Map<String, DeviceSmvData> map = deviceMap("LivingRoomAC");
        assertEquals(
                BoardSemanticFingerprint.of(List.of(), List.of(idBacked), map),
                BoardSemanticFingerprint.of(List.of(), List.of(labelBacked), map));
    }

    @Test
    void digitLeadingSpecReference_matchesEvenWhenSmvVarNamesDiffer() {
        SpecificationDto snapshotSpec = spec("s0", "30");
        snapshotSpec.getIfConditions().get(0).setDeviceId("d_1Lamp");
        snapshotSpec.getIfConditions().get(0).setDeviceLabel("d_1Lamp");

        SpecificationDto boardSpec = spec("s0", "30");
        boardSpec.getIfConditions().get(0).setDeviceId("1Lamp");
        boardSpec.getIfConditions().get(0).setDeviceLabel("1Lamp");

        assertEquals(
                BoardSemanticFingerprint.of(
                        List.of(device("d_1Lamp", "t1")),
                        List.of(snapshotSpec),
                        deviceMap("d_1Lamp", "d_1lamp")),
                BoardSemanticFingerprint.of(
                        List.of(device("1Lamp", "t1")),
                        List.of(boardSpec),
                        deviceMap("1Lamp", "_1lamp")));
    }

    @Test
    void addedSpec_changesFingerprint() {
        assertNotEquals(
                BoardSemanticFingerprint.of(List.of(), List.of(spec("s0", "30")), Map.of()),
                BoardSemanticFingerprint.of(List.of(), List.of(spec("s0", "30"), spec("s1", "40")), Map.of()));
    }

    @Test
    void changedDeviceVariable_changesFingerprint() {
        DeviceVerificationDto plain = device("sensor", "t1");
        DeviceVerificationDto edited = device("sensor", "t1");
        edited.setVariables(List.of(new VariableStateDto("threshold", "99", "trusted")));
        assertNotEquals(
                BoardSemanticFingerprint.of(List.of(plain), List.of(), Map.of()),
                BoardSemanticFingerprint.of(List.of(edited), List.of(), Map.of()));
    }

    @Test
    void changedDevicePrivacy_changesFingerprint() {
        DeviceVerificationDto pub = device("sensor", "t1");
        pub.setPrivacies(List.of(new PrivacyStateDto("temperature", "public")));
        DeviceVerificationDto priv = device("sensor", "t1");
        priv.setPrivacies(List.of(new PrivacyStateDto("temperature", "private")));
        assertNotEquals(
                BoardSemanticFingerprint.of(List.of(pub), List.of(), Map.of()),
                BoardSemanticFingerprint.of(List.of(priv), List.of(), Map.of()));
    }

    @Test
    void changedInitialState_changesFingerprint() {
        DeviceVerificationDto off = device("sensor", "t1");
        off.setState("off");
        DeviceVerificationDto on = device("sensor", "t1");
        on.setState("on");
        assertNotEquals(
                BoardSemanticFingerprint.of(List.of(off), List.of(), Map.of()),
                BoardSemanticFingerprint.of(List.of(on), List.of(), Map.of()));
    }

    @Test
    void trustCaseAndDefault_normalized() {
        // Explicit "TRUSTED" must equal the default (no trust set → trusted), so casing/defaulting
        // differences between snapshot and board don't misfire.
        DeviceVerificationDto explicit = device("sensor", "t1");
        explicit.setCurrentStateTrust("TRUSTED");
        DeviceVerificationDto defaulted = device("sensor", "t1");
        assertEquals(
                BoardSemanticFingerprint.of(List.of(explicit), List.of(), Map.of()),
                BoardSemanticFingerprint.of(List.of(defaulted), List.of(), Map.of()));
    }
}
