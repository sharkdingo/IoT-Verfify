package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.fix.ConditionAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class FixServiceImplTest {

    @Mock private TraceRepository traceRepository;
    @Mock private TraceMapper traceMapper;
    @Mock private SmvGenerator smvGenerator;
    @Mock private RuleFixer ruleFixer;
    @Mock private DeviceTemplateRepository deviceTemplateRepository;
    @Mock private BoardStorageService boardStorageService;
    @Mock private BoardDataConverter boardDataConverter;

    private FixServiceImpl fixService;

    @BeforeEach
    void setUp() {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setMaxAttempts(20);
        fixService = new FixServiceImpl(traceRepository, traceMapper, smvGenerator, ruleFixer, fixConfig,
                deviceTemplateRepository, boardStorageService, boardDataConverter);
    }

    /**
     * Stub the spec/device-drift guard's reads so the CURRENT board equals the trace snapshot (no
     * spec/device drift). The snapshot in the apply fixtures has one device {@code sensor}/{@code t1}
     * and no specs, so mirror that. lenient() because tests that reject BEFORE the guard (strategy
     * mismatch, recompute failure) never reach these reads.
     */
    private void stubNoSpecDeviceDrift() {
        DeviceVerificationDto d = new DeviceVerificationDto();
        d.setVarName("sensor");
        d.setTemplateName("t1");
        lenient().when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(d));
        lenient().when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
    }

    /**
     * Stub updateRules to run the mutator against the given current rules inside the "transaction",
     * mirroring the real read→mutate→save. Returns the mutator's output (what would be persisted).
     */
    private void stubUpdateRules(List<RuleDto> currentRules) {
        when(boardStorageService.updateRules(anyLong(), any())).thenAnswer(inv -> {
            java.util.function.UnaryOperator<List<RuleDto>> mutator = inv.getArgument(1);
            return mutator.apply(currentRules);
        });
    }

    private void setupTraceContext() {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));

        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        when(traceMapper.toDto(po)).thenReturn(traceDto);
        when(smvGenerator.buildDeviceSmvMap(anyLong(), anyList())).thenReturn(Map.of());
        when(ruleFixer.fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), any(), anyInt(), any()))
                .thenReturn(FixResultDto.builder().fixable(false).build());
    }

    // ---- P0: strategies passthrough ----

    @Test
    void fix_nullStrategies_passesNullToRuleFixer() {
        setupTraceContext();
        fixService.fix(1L, 1L, null, null);

        @SuppressWarnings("unchecked")
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(ruleFixer).fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), captor.capture(), anyInt(), any());
        assertNull(captor.getValue());
    }

    @Test
    void fix_explicitStrategies_passesToRuleFixer() {
        setupTraceContext();
        fixService.fix(1L, 1L, List.of("disable"), null);

        @SuppressWarnings("unchecked")
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(ruleFixer).fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), captor.capture(), anyInt(), any());
        assertEquals(List.of("disable"), captor.getValue());
    }

    // ---- P3: preferredRanges validation ----

    @Test
    void fix_invalidPreferredRangeKey_throws400() {
        Map<String, PreferredRange> ranges = Map.of("invalid_key", new PreferredRange(10, 20));
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_validPreferredRangeKey_passes() {
        setupTraceContext();
        Map<String, PreferredRange> ranges = Map.of("r0_c1", new PreferredRange(10, 20));
        assertDoesNotThrow(() -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeNullValue_throws400() {
        Map<String, PreferredRange> ranges = new java.util.HashMap<>();
        ranges.put("r0_c0", null);
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeLowerGreaterThanUpper_throws400() {
        Map<String, PreferredRange> ranges = Map.of("r0_c0", new PreferredRange(40, 10));
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeNullLower_throws400() {
        PreferredRange pr = new PreferredRange();
        pr.setUpper(20);
        Map<String, PreferredRange> ranges = Map.of("r0_c0", pr);
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    // ---- Template drift detection ----

    private void setupTraceContextWithCreatedAt(LocalDateTime createdAt, FixResultDto fixResult) {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));

        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        traceDto.setCreatedAt(createdAt);
        when(traceMapper.toDto(po)).thenReturn(traceDto);
        when(smvGenerator.buildDeviceSmvMap(anyLong(), anyList())).thenReturn(Map.of());
        when(ruleFixer.fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), any(), anyInt(), any()))
                .thenReturn(fixResult);
    }

    @Test
    void fix_templateDrift_appendsWarningToSummary() {
        setupTraceContextWithCreatedAt(
                LocalDateTime.of(2025, 1, 1, 0, 0),
                FixResultDto.builder().fixable(false).summary("Original summary.").build());
        when(deviceTemplateRepository.existsModifiedAfter(anyLong(), anyList(), any()))
                .thenReturn(true);

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        assertTrue(result.getSummary().contains("WARNING"));
        assertTrue(result.getSummary().startsWith("Original summary."));
    }

    @Test
    void fix_createdAtNull_skipsDriftCheck() {
        setupTraceContextWithCreatedAt(null,
                FixResultDto.builder().fixable(false).build());

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        verify(deviceTemplateRepository, never()).existsModifiedAfter(anyLong(), anyList(), any());
        assertNotNull(result);
    }

    @Test
    void fix_summaryNull_driftWarningNotCorrupted() {
        setupTraceContextWithCreatedAt(
                LocalDateTime.of(2025, 1, 1, 0, 0),
                FixResultDto.builder().fixable(false).build());
        when(deviceTemplateRepository.existsModifiedAfter(anyLong(), anyList(), any()))
                .thenReturn(true);

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        assertTrue(result.getSummary().startsWith("WARNING"));
        assertFalse(result.getSummary().contains("null"));
    }

    // ---- applyFix ----

    /** Trace snapshot with a single rule: [temperature > 30] -> ac.on. No createdAt (skips drift check). */
    private void setupApplyContextSingleRule() {
        setupApplyContext(null);
    }

    /**
     * Same single-rule snapshot but with a trace createdAt set, so the template-drift check actually
     * queries existsModifiedAfter (which the caller stubs).
     */
    private void setupApplyContextWithTraceCreatedAt() {
        setupApplyContext(LocalDateTime.now());
    }

    private void setupApplyContext(LocalDateTime createdAt) {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"sensor\",\"templateName\":\"t1\"}],"
                + "\"rules\":[{\"conditions\":[{\"deviceName\":\"sensor\",\"attribute\":\"temperature\","
                + "\"relation\":\">\",\"value\":\"30\"}],\"command\":{\"deviceName\":\"sensor\",\"action\":\"on\"},"
                + "\"ruleString\":\"r0\"}],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));

        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        traceDto.setCreatedAt(createdAt);
        when(traceMapper.toDto(po)).thenReturn(traceDto);

        // By default the current board matches the snapshot (no spec/device drift). Tests that exercise
        // drift override these stubs.
        stubNoSpecDeviceDrift();
    }

    private RuleDto boardRuleMatchingSnapshot() {
        return RuleDto.builder()
                .id(42L)
                .conditions(new java.util.ArrayList<>(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor").attribute("temperature").relation(">").value("30").build())))
                .command(RuleDto.Command.builder().deviceName("sensor").action("on").build())
                .ruleString("r0")
                .build();
    }

    private FixSuggestionDto verifiedParameterSuggestion(String newValue) {
        return FixSuggestionDto.builder()
                .strategy("parameter")
                .verified(true)
                .parameterAdjustments(List.of(ParameterAdjustment.builder()
                        .ruleIndex(0).conditionIndex(0).attribute("temperature")
                        .relation(">").originalValue("30").newValue(newValue).build()))
                .build();
    }

    /**
     * Stub the SERVER-side recompute (ruleFixer.fix) that applyFix now runs to independently verify
     * the suggestion. traceId is null in the recompute call, so match with any().
     */
    private void stubServerRecompute(FixSuggestionDto... serverSuggestions) {
        // The recompute builds the device SMV map first, then calls ruleFixer.fix. Stub both here so a
        // test that short-circuits BEFORE the recompute (e.g. template drift) has no unnecessary stubs.
        when(smvGenerator.buildDeviceSmvMap(anyLong(), anyList())).thenReturn(Map.of());
        when(ruleFixer.fix(any(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), anyList(), anyInt(), any()))
                .thenReturn(FixResultDto.builder()
                        .fixable(serverSuggestions.length > 0)
                        .suggestions(List.of(serverSuggestions))
                        .build());
    }

    @Test
    void applyFix_parameter_persistsAdjustedValue() {
        setupApplyContextSingleRule();
        // Server independently recomputes the same verified adjustment.
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // Atomic read→mutate→save: mutator runs against the current 1-rule board.
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "parameter",
                verifiedParameterSuggestion("40"), null);

        assertTrue(result.isApplied());
        // applyFix returns exactly what was persisted (the mutator's output).
        assertEquals("40", result.getRules().get(0).getConditions().get(0).getValue());
        // Original DB id must be preserved so it updates in place.
        assertEquals(42L, result.getRules().get(0).getId());
    }

    @Test
    void applyFix_specDeviceDriftGuardRunsInsideUpdateRulesMutator() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));

        DeviceVerificationDto currentDevice = new DeviceVerificationDto();
        currentDevice.setVarName("sensor");
        currentDevice.setTemplateName("t1");

        AtomicBoolean insideUpdateRules = new AtomicBoolean(false);
        when(boardDataConverter.getDevicesForVerification(1L)).thenAnswer(inv -> {
            assertTrue(insideUpdateRules.get(), "device drift read must run inside updateRules");
            return List.of(currentDevice);
        });
        when(boardStorageService.getSpecs(1L)).thenAnswer(inv -> {
            assertTrue(insideUpdateRules.get(), "spec drift read must run inside updateRules");
            return List.of();
        });
        when(boardStorageService.updateRules(anyLong(), any())).thenAnswer(inv -> {
            java.util.function.UnaryOperator<List<RuleDto>> mutator = inv.getArgument(1);
            insideUpdateRules.set(true);
            try {
                return mutator.apply(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));
            } finally {
                insideUpdateRules.set(false);
            }
        });

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "parameter",
                verifiedParameterSuggestion("40"), null);

        assertTrue(result.isApplied());
        assertEquals("40", result.getRules().get(0).getConditions().get(0).getValue());
    }

    @Test
    void applyFix_clientClaimsVerifiedButServerCannotReproduce_rejected() {
        setupApplyContextSingleRule();
        // Server produces NO verified suggestion -> apply must be refused even though the client
        // marked its suggestion verified=true (client boolean is not trusted).
        stubServerRecompute();

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService, never()).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_clientSuggestionDiffersFromServer_rejected() {
        setupApplyContextSingleRule();
        // Server's verified value is 45, client submitted 40 -> mismatch, reject.
        stubServerRecompute(verifiedParameterSuggestion("45"));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService, never()).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_strategyMismatch_rejected() {
        // strategy != suggestion.strategy is rejected before any recompute.
        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "disable", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService, never()).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_boardDrifted_rejectedAndNotSaved() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // Board now has an extra rule -> count mismatch with the 1-rule snapshot. The drift check runs
        // INSIDE updateRules' mutator, so it must throw there and nothing is persisted.
        stubUpdateRules(new java.util.ArrayList<>(
                List.of(boardRuleMatchingSnapshot(), boardRuleMatchingSnapshot())));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
    }

    @Test
    void applyFix_commandContentChanged_treatedAsDrift() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // Board rule matches the snapshot on conditions + command device/action, but its command now
        // carries privacy content the snapshot lacked. contentDevice/content drive SMV privacy content
        // migration, so this is a real rule change that the fingerprint must catch as drift.
        RuleDto withContent = boardRuleMatchingSnapshot();
        withContent.getCommand().setContent("secret");
        withContent.getCommand().setContentDevice("phone");
        stubUpdateRules(new java.util.ArrayList<>(List.of(withContent)));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
    }

    @Test
    void applyFix_templateDrifted_rejectedAndNotApplied() {
        // A device template was modified after the trace was recorded. applyFix rebuilds the SMV model
        // from current templates, so the recompute would prove/persist a fix against a different model
        // than the one that produced the counterexample. Must reject before touching rules.
        setupApplyContextWithTraceCreatedAt();
        // Template drift is checked BEFORE the recompute, so no recompute stub is needed here.
        when(deviceTemplateRepository.existsModifiedAfter(eq(1L), anyList(), any()))
                .thenReturn(true);

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService, never()).updateRules(anyLong(), any());
        verify(smvGenerator, never()).buildDeviceSmvMap(anyLong(), anyList());
    }

    @Test
    void applyFix_noTemplateDrift_applies() {
        // Same setup with a trace timestamp, but no template changed -> apply proceeds normally.
        setupApplyContextWithTraceCreatedAt();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        when(deviceTemplateRepository.existsModifiedAfter(eq(1L), anyList(), any()))
                .thenReturn(false);
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "parameter",
                verifiedParameterSuggestion("40"), null);

        assertTrue(result.isApplied());
        assertEquals("40", result.getRules().get(0).getConditions().get(0).getValue());
    }

    @Test
    void applyFix_disable_removesFlaggedRule() {
        setupApplyContextSingleRule();
        FixSuggestionDto disable = FixSuggestionDto.builder()
                .strategy("disable").verified(true)
                .disabledRuleIndices(List.of(0))
                .build();
        stubServerRecompute(disable);
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "disable", disable, null);

        assertTrue(result.isApplied());
        assertTrue(result.getRules().isEmpty());
    }

    // ---- spec/device-only drift guard (the recompute replays the stored context, so it cannot see
    //      spec/device edits on its own; the semantic fingerprint must catch them) ----

    @Test
    void applyFix_specConditionAddedAfterVerify_rejectedAndNotSaved() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // The user added a specification to the board after verifying. Rules/templates are unchanged, so
        // the server recompute would still reproduce the verified fix — only the fingerprint catches it.
        cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto spec = new cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_deviceVariableChangedAfterVerify_rejectedAndNotSaved() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // Same device identity/template, but the user edited a device variable value after verifying.
        // The snapshot stored no explicit variables; the current board now carries one → fingerprints differ.
        DeviceVerificationDto edited = new DeviceVerificationDto();
        edited.setVarName("sensor");
        edited.setTemplateName("t1");
        edited.setVariables(List.of(new cn.edu.nju.Iot_Verify.dto.device.VariableStateDto(
                "threshold", "99", "trusted")));
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(edited));
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_currentBoardDeviceModelFailsToBuild_failsClosed() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        // The current board no longer builds a valid device model (e.g. a device's template was deleted).
        // We must fail closed rather than skip the spec/device check. The guard builds the CURRENT map
        // separately from the snapshot map; the current board differs from the snapshot device (sensor),
        // so only the current-board build throws — the snapshot build + recompute still run first.
        DeviceVerificationDto current = new DeviceVerificationDto();
        current.setVarName("brokenDevice");
        current.setTemplateName("goneTemplate");
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(current));
        when(smvGenerator.buildDeviceSmvMap(eq(1L), eq(List.of(current))))
                .thenThrow(new cn.edu.nju.Iot_Verify.exception.BadRequestException("template gone"));
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_currentBoardDeviceModelTemporarilyUnavailable_failsClosedAs503() {
        setupApplyContextSingleRule();
        stubServerRecompute(verifiedParameterSuggestion("40"));
        DeviceVerificationDto current = new DeviceVerificationDto();
        current.setVarName("currentSensor");
        current.setTemplateName("t1");
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(current));
        when(smvGenerator.buildDeviceSmvMap(eq(1L), eq(List.of(current))))
                .thenThrow(SmvGenerationException.templateLoadError(
                        "t1", new RuntimeException("db down")));
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRuleMatchingSnapshot())));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));

        assertTrue(ex.getMessage().contains("retry"));
        verify(boardStorageService).updateRules(anyLong(), any());
    }

    // ---- template-drift fail-closed on apply (a repo error must not let apply proceed) ----

    @Test
    void applyFix_templateDriftCheckThrows_failsClosedAndNotApplied() {
        setupApplyContextWithTraceCreatedAt();
        // The template repository errors, so drift cannot be confirmed. On the apply path this must fail
        // closed (reject) rather than proceed — checked before the recompute, so no recompute stub.
        when(deviceTemplateRepository.existsModifiedAfter(eq(1L), anyList(), any()))
                .thenThrow(new RuntimeException("db down"));

        assertThrows(BadRequestException.class,
                () -> fixService.applyFix(1L, 1L, "parameter", verifiedParameterSuggestion("40"), null));
        verify(boardStorageService, never()).updateRules(anyLong(), any());
    }

    @Test
    void applyFix_digitLeadingLabel_notFalselyRejected() {
        // The snapshot names the device with the frontend transform (1Lamp → d_1Lamp); the persisted
        // board rule carries the raw label (1Lamp). The apply-time rule fingerprint must canonicalize
        // both sides so an untouched board is NOT rejected as drifted.
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d_1Lamp\",\"templateName\":\"t1\"}],"
                + "\"rules\":[{\"conditions\":[{\"deviceName\":\"d_1Lamp\",\"attribute\":\"state\","
                + "\"relation\":\"=\",\"value\":\"on\"}],\"command\":{\"deviceName\":\"d_1Lamp\",\"action\":\"off\"},"
                + "\"ruleString\":\"r0\"}],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));
        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        when(traceMapper.toDto(po)).thenReturn(traceDto);
        // No spec/device drift: current board mirrors the snapshot device (raw label 1Lamp).
        DeviceVerificationDto dev = new DeviceVerificationDto();
        dev.setVarName("1Lamp");
        dev.setTemplateName("t1");
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(dev));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());

        FixSuggestionDto disable = FixSuggestionDto.builder()
                .strategy("disable").verified(true).disabledRuleIndices(List.of(0)).build();
        stubServerRecompute(disable);
        // Persisted board rule uses the RAW digit-leading label.
        RuleDto boardRule = RuleDto.builder()
                .id(7L)
                .conditions(new java.util.ArrayList<>(List.of(RuleDto.Condition.builder()
                        .deviceName("1Lamp").attribute("state").relation("=").value("on").build())))
                .command(RuleDto.Command.builder().deviceName("1Lamp").action("off").build())
                .ruleString("r0")
                .build();
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRule)));

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "disable", disable, null);

        assertTrue(result.isApplied(), "untouched board with a digit-leading label must not be rejected");
    }

    @Test
    void applyFix_conditionAdd_persistsCurrentBoardDeviceLabel() {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d_1Lamp\",\"templateName\":\"t1\"}],"
                + "\"rules\":[{\"conditions\":[{\"deviceName\":\"d_1Lamp\",\"attribute\":\"state\","
                + "\"relation\":\"=\",\"value\":\"on\"}],\"command\":{\"deviceName\":\"d_1Lamp\",\"action\":\"off\"},"
                + "\"ruleString\":\"r0\"}],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));
        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        when(traceMapper.toDto(po)).thenReturn(traceDto);

        DeviceVerificationDto dev = new DeviceVerificationDto();
        dev.setVarName("1Lamp");
        dev.setTemplateName("t1");
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(dev));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());

        FixSuggestionDto addCondition = FixSuggestionDto.builder()
                .strategy("condition")
                .verified(true)
                .conditionAdjustments(List.of(ConditionAdjustment.builder()
                        .ruleIndex(0)
                        .conditionIndex(1)
                        .action("add")
                        .deviceName("d_1Lamp")
                        .attribute("state")
                        .relation("!=")
                        .value("off")
                        .build()))
                .build();
        stubServerRecompute(addCondition);

        RuleDto boardRule = RuleDto.builder()
                .id(7L)
                .conditions(new java.util.ArrayList<>(List.of(RuleDto.Condition.builder()
                        .deviceName("1Lamp").attribute("state").relation("=").value("on").build())))
                .command(RuleDto.Command.builder().deviceName("1Lamp").action("off").build())
                .ruleString("r0")
                .build();
        stubUpdateRules(new java.util.ArrayList<>(List.of(boardRule)));

        FixApplyResultDto result = fixService.applyFix(1L, 1L, "condition", addCondition, null);

        assertTrue(result.isApplied());
        List<RuleDto.Condition> savedConditions = result.getRules().get(0).getConditions();
        assertEquals(2, savedConditions.size());
        assertEquals("1Lamp", savedConditions.get(1).getDeviceName());
    }
}
