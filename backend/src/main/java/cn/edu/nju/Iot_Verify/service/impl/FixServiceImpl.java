package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.regex.Pattern;

@Slf4j
@Service
@RequiredArgsConstructor
public class FixServiceImpl implements FixService {

    private static final Pattern PARAM_KEY_PATTERN = Pattern.compile("r\\d+_c\\d+");

    private final TraceRepository traceRepository;
    private final TraceMapper traceMapper;
    private final SmvGenerator smvGenerator;
    private final RuleFixer ruleFixer;
    private final FixConfig fixConfig;
    private final DeviceTemplateRepository deviceTemplateRepository;

    @Override
    @Transactional(readOnly = true)
    public List<FaultRuleDto> localizeFault(Long userId, Long traceId) {
        VerificationContext ctx = loadContext(userId, traceId);
        Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, ctx.request.getDevices());
        return ruleFixer.localizeFaults(ctx.trace.getStates(), ctx.request.getRules(), deviceSmvMap);
    }

    @Override
    @Transactional(readOnly = true)
    public FixResultDto fix(Long userId, Long traceId, List<String> strategies,
                            Map<String, PreferredRange> preferredRanges) {
        validatePreferredRanges(preferredRanges);
        VerificationContext ctx = loadContext(userId, traceId);
        VerificationRequestDto req = ctx.request;
        Map<String, DeviceSmvData> deviceSmvMap = smvGenerator.buildDeviceSmvMap(userId, req.getDevices());

        FixResultDto result = ruleFixer.fix(
                traceId,
                ctx.trace.getViolatedSpecId(),
                ctx.trace.getStates(),
                req.getRules(),
                req.getDevices(),
                req.getSpecs(),
                deviceSmvMap,
                userId,
                req.isAttack(),
                req.getIntensity(),
                req.isEnablePrivacy(),
                strategies,
                fixConfig.getMaxAttempts(),
                preferredRanges
        );

        // Template drift detection: warn if templates were modified after the trace was recorded
        appendDriftWarningIfNeeded(result, userId, req, ctx.trace);

        return result;
    }

    private void appendDriftWarningIfNeeded(FixResultDto result, Long userId,
                                            VerificationRequestDto req, TraceDto trace) {
        if (trace.getCreatedAt() == null) return;

        List<String> templateNames = req.getDevices().stream()
                .map(DeviceVerificationDto::getTemplateName)
                .filter(Objects::nonNull)
                .filter(n -> !n.isBlank())
                // toLowerCase(Locale.ROOT) is safe: template names are restricted to
                // printable ASCII (validated by SAFE_TEMPLATE_NAME in both
                // addDeviceTemplate and initDefaultTemplates)
                .map(n -> n.toLowerCase(Locale.ROOT))
                .distinct()
                .toList();
        if (templateNames.isEmpty()) return;

        try {
            if (deviceTemplateRepository.existsModifiedAfter(userId, templateNames, trace.getCreatedAt())) {
                String warning = "WARNING: Device template(s) were modified after this trace was recorded. "
                        + "Fix suggestions may not match the original verification context.";
                String base = result.getSummary() != null ? result.getSummary() : "";
                result.setSummary(base.isEmpty() ? warning : base + " " + warning);
                log.warn("Template drift detected for trace (createdAt={})", trace.getCreatedAt());
            }
        } catch (Exception e) {
            log.debug("Template drift check failed (non-critical): {}", e.getMessage());
        }
    }

    private void validatePreferredRanges(Map<String, PreferredRange> ranges) {
        if (ranges == null) return;
        for (Map.Entry<String, PreferredRange> entry : ranges.entrySet()) {
            String key = entry.getKey();
            if (key == null) {
                throw new BadRequestException("preferredRanges key must not be null");
            }
            PreferredRange pr = entry.getValue();
            if (!PARAM_KEY_PATTERN.matcher(key).matches()) {
                throw new BadRequestException("Invalid preferredRanges key '" + key
                        + "': must match 'r{ruleIdx}_c{condIdx}' (e.g. 'r0_c1')");
            }
            if (pr == null) {
                throw new BadRequestException("preferredRanges value for '" + key + "' must not be null");
            }
            if (pr.getLower() == null || pr.getUpper() == null) {
                throw new BadRequestException("preferredRanges entry '" + key
                        + "': lower and upper must not be null");
            }
            if (pr.getLower() > pr.getUpper()) {
                throw new BadRequestException("Invalid preferred range for '" + key
                        + "': lower(" + pr.getLower() + ") > upper(" + pr.getUpper() + ")");
            }
        }
    }

    private VerificationContext loadContext(Long userId, Long traceId) {
        TracePo po = traceRepository.findByIdAndUserId(traceId, userId)
                .orElseThrow(() -> new ResourceNotFoundException("Trace", traceId));
        TraceDto trace = traceMapper.toDto(po);

        String requestJson = po.getRequestJson();
        if (requestJson == null || requestJson.isBlank()) {
            throw new BadRequestException(
                    "This trace was created before the fix feature was available. "
                    + "No verification context saved. Please re-run verification to enable fix.");
        }

        VerificationRequestDto request = JsonUtils.fromJson(requestJson, VerificationRequestDto.class);
        if (request == null || request.getDevices() == null || request.getDevices().isEmpty()) {
            throw new BadRequestException("Invalid verification context in trace requestJson.");
        }

        // Note: deviceSmvMap is rebuilt from current templates, not a snapshot.
        // Template drift is detected post-fix via appendDriftWarningIfNeeded().
        log.debug("Loaded verification context for trace {}", traceId);

        return new VerificationContext(trace, request);
    }

    private record VerificationContext(TraceDto trace, VerificationRequestDto request) {}
}
