package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

/**
 * SMV 生成器
 *
 * 职责：协调数据准备 + 各模块构建器，生成完整 NuSMV 模型文件
 * 同时提供 buildDeviceSmvMap（供 trace 解析复用）和 generateSpecString（预览）
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class SmvGenerator {

    private final DeviceSmvDataFactory deviceSmvDataFactory;
    private final SmvDeviceModuleBuilder deviceModuleBuilder;
    private final SmvRuleCommentWriter ruleCommentWriter;
    private final SmvMainModuleBuilder mainModuleBuilder;
    private final SmvSpecificationBuilder specBuilder;
    private final SmvModelValidator modelValidator;

    /** generate() 的返回值，包含 SMV 文件和构建过程中使用的 deviceSmvMap */
    public record GenerateResult(File smvFile, Map<String, DeviceSmvData> deviceSmvMap) {}

    public enum GeneratePurpose {
        VERIFICATION,
        SIMULATION
    }

    /**
     * 生成完整的 NuSMV 模型文件并写入临时目录
     */
    public GenerateResult generate(Long userId, List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules, List<SpecificationDto> specs,
                                   boolean isAttack, int intensity, boolean enablePrivacy) throws IOException {
        return generate(userId, devices, rules, specs, isAttack, intensity, enablePrivacy, GeneratePurpose.VERIFICATION);
    }

    public GenerateResult generate(Long userId, List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules, List<SpecificationDto> specs,
                                   boolean isAttack, int intensity, boolean enablePrivacy,
                                   GeneratePurpose purpose) throws IOException {
        // 防御性边界：即使绕过 DTO 校验，也确保 intensity 在 NuSMV 合法范围内
        intensity = Math.max(0, Math.min(50, intensity));
        if (devices == null || devices.isEmpty()) {
            throw SmvGenerationException.invalidBuilderInput("SmvGenerator", "devices", "must not be null or empty");
        }
        List<SpecificationDto> safeSpecs = (specs != null) ? specs : List.of();
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
        log.info("Generating NuSMV model: userId={}, devices={}, rules={}, specs={}, attack={}, intensity={}, privacy={}",
                userId, devices.size(), safeRules.size(), safeSpecs.size(), isAttack, intensity, enablePrivacy);

        Map<String, DeviceSmvData> deviceSmvMap = deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);
        String smvContent = buildSmvContent(deviceSmvMap, userId, devices, safeRules, safeSpecs, isAttack, intensity, enablePrivacy);

        Path tempDir = Files.createTempDirectory(resolveTempDirPrefix(purpose));
        File smvFile = tempDir.resolve("model.smv").toFile();

        try (PrintWriter writer = new PrintWriter(new java.io.OutputStreamWriter(
                new java.io.FileOutputStream(smvFile), StandardCharsets.UTF_8))) {
            writer.print(smvContent);
        }

        log.info("Generated NuSMV model file: {}", smvFile.getAbsolutePath());
        return new GenerateResult(smvFile, deviceSmvMap);
    }

    /**
     * 构建设备 SMV 数据映射（供外部直接调用，如无 GenerateResult 可用时）
     */
    public Map<String, DeviceSmvData> buildDeviceSmvMap(Long userId,
                                                         List<DeviceVerificationDto> devices) {
        return deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);
    }

    /**
     * Generate a parameterized SMV model for ActFeedback §5 fix strategies.
     * Uses negated spec and FROZENVAR parameterization for threshold/condition solving.
     */
    public GenerateResult generateParameterized(Long userId, List<DeviceVerificationDto> devices,
                                                 List<RuleDto> rules, List<SpecificationDto> specs,
                                                 boolean isAttack, int intensity, boolean enablePrivacy,
                                                 ParameterizationConfig config) throws IOException {
        intensity = Math.max(0, Math.min(50, intensity));
        if (devices == null || devices.isEmpty()) {
            throw SmvGenerationException.invalidBuilderInput("SmvGenerator", "devices", "must not be null or empty");
        }
        List<SpecificationDto> safeSpecs = (specs != null) ? specs : List.of();
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();

        Map<String, DeviceSmvData> deviceSmvMap = deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);
        String smvContent = buildParameterizedSmvContent(deviceSmvMap, userId, devices, safeRules, safeSpecs,
                isAttack, intensity, enablePrivacy, config);

        Path tempDir = Files.createTempDirectory("nusmv_fix_");
        File smvFile = tempDir.resolve("model.smv").toFile();

        try (PrintWriter writer = new PrintWriter(new java.io.OutputStreamWriter(
                new java.io.FileOutputStream(smvFile), StandardCharsets.UTF_8))) {
            writer.print(smvContent);
        }

        log.info("Generated parameterized NuSMV model: {}", smvFile.getAbsolutePath());
        return new GenerateResult(smvFile, deviceSmvMap);
    }

    // ==================== 内部方法 ====================

    private String buildSmvContent(Map<String, DeviceSmvData> deviceSmvMap,
                                   Long userId,
                                   List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules,
                                   List<SpecificationDto> specs,
                                   boolean isAttack,
                                   int intensity,
                                   boolean enablePrivacy) {
        return buildSmvContentInternal(deviceSmvMap, userId, devices, rules, specs,
                isAttack, intensity, enablePrivacy, null);
    }

    private String buildParameterizedSmvContent(Map<String, DeviceSmvData> deviceSmvMap,
                                                Long userId,
                                                List<DeviceVerificationDto> devices,
                                                List<RuleDto> rules,
                                                List<SpecificationDto> specs,
                                                boolean isAttack,
                                                int intensity,
                                                boolean enablePrivacy,
                                                ParameterizationConfig config) {
        return buildSmvContentInternal(deviceSmvMap, userId, devices, rules, specs,
                isAttack, intensity, enablePrivacy, config);
    }

    private String buildSmvContentInternal(Map<String, DeviceSmvData> deviceSmvMap,
                                           Long userId,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           List<SpecificationDto> specs,
                                           boolean isAttack,
                                           int intensity,
                                           boolean enablePrivacy,
                                           ParameterizationConfig config) {

        log.debug("Building SMV content: {} devices, {} rules, {} specs, attack={}, intensity={}, privacy={}",
            devices.size(), rules != null ? rules.size() : 0, specs != null ? specs.size() : 0, isAttack, intensity, enablePrivacy);

        // 前置校验：P1/P2/P3/P5 — 在生成 SMV 文本前检测模板数据不合法项
        modelValidator.validate(deviceSmvMap);

        // 前置校验：隐私规约需要 enablePrivacy=true
        if (!enablePrivacy && specs != null) {
            validateNoPrivacySpecs(specs);
        }

        StringBuilder content = new StringBuilder();

        content.append(ruleCommentWriter.build(rules));

        Set<String> generatedModules = new HashSet<>();
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv != null && generatedModules.add(smv.getModuleName())) {
                content.append(deviceModuleBuilder.build(smv, isAttack, intensity, enablePrivacy));
            }
        }

        content.append(config != null
                ? mainModuleBuilder.buildParameterized(userId, devices, rules, deviceSmvMap, isAttack, intensity, enablePrivacy, config)
                : mainModuleBuilder.build(userId, devices, rules, deviceSmvMap, isAttack, intensity, enablePrivacy));

        if (config != null) {
            // Only emit the negated spec (¬ρ)
            content.append(specBuilder.buildNegated(specs, config.getNegatedSpecIndex(),
                    isAttack, intensity, deviceSmvMap, enablePrivacy));
        } else {
            content.append(specBuilder.build(specs, isAttack, intensity, deviceSmvMap, enablePrivacy));
        }

        return content.toString();
    }

    private String resolveTempDirPrefix(GeneratePurpose purpose) {
        if (purpose == GeneratePurpose.SIMULATION) {
            return "nusmv_sim_";
        }
        return "nusmv_verify_";
    }

    /**
     * 校验：当 enablePrivacy=false 时，规约中不得包含 targetType="privacy" 的条件。
     * 否则 SmvSpecificationBuilder 会生成 privacy_* 变量引用，但这些变量未被声明，
     * 导致 NuSMV 运行时报 undefined variable 错误。
     */
    private void validateNoPrivacySpecs(List<SpecificationDto> specs) {
        for (SpecificationDto spec : specs) {
            if (spec == null) continue;
            if (hasPrivacyCondition(spec.getAConditions())
                    || hasPrivacyCondition(spec.getIfConditions())
                    || hasPrivacyCondition(spec.getThenConditions())) {
                throw SmvGenerationException.privacySpecWithoutPrivacyEnabled(spec.getId());
            }
        }
    }

    private boolean hasPrivacyCondition(List<SpecConditionDto> conditions) {
        if (conditions == null) return false;
        return conditions.stream().anyMatch(c ->
                c != null && c.getTargetType() != null
                        && "privacy".equalsIgnoreCase(c.getTargetType().trim()));
    }
}
