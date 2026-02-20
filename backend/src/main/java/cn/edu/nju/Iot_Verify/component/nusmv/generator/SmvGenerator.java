package cn.edu.nju.Iot_Verify.component.nusmv.generator;

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

    /**
     * 生成完整的 NuSMV 模型文件并写入临时目录
     */
    public GenerateResult generate(Long userId, List<DeviceVerificationDto> devices,
                         List<RuleDto> rules, List<SpecificationDto> specs,
                         boolean isAttack, int intensity, boolean enablePrivacy) throws Exception {
        List<RuleDto> safeRules = (rules != null) ? rules : List.of();
        log.info("Generating NuSMV model: userId={}, devices={}, rules={}, specs={}, attack={}, intensity={}, privacy={}",
                userId, devices.size(), safeRules.size(), specs.size(), isAttack, intensity, enablePrivacy);

        Map<String, DeviceSmvData> deviceSmvMap = deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);
        String smvContent = buildSmvContent(deviceSmvMap, userId, devices, safeRules, specs, isAttack, intensity, enablePrivacy);

        Path tempDir = Files.createTempDirectory("nusmv_");
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

    // ==================== 内部方法 ====================

    private String buildSmvContent(Map<String, DeviceSmvData> deviceSmvMap,
                                   Long userId,
                                   List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules,
                                   List<SpecificationDto> specs,
                                   boolean isAttack,
                                   int intensity,
                                   boolean enablePrivacy) {

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
                content.append(deviceModuleBuilder.build(smv, isAttack, enablePrivacy));
            }
        }

        content.append(mainModuleBuilder.build(userId, devices, rules, deviceSmvMap, isAttack, intensity, enablePrivacy));
        content.append(specBuilder.build(specs, isAttack, intensity, deviceSmvMap));

        return content.toString();
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
        return conditions.stream().anyMatch(c -> "privacy".equals(c.getTargetType()));
    }
}