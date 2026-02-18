package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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

    /**
     * 生成完整的 NuSMV 模型文件并写入临时目录
     */
    public File generate(Long userId, List<DeviceVerificationDto> devices,
                        List<RuleDto> rules, List<SpecificationDto> specs,
                        boolean isAttack, int intensity, boolean enablePrivacy) throws Exception {
        log.info("Generating NuSMV model: userId={}, devices={}, rules={}, specs={}, attack={}, intensity={}, privacy={}",
                userId, devices.size(), rules.size(), specs.size(), isAttack, intensity, enablePrivacy);

        String smvContent = buildSmvContent(userId, devices, rules, specs, isAttack, intensity, enablePrivacy);

        Path tempDir = Files.createTempDirectory("nusmv_");
        File smvFile = tempDir.resolve("model.smv").toFile();

        try (PrintWriter writer = new PrintWriter(new java.io.OutputStreamWriter(
                new java.io.FileOutputStream(smvFile), StandardCharsets.UTF_8))) {
            writer.print(smvContent);
        }

        log.info("Generated NuSMV model file: {}", smvFile.getAbsolutePath());
        return smvFile;
    }

    /**
     * 构建设备 SMV 数据映射（供 trace 解析复用）
     */
    public Map<String, DeviceSmvData> buildDeviceSmvMap(Long userId,
                                                         List<DeviceVerificationDto> devices) {
        return deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);
    }

    // ==================== 内部方法 ====================

    private String buildSmvContent(Long userId,
                                   List<DeviceVerificationDto> devices,
                                   List<RuleDto> rules,
                                   List<SpecificationDto> specs,
                                   boolean isAttack,
                                   int intensity,
                                   boolean enablePrivacy) {

        log.debug("Building SMV content: {} devices, {} rules, {} specs, attack={}, intensity={}, privacy={}",
            devices.size(), rules != null ? rules.size() : 0, specs != null ? specs.size() : 0, isAttack, intensity, enablePrivacy);

        Map<String, DeviceSmvData> deviceSmvMap = deviceSmvDataFactory.buildDeviceSmvMap(userId, devices);

        // 前置校验：P1/P2/P3/P5 — 在生成 SMV 文本前检测模板数据不合法项
        modelValidator.validate(deviceSmvMap);

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
}
