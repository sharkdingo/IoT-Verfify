package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
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
import java.util.List;

/**
 * SMV 生成器 - 协调器
 * 职责：协调三层架构的入口
 * 
 * Layer 1: 生成 SMV → SmvContentBuilder
 * Layer 2: 执行 SMV → NusmvExecutor
 * Layer 3: 解析 Trace → SmvTraceParser
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class SmvGenerator {

    private final SmvContentBuilder smvContentBuilder;

    /**
     * 生成完整的 NuSMV 模型文件
     * 
     * @param userId 用户ID，用于查询设备模板
     * @param devices 设备节点列表
     * @param rules 规则列表
     * @param specs 规格列表
     * @param isAttack 是否启用攻击模式
     * @param intensity 攻击强度 (0-10)
     * @return 生成的 SMV 临时文件
     * @throws Exception 生成过程中的异常
     */
    public File generate(Long userId, List<DeviceNodeDto> devices,
                        List<RuleDto> rules, List<SpecificationDto> specs,
                        boolean isAttack, int intensity) throws Exception {
        log.info("Generating NuSMV model: userId={}, devices={}, rules={}, specs={}, attack={}, intensity={}",
                userId, devices.size(), rules.size(), specs.size(), isAttack, intensity);

        String smvContent = smvContentBuilder.build(userId, devices, rules, specs, isAttack, intensity);

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
     * 生成规格字符串预览
     * 
     * @param spec 规格定义
     * @param isAttack 是否启用攻击模式
     * @param intensity 攻击强度
     * @return 规格对应的 NuSMV 语法字符串
     */
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity) {
        return smvContentBuilder.generateSpecString(spec, isAttack, intensity);
    }
}
