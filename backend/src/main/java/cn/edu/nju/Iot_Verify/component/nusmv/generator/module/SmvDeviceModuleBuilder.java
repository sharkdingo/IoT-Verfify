package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.PropertyDimension;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * SMV 设备模块构建器
 * 职责：构建单个设备的 NuSMV 模块定义
 */
@Slf4j
@Component
public class SmvDeviceModuleBuilder {

    private static final String NUSMV_FALSE = "FALSE";
    private static final String DEFAULT_PRIVACY = "public";
    private static final String DEFAULT_TRUST = "trusted";


    public String build(DeviceSmvData smv, boolean isAttack, boolean enablePrivacy) {
        // 参数验证
        if (smv == null) {
            log.error("SmvDeviceModuleBuilder.build: smv 参数不能为 null");
            throw new IllegalArgumentException("smv 参数不能为 null");
        }
        if (smv.getModuleName() == null || smv.getModuleName().isEmpty()) {
            log.error("SmvDeviceModuleBuilder.build: smv.moduleName 为空");
            throw new IllegalArgumentException("设备模块名称不能为空");
        }

        StringBuilder content = new StringBuilder();
        String moduleName = smv.getModuleName();

        content.append("\nMODULE ").append(moduleName);

        // 检查 manifest 是否为 null
        if (smv.getManifest() == null) {
            log.warn("SmvDeviceModuleBuilder.build: smv.manifest 为 null，将视为传感器设备");
            smv.setManifest(new DeviceManifest());
        }

        boolean isSensor = smv.isSensor();

        // FROZENVAR for sensors (attack mode + variable trust/privacy)
        appendFrozenVarSection(content, smv, isAttack, isSensor, enablePrivacy);

        appendVariables(content, smv, isSensor, isAttack, enablePrivacy);
        appendAssignments(content, smv, isAttack, isSensor, enablePrivacy);

        return content.toString();
    }

    private void appendFrozenVarSection(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor, boolean enablePrivacy) {
        boolean hasFrozenVar = false;
        StringBuilder frozenVars = new StringBuilder();

        if (isAttack) {
            frozenVars.append("\n\tis_attack: boolean;");
            hasFrozenVar = true;
        }

        if (isSensor) {
            for (DeviceManifest.InternalVariable var : smv.getVariables()) {
                frozenVars.append("\n\ttrust_").append(var.getName()).append(": {trusted, untrusted};");
                if (enablePrivacy) {
                    frozenVars.append("\n\tprivacy_").append(var.getName()).append(": {public, private};");
                }
                hasFrozenVar = true;
            }
        }

        // IsChangeable=false 的 content → FROZENVAR（隐私不可变）
        if (enablePrivacy) {
            for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
                if (!ci.isChangeable()) {
                    frozenVars.append("\n\tprivacy_").append(ci.getName()).append(": {public, private};");
                    hasFrozenVar = true;
                }
            }
        }

        if (hasFrozenVar) {
            content.append("\nFROZENVAR").append(frozenVars);
        }
    }

    private void appendVariables(StringBuilder content, DeviceSmvData smv, boolean isSensor, boolean isAttack, boolean enablePrivacy) {
        content.append("\nVAR\n");

        appendModeVariables(content, smv);
        appendInternalVariables(content, smv, isAttack);
        appendSignalVariables(content, smv);
        appendVariableRates(content, smv);
        if (!isSensor) {
            appendPropertyVariables(content, smv, PropertyDimension.TRUST);
            if (enablePrivacy) {
                appendPropertyVariables(content, smv, PropertyDimension.PRIVACY);
            }
        }
        // IsChangeable=true 的 content → VAR（隐私可被规则修改）
        if (enablePrivacy) {
            for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
                if (ci.isChangeable()) {
                    content.append("\n\tprivacy_").append(ci.getName()).append(": {public, private};");
                }
            }
        }
    }

    private void appendAssignments(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor, boolean enablePrivacy) {
        content.append("\nASSIGN\n");

        appendInitialValues(content, smv, isSensor);

        if (isAttack) {
            content.append("\n\tinit(is_attack) := {TRUE, FALSE};");
        }

        appendInitialProperty(content, smv, isAttack, isSensor, PropertyDimension.TRUST);
        if (enablePrivacy) {
            appendInitialProperty(content, smv, isAttack, isSensor, PropertyDimension.PRIVACY);
        }

        // content 隐私初始化
        if (enablePrivacy) {
            for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
                content.append("\n\tinit(privacy_").append(ci.getName()).append(") := ").append(ci.getPrivacy()).append(";");
            }
        }
    }

    private void appendModeVariables(StringBuilder content, DeviceSmvData smv) {
        if (smv.getModes().isEmpty()) {
            // 无模式设备（纯传感器）：不声明 state 变量
        } else {
            // 单模式和多模式统一处理：用模式名作为变量名
            for (String mode : smv.getModes()) {
                List<String> modeStateList = smv.getModeStates().get(mode);
                if (modeStateList != null && !modeStateList.isEmpty()) {
                    content.append("\t").append(mode).append(": {").append(String.join(", ", modeStateList)).append("};");
                }
            }
        }
    }

    private void appendInternalVariables(StringBuilder content, DeviceSmvData smv, boolean isAttack) {
        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            String varDef;
            if (var.getValues() != null && !var.getValues().isEmpty()) {
                // 去除空格，与 sample.smv 一致（如 "not authorized" → "notauthorized"）
                List<String> cleanValues = new ArrayList<>();
                for (String v : var.getValues()) {
                    cleanValues.add(v.replace(" ", ""));
                }
                varDef = "{" + String.join(", ", cleanValues) + "}";
            } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                int lower = var.getLowerBound();
                int upper = var.getUpperBound();
                // 攻击模式下扩大传感器数值范围，模拟数据篡改攻击
                // 参考 MEDIC-test SMVGeneration.java outModule() 中被注释的 upperBound+40 逻辑
                if (isAttack && smv.isSensor()) {
                    int range = upper - lower;
                    int expansion = Math.max(10, range / 5); // 扩大20%，最少扩大10
                    upper = upper + expansion;
                }
                varDef = lower + ".." + upper;
            } else {
                varDef = "boolean";
            }
            content.append("\n\t").append(var.getName()).append(": ").append(varDef).append(";");
        }
    }

    private void appendSignalVariables(StringBuilder content, DeviceSmvData smv) {
        for (DeviceSmvData.SignalInfo sig : smv.getSignalVars()) {
            content.append("\n\t").append(sig.getName()).append(": boolean;");
        }
    }

    private void appendVariableRates(StringBuilder content, DeviceSmvData smv) {
        for (String varName : smv.getImpactedVariables()) {
            // 枚举型变量不需要 _rate（用 Dynamics.Value 直接赋值）
            if (isEnumVariable(smv, varName)) continue;
            content.append("\n\t").append(varName).append("_rate: -10..10;");
        }
    }

    private void appendPropertyVariables(StringBuilder content, DeviceSmvData smv, PropertyDimension dim) {
        String domain = (dim == PropertyDimension.TRUST) ? "{untrusted, trusted}" : "{private, public}";
        for (String mode : smv.getModes()) {
            List<String> states = smv.getModeStates().get(mode);
            if (states == null) continue;
            for (String state : states) {
                content.append("\n\t").append(dim.prefix).append(mode).append("_").append(state)
                       .append(": ").append(domain).append(";");
            }
        }
        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            content.append("\n\t").append(dim.prefix).append(var.getName())
                   .append(": ").append(domain).append(";");
        }
    }

    private void appendInitialProperty(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor,
                                       PropertyDimension dim) {
        String defaultVal = (dim == PropertyDimension.TRUST) ? DEFAULT_TRUST : DEFAULT_PRIVACY;

        // 状态级 trust/privacy 初始化
        Set<String> initialized = new HashSet<>();
        for (String mode : smv.getModes()) {
            List<String> states = smv.getModeStates().get(mode);
            if (states == null) continue;

            // Bug1 修复：确定当前状态
            String currentState = smv.getCurrentModeStates().get(mode);
            if (currentState == null && smv.getCurrentState() != null) {
                // H1 修复：多模式设备 fallback 时解析分号分隔的状态
                int modeIdx = smv.getModes().indexOf(mode);
                String[] stateParts = smv.getCurrentState().replace(" ", "").split(";");
                if (modeIdx >= 0 && modeIdx < stateParts.length && !stateParts[modeIdx].isEmpty()) {
                    currentState = stateParts[modeIdx];
                }
            }

            for (String state : states) {
                String key = mode + "_" + state;
                if (!initialized.add(key)) continue;

                String value;
                if (dim == PropertyDimension.TRUST) {
                    // Bug1 修复：instanceStateTrust 仅应用于当前状态
                    boolean isCurrentState = state.equals(currentState);
                    String instanceOverride = isCurrentState ? smv.getInstanceStateTrust() : null;
                    value = instanceOverride != null ? instanceOverride
                            : smv.getModeStateTrust().getOrDefault(key, defaultVal);
                } else {
                    // P1 修复：先按 mode_state 格式查找，再按裸状态名查找
                    String instanceOverride = smv.getInstanceVariablePrivacy().get(key);
                    if (instanceOverride == null) {
                        instanceOverride = smv.getInstanceVariablePrivacy().get(state);
                    }
                    value = instanceOverride != null ? instanceOverride : resolveManifestPrivacy(smv, mode, state, defaultVal);
                }

                content.append("\n\tinit(").append(dim.prefix).append(mode).append("_").append(state)
                       .append(") := ").append(value).append(";");
            }
        }

        // 内部变量级 trust/privacy 初始化
        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            String value;
            if (dim == PropertyDimension.TRUST) {
                String instanceVarTrust = smv.getInstanceVariableTrust().get(var.getName());
                value = instanceVarTrust != null ? instanceVarTrust : (var.getTrust() != null ? var.getTrust() : defaultVal);
                if (isAttack && isSensor) {
                    content.append("\n\tinit(trust_").append(var.getName()).append(") :=\n");
                    content.append("\tcase\n");
                    content.append("\t\tis_attack=TRUE: untrusted;\n");
                    content.append("\t\tTRUE: ").append(value).append(";\n");
                    content.append("\tesac;");
                    continue;
                }
            } else {
                String instanceVarPrivacy = smv.getInstanceVariablePrivacy().get(var.getName());
                value = instanceVarPrivacy != null ? instanceVarPrivacy : (var.getPrivacy() != null ? var.getPrivacy() : defaultVal);
            }
            content.append("\n\tinit(").append(dim.prefix).append(var.getName()).append(") := ").append(value).append(";");
        }
    }

    /** 从 manifest WorkingState 解析 privacy 默认值（支持多模式复合状态名） */
    private String resolveManifestPrivacy(DeviceSmvData smv, String mode, String state, String defaultVal) {
        if (smv.getManifest() != null && smv.getManifest().getWorkingStates() != null) {
            int modeIdx = smv.getModes().indexOf(mode);
            for (DeviceManifest.WorkingState ws : smv.getManifest().getWorkingStates()) {
                if (ws.getName() == null) continue;
                String wsName = ws.getName().replace(" ", "");
                // 单模式或非复合名：直接匹配
                if (!wsName.contains(";")) {
                    if (state.equals(wsName)) {
                        return ws.getPrivacy() != null ? ws.getPrivacy() : defaultVal;
                    }
                } else {
                    // 多模式复合名（如 "on;locked"）：按分号拆分，匹配对应 mode 索引的段
                    String[] parts = wsName.split(";", -1);
                    if (modeIdx >= 0 && modeIdx < parts.length && state.equals(parts[modeIdx].trim())) {
                        return ws.getPrivacy() != null ? ws.getPrivacy() : defaultVal;
                    }
                }
            }
        }
        return defaultVal;
    }

    private void appendInitialValues(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        // 优先级：用户输入 > 模板 InitState > 非确定性
        for (String mode : smv.getModes()) {
            List<String> modeStateList = smv.getModeStates().get(mode);
            if (modeStateList == null || modeStateList.isEmpty()) continue;

            // 优先使用用户指定的当前模式状态
            String userState = smv.getCurrentModeStates().get(mode);
            if (userState == null && smv.getCurrentState() != null) {
                // M5 修复：currentState 需要去空格后再匹配
                String cleanCurrentState = smv.getCurrentState().replace(" ", "");
                if (modeStateList.contains(cleanCurrentState)) {
                    userState = cleanCurrentState;
                }
            }

            if (userState != null && modeStateList.contains(userState)) {
                content.append("\n\tinit(").append(mode).append(") := ").append(userState).append(";");
            } else {
                // fallback: 模板 InitState
                String templateState = smv.getTemplateInitModeStates().get(mode);
                if (templateState != null && modeStateList.contains(templateState)) {
                    content.append("\n\tinit(").append(mode).append(") := ").append(templateState).append(";");
                } else {
                    // 最终 fallback: 非确定性初始状态
                    content.append("\n\tinit(").append(mode).append(") := {")
                           .append(String.join(", ", modeStateList)).append("};");
                }
            }
        }

        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            if (var.getIsInside() == null || !var.getIsInside()) {
                // 外部变量由主模块的 appendSensorEnvAssignments 用简单赋值处理，
                // 不能同时有 init() 和简单赋值
                continue;
            }
            if (var.getValues() != null && !var.getValues().isEmpty()) {
                String rawInit = smv.getVariableValues().getOrDefault(var.getName(), var.getValues().get(0));
                String initValue = rawInit.replace(" ", "");
                content.append("\n\tinit(").append(var.getName()).append(") := ").append(initValue).append(";");
            } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                String initValue = smv.getVariableValues().getOrDefault(var.getName(), String.valueOf(var.getLowerBound()));
                content.append("\n\tinit(").append(var.getName()).append(") := ").append(initValue).append(";");
            }
        }

        for (DeviceSmvData.SignalInfo sig : smv.getSignalVars()) {
            content.append("\n\tinit(").append(sig.getName()).append(") := ").append(NUSMV_FALSE).append(";");
        }

        for (String varName : smv.getImpactedVariables()) {
            if (isEnumVariable(smv, varName)) continue;
            content.append("\n\tinit(").append(varName).append("_rate) := 0;");
        }
    }

    private boolean isEnumVariable(DeviceSmvData smv, String varName) {
        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            if (var.getName().equals(varName) && var.getValues() != null && !var.getValues().isEmpty()) {
                return true;
            }
        }
        return false;
    }

}