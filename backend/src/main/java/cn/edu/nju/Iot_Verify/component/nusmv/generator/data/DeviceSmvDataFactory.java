package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvModelValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * DeviceSmvData 工厂
 * 职责：从用户输入 + 设备模板构建 DeviceSmvData 映射
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class DeviceSmvDataFactory {

    private final ObjectMapper objectMapper;
    private final DeviceTemplateService deviceTemplateService;
    private final SmvModelValidator modelValidator;

    // ==================== 公共入口 ====================

    public Map<String, DeviceSmvData> buildDeviceSmvMap(Long userId,
                                                        List<DeviceVerificationDto> devices) {
        return buildDeviceSmvMap(userId, devices, new HashMap<>());
    }

    public Map<String, DeviceSmvData> buildDeviceSmvMap(Long userId,
                                                        List<DeviceVerificationDto> devices,
                                                        Map<String, DeviceManifest> templateCache) {
        Map<String, DeviceSmvData> deviceSmvMap = new LinkedHashMap<>();
        List<String> missingTemplateDevices = new ArrayList<>();

        for (DeviceVerificationDto device : devices) {
            if (device == null || device.getVarName() == null || device.getVarName().isBlank()
                    || device.getTemplateName() == null || device.getTemplateName().isBlank()) {
                continue;
            }
            DeviceSmvData smv = new DeviceSmvData();
            smv.setTemplateName(device.getTemplateName());
            smv.setCurrentState(device.getState());
            smv.setInstanceStateTrust(normalizeTrustPrivacy(device.getCurrentStateTrust()));

            if (device.getVariables() != null) {
                for (VariableStateDto var : device.getVariables()) {
                    if (var.getName() != null && var.getValue() != null)
                        smv.getVariableValues().put(var.getName(), var.getValue());
                    if (var.getName() != null && var.getTrust() != null)
                        smv.getInstanceVariableTrust().put(var.getName(), normalizeTrustPrivacy(var.getTrust()));
                }
            }
            if (device.getPrivacies() != null) {
                for (PrivacyStateDto p : device.getPrivacies()) {
                    if (p.getName() != null && p.getPrivacy() != null)
                        smv.getInstanceVariablePrivacy().put(p.getName(), normalizeTrustPrivacy(p.getPrivacy()));
                }
            }

            DeviceManifest manifest = loadManifest(templateCache, userId, smv.getTemplateName());
            if (manifest == null) {
                log.warn("Template not found or invalid for device: {}", smv.getTemplateName());
                missingTemplateDevices.add(device.getVarName() + "(template=" + smv.getTemplateName() + ")");
                continue;
            }
            smv.setManifest(manifest);

            extractModes(smv, manifest);
            extractStatesAndTrust(smv, manifest);
            parseTemplateInitState(smv, manifest);
            parseCurrentModeStates(smv, device);

            if (manifest.getInternalVariables() != null) smv.getVariables().addAll(manifest.getInternalVariables());
            extractSignalVars(smv, manifest);
            if (manifest.getImpactedVariables() != null) smv.getImpactedVariables().addAll(manifest.getImpactedVariables());
            extractEnvVariables(smv, manifest);
            extractContents(smv, manifest);
            computeIdentifiers(smv, device.getVarName());

            // P2-2: 检测归一化后变量名冲突
            for (DeviceSmvData existing : deviceSmvMap.values()) {
                if (smv.getVarName().equals(existing.getVarName())) {
                    throw SmvGenerationException.smvGenerationError(
                            "Variable name collision: '" + device.getVarName()
                            + "' and another device both normalize to '" + smv.getVarName() + "'");
                }
            }

            // 软性校验：委托给 SmvModelValidator（集中管理）
            modelValidator.warnUnknownUserVariables(smv, device);
            modelValidator.warnStatelessDeviceWithState(smv, device);

            deviceSmvMap.put(device.getVarName(), smv);
            // 同时注册清洗后的 varName（如果不同），使规则/规约中用清洗后名称也能查到
            if (!device.getVarName().equals(smv.getVarName())) {
                deviceSmvMap.putIfAbsent(smv.getVarName(), smv);
            }
        }

        if (!missingTemplateDevices.isEmpty()) {
            throw SmvGenerationException.multipleDevicesFailed(String.join(", ", missingTemplateDevices));
        }

        return deviceSmvMap;
    }

    // ==================== 模板加载 ====================

    private DeviceManifest loadManifest(Map<String, DeviceManifest> cache, Long userId, String templateName) {
        if (templateName == null) return null;
        if (cache.containsKey(templateName)) return cache.get(templateName);
        try {
            Optional<DeviceTemplatePo> po = deviceTemplateService.findTemplateByName(userId, templateName);
            if (po.isEmpty()) return null;
            DeviceManifest manifest = objectMapper.readValue(po.get().getManifestJson(), DeviceManifest.class);
            cache.put(templateName, manifest);
            return manifest;
        } catch (BaseException e) {
            throw e;
        } catch (com.fasterxml.jackson.core.JsonProcessingException e) {
            throw SmvGenerationException.manifestParseError(templateName, e);
        } catch (Exception e) {
            throw SmvGenerationException.templateLoadError(templateName, e);
        }
    }

    // ==================== 提取方法 ====================

    private void extractModes(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getModes() != null && !manifest.getModes().isEmpty()) {
            for (String rawMode : manifest.getModes()) {
                String mode = sanitizeSmvToken(rawMode);
                smv.getModes().add(mode);
                smv.getModeStates().put(mode, new ArrayList<>());
            }
        }
    }

    /** 解析模板 InitState 到 templateInitModeStates（在 extractStatesAndTrust 之后调用） */
    private void parseTemplateInitState(DeviceSmvData smv, DeviceManifest manifest) {
        if (smv.getModes().isEmpty() || manifest.getInitState() == null || manifest.getInitState().isBlank()) return;
        String initState = manifest.getInitState();
        if (smv.getModes().size() == 1) {
            String singleMode = smv.getModes().get(0);
            String cleanState = sanitizeSmvToken(initState);
            List<String> modeStateList = smv.getModeStates().get(singleMode);
            if (modeStateList != null && modeStateList.contains(cleanState)) {
                smv.getTemplateInitModeStates().put(singleMode, cleanState);
            }
        } else {
            String[] parts = initState.split(";");
            for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                String mode = smv.getModes().get(i);
                String cleanState = sanitizeSmvToken(parts[i].trim());
                if (cleanState.isEmpty() || cleanState.equals("_")) continue;
                List<String> modeStateList = smv.getModeStates().get(mode);
                if (modeStateList != null && modeStateList.contains(cleanState)) {
                    smv.getTemplateInitModeStates().put(mode, cleanState);
                }
            }
        }
    }

    private void parseCurrentModeStates(DeviceSmvData smv, DeviceVerificationDto device) {
        if (smv.getModes().isEmpty()) return;
        if (smv.getCurrentState() != null) {
            String cleanState = sanitizeSmvToken(smv.getCurrentState());
            if (smv.getModes().size() == 1) {
                String singleMode = smv.getModes().get(0);
                List<String> modeStateList = smv.getModeStates().get(singleMode);
                if (modeStateList != null && modeStateList.contains(cleanState))
                    smv.getCurrentModeStates().put(singleMode, cleanState);
            } else {
                String[] parts = smv.getCurrentState().split(";");
                for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                    String mode = smv.getModes().get(i);
                    String part = sanitizeSmvToken(parts[i].trim());
                    if (!part.isEmpty() && !part.equals("_")) {
                        List<String> modeStateList = smv.getModeStates().get(mode);
                        if (modeStateList != null && modeStateList.contains(part))
                            smv.getCurrentModeStates().put(mode, part);
                    }
                }
            }
        }
        if (device.getVariables() != null) {
            for (VariableStateDto var : device.getVariables()) {
                if (var.getName() != null && var.getValue() != null) {
                    if (smv.getModes().contains(var.getName())) {
                        String cleanVal = sanitizeSmvToken(var.getValue());
                        smv.getCurrentModeStates().put(var.getName(), cleanVal);
                    }
                }
            }
        }
    }

    private void extractStatesAndTrust(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getWorkingStates() == null) return;
        String singleMode = (smv.getModes().size() == 1) ? smv.getModes().get(0) : null;
        for (DeviceManifest.WorkingState ws : manifest.getWorkingStates()) {
            if (ws.getName() == null) continue;
            String cleanName = sanitizeSmvToken(ws.getName());
            smv.getStates().add(cleanName);
            if (singleMode != null) {
                List<String> modeStateList = smv.getModeStates().get(singleMode);
                if (modeStateList != null && !modeStateList.contains(cleanName))
                    modeStateList.add(cleanName);
                String key = singleMode + "_" + cleanName;
                if (ws.getTrust() != null) smv.getModeStateTrust().put(key, normalizeTrustPrivacy(ws.getTrust()));
            } else {
                String[] parts = ws.getName().split(";");
                for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                    String mode = smv.getModes().get(i);
                    String stateName = sanitizeSmvToken(parts[i].trim());
                    List<String> modeStateList = smv.getModeStates().get(mode);
                    if (modeStateList != null && !modeStateList.contains(stateName))
                        modeStateList.add(stateName);
                    String key = mode + "_" + stateName;
                    if (ws.getTrust() != null) smv.getModeStateTrust().put(key, normalizeTrustPrivacy(ws.getTrust()));
                }
            }
        }
    }

    private void extractSignalVars(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                if (trans.getSignal() != null && trans.getSignal()) {
                    DeviceSmvData.SignalInfo sig = new DeviceSmvData.SignalInfo();
                    sig.setName(formatSignalName(trans.getName()));
                    sig.setStart(trans.getStartState());
                    sig.setEnd(trans.getEndState());
                    sig.setTrigger(formatTrigger(trans.getTrigger()));
                    smv.getSignalVars().add(sig);
                }
            }
        }
        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                if (api.getSignal() != null && api.getSignal()) {
                    DeviceSmvData.SignalInfo sig = new DeviceSmvData.SignalInfo();
                    sig.setName(formatApiSignalName(api.getName()));
                    sig.setStart(api.getStartState());
                    sig.setEnd(api.getEndState());
                    sig.setType("api");
                    smv.getSignalVars().add(sig);
                }
            }
        }
    }

    private void extractEnvVariables(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getInternalVariables() == null) return;
        for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
            if (iv.getIsInside() == null || !iv.getIsInside()) {
                smv.getEnvVariables().put(iv.getName(), iv);
            }
        }
    }

    private void extractContents(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getContents() == null) return;
        for (DeviceManifest.Content c : manifest.getContents()) {
            if (c.getName() == null || c.getName().isBlank()) continue;
            DeviceSmvData.ContentInfo info = new DeviceSmvData.ContentInfo();
            info.setName(c.getName());
            info.setPrivacy(normalizeTrustPrivacy(c.getPrivacy() != null ? c.getPrivacy() : "public"));
            info.setChangeable(c.getIsChangeable() != null && c.getIsChangeable());
            smv.getContents().add(info);
        }
    }

    // ==================== NuSMV 保留字 ====================

    /**
     * NuSMV reserved words — identifiers matching these (case-insensitive) must be escaped
     * by prepending '_' to avoid syntax errors in generated SMV models.
     */
    public static final Set<String> NUSMV_RESERVED_WORDS = Set.of(
            "MODULE", "VAR", "IVAR", "FROZENVAR", "DEFINE", "CONSTANTS", "ASSIGN",
            "INIT", "TRANS", "INVAR", "SPEC", "CTLSPEC", "LTLSPEC",
            "FAIRNESS", "COMPASSION", "JUSTICE", "ISA", "FUN", "PRED",
            "MIRROR", "INVARSPEC", "COMPUTE",
            "case", "esac", "next", "init", "self",
            "TRUE", "FALSE", "boolean", "integer", "word", "signed", "unsigned",
            "process", "array", "of", "mod", "union", "in", "xor", "xnor",
            "abs", "max", "min", "count", "toint", "typeof",
            "swconst", "wordconst", "uwconst", "resize", "extend",
            "signed_word", "unsigned_word",
            "EX", "AX", "EF", "AF", "EG", "AG",
            "E", "F", "O", "G", "H", "X", "Y", "Z", "W", "A", "U", "S", "V", "T",
            "BU", "EBF", "ABF", "EBG", "ABG"
    );

    // ==================== 工具方法 ====================

    private String formatTrigger(DeviceManifest.Trigger trigger) {
        if (trigger == null || trigger.getAttribute() == null || trigger.getRelation() == null || trigger.getValue() == null)
            return null;
        return trigger.getAttribute() + trigger.getRelation() + trigger.getValue();
    }

    private void computeIdentifiers(DeviceSmvData smv, String rawVarName) {
        // Use one normalization pipeline for both varName and module suffix
        // so module identity cannot diverge from instance identity.
        String safeId = rawVarName != null ? rawVarName.replaceAll("[^a-zA-Z0-9_]", "_") : "_";
        String result = safeId.toLowerCase();
        if (result.isEmpty() || result.matches("^_+$")) {
            result = "device_0";
        }
        // NuSMV identifiers must not start with a digit
        if (!result.isEmpty() && Character.isDigit(result.charAt(0))) {
            result = "_" + result;
        }
        // Check NuSMV reserved words (same as sanitizeSmvToken)
        if (NUSMV_RESERVED_WORDS.contains(result)
                || NUSMV_RESERVED_WORDS.contains(result.toUpperCase())
                || NUSMV_RESERVED_WORDS.contains(result.toLowerCase())) {
            result = "_" + result;
        }
        smv.setVarName(result);

        // moduleName
        String tplName = smv.getTemplateName() != null ? smv.getTemplateName() : "Device";
        String base = tplName.replaceAll("[^a-zA-Z0-9]", "");
        if (base.isEmpty()) base = "Device";
        // NuSMV identifiers must not start with a digit
        if (Character.isDigit(base.charAt(0))) {
            base = "_" + base;
        }
        // NuSMV reserved-word guard on base
        if (NUSMV_RESERVED_WORDS.contains(base)
                || NUSMV_RESERVED_WORDS.contains(base.toUpperCase())
                || NUSMV_RESERVED_WORDS.contains(base.toLowerCase())) {
            base = "_" + base;
        }
        String suffix = result;
        // NuSMV reserved-word guard on suffix (defense-in-depth, result is already checked)
        if (NUSMV_RESERVED_WORDS.contains(suffix)
                || NUSMV_RESERVED_WORDS.contains(suffix.toUpperCase())
                || NUSMV_RESERVED_WORDS.contains(suffix.toLowerCase())) {
            suffix = "_" + suffix;
        }
        // NuSMV identifiers should not start with a digit.
        if (!suffix.isEmpty() && Character.isDigit(suffix.charAt(0))) {
            suffix = "_" + suffix;
        }
        smv.setModuleName(base + "_" + suffix);

        // sensor
        smv.setSensor(smv.getManifest() != null
                && (smv.getManifest().getApis() == null || smv.getManifest().getApis().isEmpty()));
    }

    public static String formatSignalName(String raw) {
        if (raw == null) return null;
        String cleaned = raw.replaceAll("[^a-zA-Z0-9_]", "_");
        return cleaned.isBlank() ? raw : cleaned;
    }

    public static String formatApiSignalName(String raw) {
        if (raw == null) return null;
        String cleaned = raw.replaceAll("[^a-zA-Z0-9_]", "_");
        if (cleaned.isBlank()) return null;
        return cleaned + "_a";
    }

    /**
     * Defensive sanitization for NuSMV tokens from legacy/bypass data.
     * Removes spaces, replaces non-alphanumeric/underscore chars with '_',
     * prepends '_' if starting with digit.
     */
    static String sanitizeSmvToken(String raw) {
        if (raw == null) return null;
        String s = raw.replace(" ", "").replaceAll("[^a-zA-Z0-9_]", "_");
        if (s.isEmpty()) return "_";
        if (Character.isDigit(s.charAt(0))) s = "_" + s;
        if (NUSMV_RESERVED_WORDS.contains(s)
                || NUSMV_RESERVED_WORDS.contains(s.toUpperCase())
                || NUSMV_RESERVED_WORDS.contains(s.toLowerCase())) s = "_" + s;
        return s;
    }

    /**
     * Normalize trust/privacy values to lowercase for NuSMV enum compatibility.
     * NuSMV enums are defined as {untrusted, trusted} / {private, public} (lowercase).
     */
    public static String normalizeTrustPrivacy(String value) {
        if (value == null) return null;
        return value.trim().toLowerCase();
    }

    // ==================== 静态工具方法（原 SmvUtils，供 builder 使用） ====================

    /** 获取 state 所属的 mode 索引 */
    public static int getModeIndexOfState(DeviceSmvData smv, String state) {
        if (smv == null || smv.getModes() == null || state == null) return -1;
        // 优先：检查 state 是否以 mode 名作为独立词前缀（如 "ThermostatMode_cool"）
        // 使用精确匹配或 mode+"_" 前缀，避免子串误判（如 mode "on" 误匹配 "offline"）
        for (int i = 0; i < smv.getModes().size(); i++) {
            String mode = smv.getModes().get(i);
            if (mode == null || mode.isEmpty()) continue;
            if (state.equals(mode) || state.startsWith(mode + "_")) {
                return i;
            }
        }
        // M3 修复：对分号分隔的 EndState（如 ";cool" 或 "auto;"），找到非空部分的索引
        if (state.contains(";")) {
            String[] parts = state.split(";", -1);
            for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                if (!parts[i].trim().isEmpty()) {
                    return i;
                }
            }
        }
        // 单值 fallback：检查 value 在哪个 mode 的状态列表中
        String cleanState = cleanStateName(state);
        for (int i = 0; i < smv.getModes().size(); i++) {
            List<String> modeStates = smv.getModeStates().get(smv.getModes().get(i));
            if (modeStates != null && modeStates.contains(cleanState)) {
                return i;
            }
        }
        return -1;
    }

    /** 按 varName 或模板名查找设备 SMV 数据 */
    public static DeviceSmvData findDeviceSmvData(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        return findDeviceSmvDataInternal(deviceName, deviceSmvMap, false);
    }

    /** 严格模式：templateName 回退命中多个实例时抛错，避免静默绑定错误设备 */
    public static DeviceSmvData findDeviceSmvDataStrict(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        return findDeviceSmvDataInternal(deviceName, deviceSmvMap, true);
    }

    private static DeviceSmvData findDeviceSmvDataInternal(String deviceName,
                                                           Map<String, DeviceSmvData> deviceSmvMap,
                                                           boolean failOnAmbiguousTemplateMatch) {
        if (deviceName == null || deviceSmvMap == null) return null;
        DeviceSmvData smv = deviceSmvMap.get(deviceName);
        if (smv != null) return smv;

        Set<DeviceSmvData> matches = Collections.newSetFromMap(new IdentityHashMap<>());
        for (DeviceSmvData data : deviceSmvMap.values()) {
            if (deviceName.equals(data.getTemplateName())) {
                matches.add(data);
            }
        }

        if (matches.isEmpty()) {
            return null;
        }
        if (matches.size() == 1) {
            return matches.iterator().next();
        }

        if (failOnAmbiguousTemplateMatch) {
            List<String> candidates = matches.stream()
                    .map(DeviceSmvData::getVarName)
                    .sorted()
                    .toList();
            throw SmvGenerationException.ambiguousDeviceReference(deviceName, candidates);
        }
        return matches.iterator().next();
    }

    /** 清理状态名：移除分号后进行 NuSMV 标识符清洗 */
    public static String cleanStateName(String raw) {
        if (raw == null) return null;
        String cleaned = raw.replace(";", "").trim();
        if (cleaned.isEmpty() || cleaned.equals("_")) return "";
        return sanitizeSmvToken(cleaned);
    }

    /** 按名称查找 API 定义 */
    public static DeviceManifest.API findApi(DeviceManifest manifest, String actionName) {
        if (manifest == null || manifest.getApis() == null || actionName == null) return null;
        for (DeviceManifest.API api : manifest.getApis()) {
            if (actionName.equals(api.getName())) return api;
        }
        return null;
    }

    /** 将任意设备 ID 转为安全变量名 */
    public static String toVarName(String deviceId) {
        if (deviceId == null) return "device";
        String s = deviceId.replaceAll("[^a-zA-Z0-9_]", "_").toLowerCase();
        if (s.isEmpty() || s.matches("^_+$")) return "device";
        if (Character.isDigit(s.charAt(0))) s = "_" + s;
        if (NUSMV_RESERVED_WORDS.contains(s) || NUSMV_RESERVED_WORDS.contains(s.toUpperCase())) s = "_" + s;
        return s;
    }
}
