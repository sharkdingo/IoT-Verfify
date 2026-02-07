package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.data.TemplateWrapper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.Optional;

/**
 * SMV 内容构建器
 * 
 * 职责：
 * 1. 构建设备 SMV 数据映射（buildDeviceSmvMap）
 * 2. 协调各模块生成器组装完整 SMV 内容
 * 3. 生成规格字符串
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class SmvContentBuilder {

    private final ObjectMapper objectMapper;
    private final DeviceTemplateService deviceTemplateService;
    private final SmvDeviceModuleBuilder deviceModuleBuilder;
    private final SmvRulesModuleBuilder rulesModuleBuilder;
    private final SmvMainModuleBuilder mainModuleBuilder;
    private final SmvSpecificationBuilder specBuilder;

    /**
     * 构建完整的 SMV 模型内容
     */
    public String build(Long userId,
                       List<DeviceNodeDto> devices,
                       List<RuleDto> rules,
                       List<SpecificationDto> specs,
                       boolean isAttack,
                       int intensity) {

        log.debug("Building SMV content: {} devices, {} rules, {} specs, attack={}, intensity={}", 
            devices.size(), rules != null ? rules.size() : 0, specs != null ? specs.size() : 0, isAttack, intensity);

        // 1. 准备设备 SMV 数据
        Map<String, TemplateWrapper> templateCache = new HashMap<>();
        Map<String, DeviceSmvData> deviceSmvMap = buildDeviceSmvMap(userId, devices, rules, templateCache);

        // 2. 组装 SMV 内容
        StringBuilder content = new StringBuilder();

        // 2.1 规则注释
        content.append(rulesModuleBuilder.build(rules, deviceSmvMap));

        // 2.2 设备模块（去重）
        Set<String> generatedModules = new HashSet<>();
        int deviceModuleCount = 0;
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv != null) {
                String moduleName = smv.getModuleName();
                if (!generatedModules.contains(moduleName)) {
                    content.append(deviceModuleBuilder.build(smv, isAttack));
                    generatedModules.add(moduleName);
                    deviceModuleCount++;
                }
            }
        }
        log.debug("Generated {} unique device modules", deviceModuleCount);

        // 2.3 main 模块
        content.append(mainModuleBuilder.build(userId, devices, rules, deviceSmvMap, isAttack, intensity));

        // 2.4 规格定义
        content.append(specBuilder.build(specs, isAttack, intensity, deviceSmvMap));

        return content.toString();
    }

    /**
     * 生成规格字符串
     */
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity) {
        return specBuilder.generateSpecString(spec, isAttack, intensity);
    }

    // ==================== 私有数据准备方法 ====================

    /**
     * 构建设备 SMV 数据映射
     */
    private Map<String, DeviceSmvData> buildDeviceSmvMap(Long userId,
                                                          List<DeviceNodeDto> devices,
                                                          List<RuleDto> rules,
                                                          Map<String, TemplateWrapper> templateCache) {
        Map<String, DeviceSmvData> deviceSmvMap = new LinkedHashMap<>();

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = new DeviceSmvData();
            smv.id = device.getId();
            smv.name = device.getTemplateName();
            smv.deviceNo = extractDeviceNo(device.getId());
            smv.currentState = device.getState();
            smv.currentStateTrust = device.getCurrentStateTrust();

            if (device.getVariables() != null) {
                for (DeviceNodeDto.VariableStateDto var : device.getVariables()) {
                    if (var.getName() != null && var.getValue() != null) {
                        smv.variableValues.put(var.getName(), var.getValue());
                    }
                }
            }

            TemplateWrapper template = getTemplateFromCache(templateCache, userId, smv.name);
            if (template == null || template.getManifest() == null) {
                log.warn("Template not found or invalid for device: {}", smv.name);
                continue;
            }

            DeviceManifest manifest = template.getManifest();
            smv.manifest = manifest;

            extractModes(smv, manifest);
            parseCurrentModeStates(smv, device);
            extractStatesAndTrust(smv, manifest);

            if (manifest.getInternalVariables() != null) {
                smv.variables.addAll(manifest.getInternalVariables());
            }

            extractSignalVars(smv, manifest);

            if (manifest.getImpactedVariables() != null) {
                smv.impactedVariables.addAll(manifest.getImpactedVariables());
            }

            extractContents(smv, manifest);
            extractEnvVariables(smv, manifest);

            deviceSmvMap.put(device.getId(), smv);
        }

        processRules(userId, deviceSmvMap, rules, templateCache);

        return deviceSmvMap;
    }

    private TemplateWrapper getTemplateFromCache(Map<String, TemplateWrapper> cache,
                                                   Long userId, String templateName) {
        if (cache.containsKey(templateName)) {
            return cache.get(templateName);
        }

        TemplateWrapper wrapper = new TemplateWrapper();
        try {
            Optional<DeviceTemplatePo> templatePo = deviceTemplateService.findTemplateByName(userId, templateName);
            if (templatePo.isPresent()) {
                wrapper.setTemplatePo(templatePo.get());
                try {
                    wrapper.setManifest(objectMapper.readValue(templatePo.get().getManifestJson(), DeviceManifest.class));
                } catch (Exception e) {
                    log.warn("Failed to parse manifest JSON for template {}: {}", templateName, e.getMessage());
                }
            }
            cache.put(templateName, wrapper);
        } catch (Exception e) {
            log.warn("Failed to load template {}: {}", templateName, e.getMessage());
        }
        return wrapper;
    }

    private void extractModes(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getModes() != null && !manifest.getModes().isEmpty()) {
            smv.modes.addAll(manifest.getModes());
            for (String mode : manifest.getModes()) {
                smv.modeStates.put(mode, new ArrayList<>());
                smv.modeStateTrust.put(mode, "trusted");
            }
        }
    }

    private void parseCurrentModeStates(DeviceSmvData smv, DeviceNodeDto device) {
        if (smv.modes.isEmpty()) {
            return;
        }

        if (smv.currentState != null) {
            String mode = extractTargetMode(smv.currentState);
            if (smv.modes.contains(mode)) {
                smv.currentModeStates.put(mode, smv.currentState);
            }
        }

        if (device.getVariables() != null) {
            for (DeviceNodeDto.VariableStateDto var : device.getVariables()) {
                if (var.getName() != null && var.getValue() != null) {
                    String mode = extractTargetMode(var.getName());
                    if (smv.modes.contains(mode)) {
                        smv.currentModeStates.put(mode, var.getValue());
                    }
                }
            }
        }
    }

    private String extractTargetMode(String stateName) {
        if (stateName == null || stateName.isEmpty()) {
            return "";
        }
        int underscoreIndex = stateName.indexOf('_');
        if (underscoreIndex > 0) {
            return stateName.substring(0, underscoreIndex);
        }
        return "";
    }

    private void extractStatesAndTrust(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getWorkingStates() == null) {
            return;
        }

        for (DeviceManifest.WorkingState ws : manifest.getWorkingStates()) {
            if (ws.getName() == null) continue;
            
            smv.states.add(ws.getName());

            String trust = ws.getTrust() != null ? ws.getTrust() : "trusted";
            smv.stateTrust.put(ws.getName(), trust);

            String mode = extractTargetMode(ws.getName());
            if (!mode.isEmpty() && smv.modes.contains(mode)) {
                smv.modeStates.get(mode).add(ws.getName());
                smv.modeStateTrust.put(mode + "_" + ws.getName(), trust);
            }

            if (ws.getDynamics() != null) {
                Map<String, String> dynamics = new HashMap<>();
                for (DeviceManifest.Dynamic d : ws.getDynamics()) {
                    if (d.getVariableName() != null && d.getValue() != null) {
                        dynamics.put(d.getVariableName(), d.getValue());
                    }
                }
                if (!dynamics.isEmpty()) {
                    smv.stateDynamics.put(ws.getName(), dynamics);
                }
            }
        }
    }

    private void extractSignalVars(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                if (trans.getSignal() != null && trans.getSignal()) {
                    DeviceSmvData.SignalInfo sig = new DeviceSmvData.SignalInfo();
                    sig.setName(trans.getName());
                    sig.setStart(trans.getStartState());
                    sig.setEnd(trans.getEndState());
                    sig.setTrigger(formatTrigger(trans.getTrigger()));
                    smv.signalVars.add(sig);
                }
            }
        }

        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                if (api.getSignal() != null && api.getSignal()) {
                    DeviceSmvData.SignalInfo sig = new DeviceSmvData.SignalInfo();
                    sig.setName(api.getName());
                    sig.setStart(api.getStartState());
                    sig.setEnd(api.getEndState());
                    sig.setTrigger(formatTrigger(api.getTrigger()));
                    sig.setType("api");
                    smv.signalVars.add(sig);
                }
            }
        }
    }

    private void extractContents(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getContents() == null) {
            return;
        }

        for (DeviceManifest.Content c : manifest.getContents()) {
            DeviceSmvData.ContentInfo info = new DeviceSmvData.ContentInfo();
            info.setName(c.getName());
            info.setPrivacy(c.getPrivacy() != null ? c.getPrivacy() : "public");
            info.setIsChangeable(c.getIsChangeable());
            smv.contents.add(info);

            smv.contentPrivacy.put(c.getName(), c.getPrivacy() != null ? c.getPrivacy() : "public");
        }
    }

    private void extractEnvVariables(DeviceSmvData smv, DeviceManifest manifest) {
        if (manifest.getInternalVariables() == null) {
            return;
        }

        for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
            if (iv.getIsInside() == null || !iv.getIsInside()) {
                smv.envVariables.put(iv.getName(), iv);

                if (iv.getValues() != null && !iv.getValues().isEmpty()) {
                    List<String> values = iv.getValues();
                    String maxVal = values.stream().max(String::compareTo).orElse("0");
                    String minVal = values.stream().min(String::compareTo).orElse("0");
                    try {
                        int max = Integer.parseInt(maxVal);
                        int min = Integer.parseInt(minVal);
                        smv.envVariables.get(iv.getName()).setLowerBound(min);
                        smv.envVariables.get(iv.getName()).setUpperBound(max);
                    } catch (NumberFormatException e) {
                        // 非数字类型，跳过
                    }
                }
            }
        }
    }

    private void processRules(Long userId, Map<String, DeviceSmvData> deviceSmvMap,
                             List<RuleDto> rules, Map<String, TemplateWrapper> templateCache) {
        if (rules == null) return;

        for (RuleDto rule : rules) {
            if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
                continue;
            }

            String condition = buildRuleCondition(deviceSmvMap, rule);
            if (condition == null || condition.isEmpty()) continue;

            if (rule.getCommand() == null) continue;

            DeviceSmvData targetSmv = deviceSmvMap.get(rule.getCommand().getDeviceName());
            if (targetSmv == null) continue;

            DeviceSmvData.TransitionInfo trans = createTransitionFromRule(rule, condition, targetSmv, templateCache, userId);
            if (trans != null && trans.state != null && trans.nextState != null) {
                targetSmv.transitions.add(trans);
            }
        }
    }

    private String buildRuleCondition(Map<String, DeviceSmvData> deviceSmvMap, RuleDto rule) {
        StringBuilder conditionBuilder = new StringBuilder();
        
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            return "";
        }
        
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null || condition.getDeviceName() == null || condition.getAttribute() == null) {
                continue;
            }
            
            String sigName = getSignalName(deviceSmvMap, condition.getDeviceName(), condition.getAttribute());
            if (sigName != null) {
                conditionBuilder.append(sigName).append("=TRUE & ");
            } else {
                conditionBuilder.append(condition.getDeviceName()).append(".")
                        .append(condition.getAttribute());
                
                if (condition.getRelation() != null && condition.getValue() != null) {
                    conditionBuilder.append(condition.getRelation()).append(condition.getValue());
                } else {
                    log.warn("Condition has null relation or value: {}", condition);
                }
                conditionBuilder.append(" & ");
            }
        }
        
        if (conditionBuilder.length() > 3) {
            conditionBuilder.setLength(conditionBuilder.length() - 3);
        }
        return conditionBuilder.toString();
    }

    private String getSignalName(Map<String, DeviceSmvData> deviceSmvMap, String deviceId, String attribute) {
        DeviceSmvData smv = deviceSmvMap.get(deviceId);
        if (smv == null) return null;

        for (DeviceSmvData.SignalInfo sig : smv.signalVars) {
            if (attribute != null && attribute.equals(sig.getName())) {
                return sig.getName();
            }
            if (attribute != null && sig.getTrigger() != null &&
                    sig.getTrigger().equalsIgnoreCase(attribute)) {
                return sig.getName();
            }
        }
        return null;
    }

    private DeviceSmvData.TransitionInfo createTransitionFromRule(RuleDto rule, String condition,
                                                   DeviceSmvData targetSmv,
                                                   Map<String, TemplateWrapper> templateCache,
                                                   Long userId) {
        if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
            log.warn("Rule command or action is null");
            return null;
        }
        
        TemplateWrapper template = getTemplateFromCache(templateCache, userId, targetSmv.name);
        if (template == null || template.getManifest() == null) {
            log.warn("Template not found for device: {}", targetSmv.name);
            return null;
        }
        
        DeviceSmvData.TransitionInfo trans = new DeviceSmvData.TransitionInfo();
        trans.ruleNo = rule.getConditions() != null ? rule.getConditions().hashCode() : 0;
        trans.condition = condition;
        
        String action = rule.getCommand().getAction();
        trans.state = getApiStartState(template.getManifest(), action);
        trans.nextState = getApiEndState(template.getManifest(), action);
        trans.transitionName = action;
        trans.nextValue = extractNextValueFromApi(template.getManifest(), action);
        
        if (trans.state == null && trans.nextState == null) {
            log.warn("Both state and nextState are null for action: {}", action);
            return null;
        }
        
        return trans;
    }

    private String getApiStartState(DeviceManifest manifest, String apiName) {
        if (apiName == null || manifest.getApis() == null) return null;

        for (DeviceManifest.API api : manifest.getApis()) {
            if (apiName.equals(api.getName()) && api.getStartState() != null) {
                return api.getStartState();
            }
        }
        return null;
    }

    private String getApiEndState(DeviceManifest manifest, String apiName) {
        if (apiName == null || manifest.getApis() == null) return null;

        for (DeviceManifest.API api : manifest.getApis()) {
            if (apiName.equals(api.getName()) && api.getEndState() != null) {
                return api.getEndState();
            }
        }
        return null;
    }

    private String extractNextValueFromApi(DeviceManifest manifest, String apiName) {
        if (apiName == null || manifest.getApis() == null) return null;

        for (DeviceManifest.API api : manifest.getApis()) {
            if (apiName.equals(api.getName())) {
                if (api.getAssignments() != null && !api.getAssignments().isEmpty()) {
                    return api.getAssignments().get(0).getValue();
                }
            }
        }
        return null;
    }

    private String formatTrigger(DeviceManifest.Trigger trigger) {
        if (trigger == null) return null;
        return trigger.getAttribute() + trigger.getRelation() + trigger.getValue();
    }

    private int extractDeviceNo(String deviceId) {
        if (deviceId == null) return 0;
        String cleaned = deviceId.replaceAll("[^0-9]", "");
        if (cleaned.isEmpty()) return 0;
        try {
            long num = Long.parseLong(cleaned);
            return (int) (num % 1000);
        } catch (NumberFormatException e) {
            return 0;
        }
    }
}
