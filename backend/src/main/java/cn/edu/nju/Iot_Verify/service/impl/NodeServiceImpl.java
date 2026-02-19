package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.LevenshteinDistanceUtil;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

@Slf4j
@Service
@RequiredArgsConstructor
public class NodeServiceImpl implements NodeService {

    private final DeviceNodeRepository nodeRepo;
    private final DeviceTemplateService deviceTemplateService;
    private final ObjectMapper objectMapper;

    // 硬编码回退状态
    private static final String HARD_FALLBACK_STATE = "Working";
    
    // 默认位置和尺寸常量
    private static final double DEFAULT_POSITION_X = 250.0;
    private static final double DEFAULT_POSITION_Y = 250.0;
    private static final int DEFAULT_WIDTH = 110;
    private static final int DEFAULT_HEIGHT = 90;
    
    // ID 生成相关常量
    private static final int RANDOM_ID_RANGE = 1000;
    private static final int MAX_RETRY_COUNT = 10;
    private static final int UUID_SUFFIX_LENGTH = 6;

    @Override
    public String searchNodes(Long userId, String keyword) {
        List<DeviceNodePo> results;

        if (keyword == null || keyword.trim().isEmpty() || keyword.equalsIgnoreCase("所有设备")) {
            results = nodeRepo.findByUserId(userId);
        } else {
            results = nodeRepo.findByUserIdAndTemplateNameContainingIgnoreCaseOrLabelContainingIgnoreCase(
                    userId, keyword, keyword);
        }

        try {
            if (results.isEmpty()) {
                return "未找到匹配 '" + keyword + "' 的设备。";
            }
            return objectMapper.writeValueAsString(results);
        } catch (JsonProcessingException e) {
            log.error("序列化搜索结果失败", e);
            return "[]";
        }
    }

    @Override
    @Transactional
    public String addNode(Long userId, String reqTemplate, String label, Double x, Double y, String state, Integer w, Integer h) {

        String rawTemplate = reqTemplate != null ? reqTemplate.trim() : "";
        String finalTemplate = rawTemplate;
        StringBuilder resultMsg = new StringBuilder();

        if (!deviceTemplateService.checkTemplateExists(userId, rawTemplate)) {
            List<String> allTemplates = deviceTemplateService.getAllTemplateNames(userId);
            log.info("User requested template: [{}], Available templates in DB: {}", rawTemplate, allTemplates);

            String bestMatch = findBestMatch(rawTemplate, allTemplates);

            if (bestMatch != null) {
                finalTemplate = bestMatch;
                String normRaw = rawTemplate.replace(" ", "").toLowerCase();
                String normMatch = bestMatch.replace(" ", "").toLowerCase();

                if (!normRaw.equals(normMatch)) {
                    resultMsg.append(String.format("【系统提示】库中未找到 '%s'，已为您自动匹配最接近的模板 '%s'。", rawTemplate, finalTemplate));
                } else {
                    log.info("Template name auto-corrected: {} -> {}", rawTemplate, finalTemplate);
                }
            } else {
                String fallbackTemplate = chooseFallbackTemplate(allTemplates);
                if (fallbackTemplate == null) {
                    return String.format("创建失败：无法识别模板 '%s'，且当前账户没有可用模板。请先上传设备模板。", rawTemplate);
                }
                finalTemplate = fallbackTemplate;
                resultMsg.append(String.format("【系统提示】无法识别模板 '%s'，已使用兜底模板 '%s'。", rawTemplate, finalTemplate));
            }
        }

        String finalState = state;
        if (finalState == null || finalState.trim().isEmpty() || finalState.equals("null")) {
            finalState = getInitStateFromTemplate(userId, finalTemplate);
        }

        double posX = (x != null) ? x : DEFAULT_POSITION_X;
        double posY = (y != null) ? y : DEFAULT_POSITION_Y;
        int width = (w != null) ? w : DEFAULT_WIDTH;
        int height = (h != null) ? h : DEFAULT_HEIGHT;

        String generatedId;

        if (label != null && !label.equals("null") && !label.isEmpty() && !nodeRepo.existsById(label)) {
            generatedId = label;
        } else {
            if (label != null && nodeRepo.existsById(label) && !label.equals("null") && !label.isEmpty()) {
                resultMsg.append(String.format("【系统提示】您指定的名称 '%s' 已经存在，系统已为您自动生成新名称。\n", label));
            }

            java.util.Random random = new java.util.Random();
            int retryCount = 0;

            do {
                int randomNum = random.nextInt(RANDOM_ID_RANGE);
                generatedId = finalTemplate + "_ai_" + randomNum;
                retryCount++;

                if (retryCount > MAX_RETRY_COUNT) {
                    generatedId = finalTemplate + "_ai_" + UUID.randomUUID().toString().substring(0, UUID_SUFFIX_LENGTH);
                    break;
                }
            } while (nodeRepo.existsById(generatedId));
        }

        DeviceNodePo po = DeviceNodePo.builder()
                .id(generatedId)
                .userId(userId)
                .templateName(finalTemplate)
                .label(generatedId)
                .posX(posX)
                .posY(posY)
                .width(width)
                .height(height)
                .state(finalState)
                .build();

        nodeRepo.save(Objects.requireNonNull(po, "node to save must not be null"));

        resultMsg.insert(0, String.format("成功创建设备: %s。", generatedId));
        return resultMsg.toString();
    }

    @Override
    @Transactional
    public String deleteNode(Long userId, String label) {
        Optional<DeviceNodePo> nodeOpt = nodeRepo.findByUserIdAndLabel(userId, label);

        if (nodeOpt.isPresent()) {
            DeviceNodePo node = nodeOpt.get();
            nodeRepo.delete(Objects.requireNonNull(node, "node to delete must not be null"));
            log.info("成功删除设备: {}", label);
            return "成功删除设备: " + label;
        } else {
            return String.format("删除失败：未找到名称为 '%s' 的设备。请检查名称是否正确。", label);
        }
    }

    private String findBestMatch(String target, List<String> candidates) {
        if (candidates == null || candidates.isEmpty()) {
            return null;
        }

        String best = null;
        int minDistance = Integer.MAX_VALUE;
        String normalizedTarget = target.toLowerCase();

        for (String candidate : candidates) {
            String normalizedCandidate = candidate.toLowerCase();

            // Check for substring match first
            if (normalizedCandidate.contains(normalizedTarget) || normalizedTarget.contains(normalizedCandidate)) {
                return candidate;
            }

            // Calculate Levenshtein distance using utility class
            int dist = LevenshteinDistanceUtil.calculate(normalizedTarget, normalizedCandidate);

            if (dist < minDistance) {
                minDistance = dist;
                best = candidate;
            }
        }

        // Return null if similarity is too low
        if (minDistance > target.length() / 2 + 2) {
            return null;
        }
        return best;
    }

    private String chooseFallbackTemplate(List<String> templates) {
        if (templates == null || templates.isEmpty()) {
            return null;
        }
        for (String template : templates) {
            if (template != null && template.trim().equalsIgnoreCase("Air Conditioner")) {
                return template;
            }
        }
        return templates.stream().filter(t -> t != null && !t.isBlank()).findFirst().orElse(null);
    }

    private String getInitStateFromTemplate(Long userId, String templateName) {
        try {
            Optional<DeviceTemplatePo> templateOpt = deviceTemplateService.findTemplateByName(userId, templateName);

            if (templateOpt.isEmpty()) {
                log.warn("模板 {} 不存在，使用硬兜底状态", templateName);
                return HARD_FALLBACK_STATE;
            }

            String json = templateOpt.get().getManifestJson();
            if (json == null || json.isEmpty()) {
                return HARD_FALLBACK_STATE;
            }

            JsonNode rootNode = objectMapper.readTree(json);

            if (rootNode.has("InitState")) {
                return rootNode.get("InitState").asText();
            } else {
                log.warn("模板 {} 的 Manifest 中缺少 InitState 字段", templateName);
                return HARD_FALLBACK_STATE;
            }

        } catch (Exception e) {
            log.error("解析模板 {} 的 Manifest 失败", templateName, e);
            return HARD_FALLBACK_STATE;
        }
    }
}
