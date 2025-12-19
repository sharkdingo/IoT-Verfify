package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

@Slf4j
@Service
@RequiredArgsConstructor
public class NodeServiceImpl implements NodeService {

    private final DeviceNodeRepository nodeRepo;
    // 移除直接依赖 templateRepo，改用 Service
    private final DeviceTemplateService deviceTemplateService;
    private final ObjectMapper objectMapper;

    private static final String DEFAULT_TEMPLATE = "AC Cooler";
    private static final String HARD_FALLBACK_STATE = "Working";

    @Override
    public String searchNodes(String keyword) {
        List<DeviceNodePo> results;

        // 1. 如果关键词为空，返回所有
        if (keyword == null || keyword.trim().isEmpty() || keyword.equalsIgnoreCase("所有设备")) {
            results = nodeRepo.findAll();
        } else {
            // 2. 调用混合搜索
            results = nodeRepo.findByTemplateNameContainingIgnoreCaseOrLabelContainingIgnoreCase(keyword, keyword);
        }

        // 3. 序列化结果
        try {
            if (results.isEmpty()) {
                return "未找到匹配 '" + keyword + "' 的设备。";
            }
            // 简单序列化
            return objectMapper.writeValueAsString(results);
        } catch (JsonProcessingException e) {
            log.error("序列化搜索结果失败", e);
            return "[]";
        }
    }

    @Override
    @Transactional
    public String addNode(String reqTemplate, String label, Double x, Double y, String state, Integer w, Integer h) {

        String rawTemplate = reqTemplate != null ? reqTemplate.trim() : "";
        String finalTemplate = rawTemplate;
        StringBuilder resultMsg = new StringBuilder();

        // 2. 核心：模板校验与模糊匹配
        // 使用 Service 检查 (现在支持忽略大小写了)
        if (!deviceTemplateService.checkTemplateExists(rawTemplate)) {

            List<String> allTemplates = deviceTemplateService.getAllTemplateNames();

            log.info("User requested template: [{}], Available templates in DB: {}", rawTemplate, allTemplates);

            String bestMatch = findBestMatch(rawTemplate, allTemplates);

            if (bestMatch != null) {
                finalTemplate = bestMatch;

                // Ignore case/space difference
                String normRaw = rawTemplate.replace(" ", "").toLowerCase();
                String normMatch = bestMatch.replace(" ", "").toLowerCase();

                if (!normRaw.equals(normMatch)) {
                    resultMsg.append(String.format("【系统提示】库中未找到 '%s'，已为您自动匹配最接近的模板 '%s'。", rawTemplate, finalTemplate));
                } else {
                    log.info("Template name auto-corrected: {} -> {}", rawTemplate, finalTemplate);
                }
            } else {
                finalTemplate = DEFAULT_TEMPLATE;
                resultMsg.append(String.format("【系统提示】无法识别模板 '%s'，已使用默认模板 '%s'。", rawTemplate, finalTemplate));
            }
        }
        String finalState = state;
        // 只有当 AI 没传状态 (null 或空) 时，才去查 Manifest
        if (finalState == null || finalState.trim().isEmpty() || finalState.equals("null")) {
            finalState = getInitStateFromTemplate(finalTemplate);
        }
        // 2. 处理默认值
        double posX = (x != null) ? x : 250.0;
        double posY = (y != null) ? y : 250.0;
        int width = (w != null) ? w : 110;
        int height = (h != null) ? h : 90;

        // 3. 简化后的 ID 生成逻辑
        String generatedId;

        // 3.1. 判断是否可以直接使用用户提供的 Label
        if (label != null && !label.equals("null") && !label.isEmpty() && !nodeRepo.existsById(label)) {
            generatedId = label;
        } else {
            // 3.2. 进入自动生成逻辑
            if (label != null && nodeRepo.existsById(label) && !label.equals("null") && !label.isEmpty()) {
                resultMsg.append(String.format("【系统提示】您指定的名称 '%s' 已经存在，系统已为您自动生成新名称。\n", label));
            }

            java.util.Random random = new java.util.Random();
            int retryCount = 0;

            do {
                int randomNum = random.nextInt(1000);
                generatedId = finalTemplate + "_ai_" + randomNum;
                retryCount++;

                if (retryCount > 10) {
                    generatedId = finalTemplate + "_ai_" + UUID.randomUUID().toString().substring(0, 6);
                    break;
                }
            } while (nodeRepo.existsById(generatedId));
        }

        // 4. 构建 PO
        DeviceNodePo po = DeviceNodePo.builder()
                .id(generatedId)
                .templateName(finalTemplate)
                .label(generatedId)
                .posX(posX)
                .posY(posY)
                .width(width)
                .height(height)
                .state(finalState)
                .build();

        // 5. 落库
        nodeRepo.save(po);

        // 6. 返回结果
        resultMsg.insert(0, String.format("成功创建设备: %s。", generatedId));
        return resultMsg.toString();
    }

    @Override
    @Transactional
    public String deleteNode(String label) {
        // 1. 根据 Label 查找设备
        Optional<DeviceNodePo> nodeOpt = nodeRepo.findByLabel(label);

        if (nodeOpt.isPresent()) {
            DeviceNodePo node = nodeOpt.get();
            // 2. 获取 ID 并删除
            nodeRepo.delete(node);
            log.info("成功删除设备: {}", label);
            return "成功删除设备: " + label;
        } else {
            return String.format("删除失败：未找到名称为 '%s' 的设备。请检查名称是否正确。", label);
        }
    }

    // ... findBestMatch 和 calculateLevenshteinDistance 保持不变 ...

    /**
     * 寻找最佳匹配项
     */
    private String findBestMatch(String target, List<String> candidates) {
        if (candidates == null || candidates.isEmpty()) return null;

        String best = null;
        int minDistance = Integer.MAX_VALUE;

        for (String candidate : candidates) {
            // 1. 简单的包含匹配优先 (比如 "Big Switch" -> "Switch")
            if (candidate.toLowerCase().contains(target.toLowerCase()) || target.toLowerCase().contains(candidate.toLowerCase())) {
                return candidate;
            }

            // 2. 编辑距离计算 (手写算法，无需依赖包)
            int dist = calculateLevenshteinDistance(target.toLowerCase(), candidate.toLowerCase());

            if (dist < minDistance) {
                minDistance = dist;
                best = candidate;
            }
        }

        // 阈值控制：如果差异过大（超过目标长度的一半 + 2），则认为匹配失败
        if (minDistance > target.length() / 2 + 2) {
            return null;
        }
        return best;
    }

    private int calculateLevenshteinDistance(String s1, String s2) {
        int len1 = s1.length();
        int len2 = s2.length();
        int[][] dp = new int[len1 + 1][len2 + 1];

        for (int i = 0; i <= len1; i++) dp[i][0] = i;
        for (int j = 0; j <= len2; j++) dp[0][j] = j;

        for (int i = 1; i <= len1; i++) {
            for (int j = 1; j <= len2; j++) {
                int cost = (s1.charAt(i - 1) == s2.charAt(j - 1)) ? 0 : 1;
                dp[i][j] = Math.min(Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1), dp[i - 1][j - 1] + cost);
            }
        }
        return dp[len1][len2];
    }

    /**
     * 【辅助方法】解析 manifestJson 获取 InitState
     * 修改：使用 DeviceTemplateService 替代直接查库
     */
    private String getInitStateFromTemplate(String templateName) {
        try {
            // 改用 Service 获取
            Optional<DeviceTemplatePo> templateOpt = deviceTemplateService.findTemplateByName(templateName);

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