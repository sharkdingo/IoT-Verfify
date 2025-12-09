package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
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
    private final DeviceTemplateRepository templateRepo;
    private final ObjectMapper objectMapper; // Spring Boot 自动配置的 Jackson 工具

    private static final String DEFAULT_TEMPLATE = "AC Cooler";
    private static final String HARD_FALLBACK_STATE = "Working";

    @Override
    public String searchNodes(String keyword) {
        List<DeviceNodePo> results;

        // 1. 如果关键词为空，返回所有
        if (keyword == null || keyword.trim().isEmpty() || keyword.equalsIgnoreCase("所有设备")) {
            results = nodeRepo.findAll();
        } else {
            // 2. 【核心修改】调用混合搜索
            // 用户搜 "Cooler" -> 既能搜到 Template="AC Cooler"，也能搜到 Label="My_Cooler_1"
            results = nodeRepo.findByTemplateNameContainingIgnoreCaseOrLabelContainingIgnoreCase(keyword, keyword);
        }

        // 3. 序列化结果
        try {
            if (results.isEmpty()) {
                return "未找到匹配 '" + keyword + "' 的设备。";
            }
            // 简单序列化 (如果字段太多，建议定义一个简单的 DTO 只返回 AI 需要的关键字段，如 id, label, templateName)
            return objectMapper.writeValueAsString(results);
        } catch (JsonProcessingException e) {
            log.error("序列化搜索结果失败", e);
            return "[]";
        }
    }

    @Override
    @Transactional
    public String addNode(String reqTemplate, String label, Double x, Double y, String state, Integer w, Integer h) {

        String finalTemplate = reqTemplate;
        StringBuilder resultMsg = new StringBuilder();

        // 1. 核心：模板校验与模糊匹配 (保持之前的逻辑不变)
        if (!templateRepo.existsByName(reqTemplate)) {
            List<String> allTemplates = templateRepo.findAllNames();
            String bestMatch = findBestMatch(reqTemplate, allTemplates);

            if (bestMatch != null) {
                finalTemplate = bestMatch;
                resultMsg.append(String.format("【系统提示】库中未找到 '%s'，已为您自动匹配最接近的模板 '%s'。", reqTemplate, finalTemplate));
            } else {
                finalTemplate = DEFAULT_TEMPLATE;
                resultMsg.append(String.format("【系统提示】无法识别模板 '%s'，已使用默认模板 '%s'。", reqTemplate, finalTemplate));
            }
        }

        String finalState = state;
        // 只有当 AI 没传状态 (null 或空) 时，才去查 Manifest
        if (finalState == null || finalState.trim().isEmpty()) {
            finalState = getInitStateFromTemplate(finalTemplate);
        }

        // 2. 处理默认值
        double posX = (x != null) ? x : 150.0;
        double posY = (y != null) ? y : 150.0;
        int width = (w != null) ? w : 110;
        int height = (h != null) ? h : 90;

        // 3. 生成符合 "Template_ai_数字" 格式的唯一 ID
        String generatedId;
        java.util.Random random = new java.util.Random();
        int retryCount = 0;

        // 循环生成，直到找到一个数据库里不存在的 ID，防止重复
        do {
            int randomNum = random.nextInt(10000); // 生成 0 - 9999 的随机数
            // 格式化：例如 AC Cooler_ai_1
            generatedId = finalTemplate + "_ai_" + randomNum;
            retryCount++;

            // 防止死循环（极小概率）：如果尝试10次都重复，就加个UUID后缀兜底
            if (retryCount > 10) {
                generatedId = finalTemplate + "_ai_" + UUID.randomUUID().toString().substring(0, 6);
                break;
            }
        } while (nodeRepo.existsById(generatedId)); // 如果ID已存在，就重试

        // 4. 构建 PO
        DeviceNodePo po = DeviceNodePo.builder()
                .id(generatedId)            // 设置 ID 为 AC Cooler_ai_xxx
                .templateName(finalTemplate)
                .label(generatedId)         // 【核心需求】Label 和 ID 完全一致
                .posX(posX)
                .posY(posY)
                .width(width)
                .height(height)
                .state(finalState)
                .build();

        // ================== 【修改重点结束】 ==================

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
            // 或者 nodeRepo.deleteById(node.getId());

            log.info("成功删除设备: {}", label);
            return "成功删除设备: " + label;
        } else {
            // 3. 如果没找到，给 AI 返回明确的错误，AI 可能会尝试重新搜索或询问用户
            return String.format("删除失败：未找到名称为 '%s' 的设备。请检查名称是否正确。", label);
        }
    }

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

    /**
     * 计算两个字符串的编辑距离 (Levenshtein Distance)
     * 这样你就不需要在 pom.xml 里引入 Apache Commons Text 了
     */
    private int calculateLevenshteinDistance(String s1, String s2) {
        int len1 = s1.length();
        int len2 = s2.length();

        int[][] dp = new int[len1 + 1][len2 + 1];

        for (int i = 0; i <= len1; i++) {
            dp[i][0] = i;
        }
        for (int j = 0; j <= len2; j++) {
            dp[0][j] = j;
        }

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
     */
    private String getInitStateFromTemplate(String templateName) {
        try {
            // 1. 查库拿到 PO
            Optional<DeviceTemplatePo> templateOpt = templateRepo.findByName(templateName);

            if (templateOpt.isEmpty()) {
                log.warn("模板 {} 不存在，使用硬兜底状态", templateName);
                return HARD_FALLBACK_STATE;
            }

            String json = templateOpt.get().getManifestJson();
            if (json == null || json.isEmpty()) {
                return HARD_FALLBACK_STATE;
            }

            // 2. 解析 JSON
            JsonNode rootNode = objectMapper.readTree(json);

            // 3. 寻找 "InitState" 键
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