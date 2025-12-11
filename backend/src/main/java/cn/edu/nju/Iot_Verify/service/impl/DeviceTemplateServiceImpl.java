// src/main/java/cn/edu/nju/Iot_Verify/service/impl/DeviceTemplateServiceImpl.java
package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.cache.annotation.Cacheable; // 可选
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

@Slf4j
@Service
@RequiredArgsConstructor
public class DeviceTemplateServiceImpl implements DeviceTemplateService {

    private final DeviceTemplateRepository templateRepo;
    private final ObjectMapper objectMapper;

    @Override
    @Transactional(readOnly = true)
    public List<String> getAllTemplateNames() {
        List<DeviceTemplatePo> allPos = templateRepo.findAll();

        // Log in English to avoid encoding issues
        //log.info("Fetching all templates. Total records found in DB: {}", allPos.size());

        List<String> names = new ArrayList<>();

        for (DeviceTemplatePo po : allPos) {
            // 1. Try to extract from JSON
            String name = extractNameFromJson(po.getManifestJson());

            // 2. Fallback: Use PO name if JSON parsing fails
            if (name == null || name.trim().isEmpty()) {
                name = po.getName();
                // Debug log (Optional, usually verify logic is enough)
                // log.debug("Manifest JSON name missing for ID: {}, using DB column name: {}", po.getId(), name);
            }

            if (name != null) {
                names.add(name);
            }
        }

        //log.info("Final available template names: {}", names);
        return names;
    }

    @Override
    @Transactional(readOnly = true)
    public Optional<DeviceTemplatePo> findTemplateByName(String targetName) {
        if (targetName == null) return Optional.empty();
        // 1. 预处理目标名称：去空格、转小写
        String normalizedTarget = targetName.trim().toLowerCase();
        List<DeviceTemplatePo> allPos = templateRepo.findAll();
        for (DeviceTemplatePo po : allPos) {
            String jsonName = extractNameFromJson(po.getManifestJson());
            // 2. 宽松匹配：忽略大小写
            if (jsonName != null && jsonName.trim().toLowerCase().equals(normalizedTarget)) {
                return Optional.of(po);
            }
        }
        return Optional.empty();
    }

    @Override
    @Transactional(readOnly = true)
    public boolean checkTemplateExists(String targetName) {
        return findTemplateByName(targetName).isPresent();
    }

    // --- 私有辅助方法：解析 JSON 提取 name ---
    private String extractNameFromJson(String json) {
        if (json == null || json.trim().isEmpty()) return null;
        try {
            JsonNode root = objectMapper.readTree(json);

            // 1. 【优先】读取大写 "Name" (这是你当前数据库的格式)
            if (root.hasNonNull("Name")) {
                return root.get("Name").asText();
            }
            // 2. 【兼容】读取小写 "name" (防止部分数据格式不一致)
            if (root.hasNonNull("name")) {
                return root.get("name").asText();
            }
        } catch (Exception e) {
            // 防止日志过长，只打印前20个字符
            log.warn("解析模板 JSON 异常: {}", json.substring(0, Math.min(json.length(), 20)));
        }
        return null;
    }
}