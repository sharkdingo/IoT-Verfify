package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.core.io.Resource;
import org.springframework.core.io.support.PathMatchingResourcePatternResolver;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
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
    public List<String> getAllTemplateNames(Long userId) {
        List<DeviceTemplatePo> allPos = templateRepo.findByUserId(userId);
        List<String> names = new ArrayList<>();

        for (DeviceTemplatePo po : allPos) {
            String name = extractNameFromJson(po.getManifestJson());

            if (name == null || name.trim().isEmpty()) {
                name = po.getName();
            }

            if (name != null) {
                names.add(name);
            }
        }

        return names;
    }

    @Override
    @Transactional(readOnly = true)
    public Optional<DeviceTemplatePo> findTemplateByName(Long userId, String targetName) {
        if (targetName == null) return Optional.empty();
        String normalizedTarget = targetName.trim().toLowerCase();
        List<DeviceTemplatePo> allPos = templateRepo.findByUserId(userId);
        for (DeviceTemplatePo po : allPos) {
            String jsonName = extractNameFromJson(po.getManifestJson());
            if (jsonName != null && jsonName.trim().toLowerCase().equals(normalizedTarget)) {
                return Optional.of(po);
            }
        }
        return Optional.empty();
    }

    @Override
    @Transactional(readOnly = true)
    public boolean checkTemplateExists(Long userId, String targetName) {
        return findTemplateByName(userId, targetName).isPresent();
    }

    private String extractNameFromJson(String json) {
        if (json == null || json.trim().isEmpty()) return null;
        try {
            JsonNode root = objectMapper.readTree(json);

            if (root.hasNonNull("Name")) {
                return root.get("Name").asText();
            }
            if (root.hasNonNull("name")) {
                return root.get("name").asText();
            }
        } catch (Exception e) {
            log.warn("解析模板 JSON 异常: {}", json.substring(0, Math.min(json.length(), 20)));
        }
        return null;
    }

    @Override
    @Transactional
    public int initDefaultTemplates(Long userId) {
        if (!templateRepo.findByUserId(userId).isEmpty()) {
            log.debug("User {} already has templates, skipping init", userId);
            return 0;
        }

        int count = 0;
        try {
            PathMatchingResourcePatternResolver resolver = new PathMatchingResourcePatternResolver();
            Resource[] resources = resolver.getResources("classpath:deviceTemplate/*.json");
            log.info("Found {} device template resources on classpath for user {}", resources.length, userId);

            if (resources.length == 0) {
                // Fallback: try classpath* pattern
                resources = resolver.getResources("classpath*:deviceTemplate/*.json");
                log.info("Fallback found {} device template resources for user {}", resources.length, userId);
            }

            List<DeviceTemplatePo> templates = new ArrayList<>();
            for (Resource resource : resources) {
                try (InputStream is = resource.getInputStream()) {
                    String json = new String(is.readAllBytes(), StandardCharsets.UTF_8);
                    String name = extractNameFromJson(json);
                    if (name == null || name.isBlank()) {
                        String filename = resource.getFilename();
                        name = filename != null ? filename.replace(".json", "") : "Unknown";
                    }

                    templates.add(DeviceTemplatePo.builder()
                            .userId(userId)
                            .name(name)
                            .manifestJson(json)
                            .build());
                    count++;
                } catch (Exception e) {
                    log.warn("Failed to load template: {}", resource.getFilename(), e);
                }
            }

            if (!templates.isEmpty()) {
                templateRepo.saveAll(templates);
                log.info("Initialized {} default device templates for user {}", count, userId);
            } else {
                log.warn("No device templates found on classpath for user {}", userId);
            }
        } catch (Exception e) {
            log.error("Failed to initialize default templates for user {}", userId, e);
        }
        return count;
    }
}
