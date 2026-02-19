package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
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

    @Override
    @Transactional(readOnly = true)
    public List<String> getAllTemplateNames(Long userId) {
        return templateRepo.findByUserId(userId).stream()
                .map(DeviceTemplatePo::getName)
                .filter(name -> name != null && !name.isBlank())
                .toList();
    }

    @Override
    @Transactional(readOnly = true)
    public Optional<DeviceTemplatePo> findTemplateByName(Long userId, String targetName) {
        if (targetName == null) {
            return Optional.empty();
        }
        String normalizedTarget = targetName.trim().toLowerCase();
        return templateRepo.findByUserId(userId).stream()
                .filter(po -> po.getName() != null && po.getName().trim().toLowerCase().equals(normalizedTarget))
                .findFirst();
    }

    @Override
    @Transactional(readOnly = true)
    public boolean checkTemplateExists(Long userId, String targetName) {
        return findTemplateByName(userId, targetName).isPresent();
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
                resources = resolver.getResources("classpath*:deviceTemplate/*.json");
                log.info("Fallback found {} device template resources for user {}", resources.length, userId);
            }

            List<DeviceTemplatePo> templates = new ArrayList<>();
            for (Resource resource : resources) {
                try (InputStream is = resource.getInputStream()) {
                    String json = new String(is.readAllBytes(), StandardCharsets.UTF_8);
                    String filename = resource.getFilename();
                    String name = extractManifestName(json);
                    if (name == null || name.isBlank()) {
                        name = filename != null ? filename.replace(".json", "") : "Unknown";
                    }
                    if (name.isBlank()) {
                        name = "Unknown";
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

    private String extractManifestName(String json) {
        DeviceManifest manifest = JsonUtils.fromJsonOrDefault(
                json,
                new TypeReference<DeviceManifest>() {},
                null
        );
        if (manifest == null || manifest.getName() == null) {
            return null;
        }
        return manifest.getName().trim();
    }
}
