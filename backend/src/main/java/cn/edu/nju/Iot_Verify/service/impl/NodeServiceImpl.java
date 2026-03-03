package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
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
import java.util.concurrent.ThreadLocalRandom;

@Slf4j
@Service
@RequiredArgsConstructor
public class NodeServiceImpl implements NodeService {

    private final DeviceNodeRepository nodeRepo;
    private final DeviceTemplateService deviceTemplateService;
    private final ObjectMapper objectMapper;

    private static final String HARD_FALLBACK_STATE = "Working";
    private static final double DEFAULT_POSITION_X = 250.0;
    private static final double DEFAULT_POSITION_Y = 250.0;
    private static final int DEFAULT_WIDTH = 110;
    private static final int DEFAULT_HEIGHT = 90;
    private static final int RANDOM_ID_RANGE = 1000;
    private static final int MAX_RETRY_COUNT = 10;
    private static final int UUID_SUFFIX_LENGTH = 6;

    @Override
    public String searchNodes(Long userId, String keyword) {
        List<DeviceNodePo> results;
        if (keyword == null || keyword.trim().isEmpty() || "all devices".equalsIgnoreCase(keyword.trim())) {
            results = nodeRepo.findByUserId(userId);
        } else {
            results = nodeRepo.searchByUserIdAndTemplateOrLabel(userId, keyword);
        }

        try {
            if (results.isEmpty()) {
                return "No devices found matching '" + keyword + "'.";
            }
            return objectMapper.writeValueAsString(results);
        } catch (JsonProcessingException e) {
            log.error("Failed to serialize search result", e);
            return "[]";
        }
    }

    @Override
    @Transactional
    public String addNode(Long userId,
                          String reqTemplate,
                          String label,
                          Double x,
                          Double y,
                          String state,
                          Integer w,
                          Integer h) {

        String rawTemplate = reqTemplate != null ? reqTemplate.trim() : "";
        String finalTemplate = rawTemplate;
        StringBuilder resultMsg = new StringBuilder();

        if (!deviceTemplateService.checkTemplateExists(userId, rawTemplate)) {
            List<String> allTemplates = deviceTemplateService.getAllTemplateNames(userId);
            log.info("User requested template: [{}], available templates: {}", rawTemplate, allTemplates);

            String bestMatch = findBestMatch(rawTemplate, allTemplates);
            if (bestMatch != null) {
                finalTemplate = bestMatch;
                String normalizedRaw = rawTemplate.replace(" ", "").toLowerCase();
                String normalizedMatch = bestMatch.replace(" ", "").toLowerCase();
                if (!normalizedRaw.equals(normalizedMatch)) {
                    resultMsg.append(String.format(
                            "[System] Template '%s' not found. Auto-matched to '%s'. ",
                            rawTemplate,
                            finalTemplate));
                } else {
                    log.info("Template name auto-corrected: {} -> {}", rawTemplate, finalTemplate);
                }
            } else {
                String fallbackTemplate = chooseFallbackTemplate(allTemplates);
                if (fallbackTemplate == null) {
                    throw new BadRequestException(String.format(
                            "Create device failed: cannot resolve template '%s' and no fallback template is available.",
                            rawTemplate));
                }
                finalTemplate = fallbackTemplate;
                resultMsg.append(String.format(
                        "[System] Template '%s' not recognized. Fallback template '%s' is used. ",
                        rawTemplate,
                        finalTemplate));
            }
        }

        String finalState = state;
        if (finalState == null || finalState.trim().isEmpty() || "null".equals(finalState)) {
            finalState = getInitStateFromTemplate(userId, finalTemplate);
        }

        double posX = x != null ? x : DEFAULT_POSITION_X;
        double posY = y != null ? y : DEFAULT_POSITION_Y;
        int width = w != null ? w : DEFAULT_WIDTH;
        int height = h != null ? h : DEFAULT_HEIGHT;

        String generatedId;
        if (label != null && !label.equals("null") && !label.isEmpty() && !nodeRepo.existsByUserIdAndId(userId, label)) {
            generatedId = label;
        } else {
            if (label != null && !label.equals("null") && !label.isEmpty() && nodeRepo.existsByUserIdAndId(userId, label)) {
                resultMsg.append(String.format(
                        "[System] Requested name '%s' already exists. Auto-generated a new name. ",
                        label));
            }

            int retryCount = 0;
            do {
                generatedId = finalTemplate + "_ai_" + ThreadLocalRandom.current().nextInt(RANDOM_ID_RANGE);
                retryCount++;
                if (retryCount > MAX_RETRY_COUNT) {
                    generatedId = finalTemplate + "_ai_" + UUID.randomUUID().toString().substring(0, UUID_SUFFIX_LENGTH);
                    break;
                }
            } while (nodeRepo.existsByUserIdAndId(userId, generatedId));
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

        resultMsg.insert(0, String.format("Created device successfully: %s. ", generatedId));
        return resultMsg.toString();
    }

    @Override
    @Transactional
    public String deleteNode(Long userId, String label) {
        Optional<DeviceNodePo> nodeOpt = nodeRepo.findByUserIdAndLabel(userId, label);
        if (nodeOpt.isPresent()) {
            DeviceNodePo node = nodeOpt.get();
            nodeRepo.delete(Objects.requireNonNull(node, "node to delete must not be null"));
            log.info("Deleted device successfully: {}", label);
            return "Deleted device successfully: " + label;
        }
        throw new ResourceNotFoundException(String.format("Device not found for deletion: '%s'.", label));
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
            if (normalizedCandidate.contains(normalizedTarget) || normalizedTarget.contains(normalizedCandidate)) {
                return candidate;
            }

            int dist = LevenshteinDistanceUtil.calculate(normalizedTarget, normalizedCandidate);
            if (dist < minDistance) {
                minDistance = dist;
                best = candidate;
            }
        }

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
                log.warn("Template {} not found, using fallback state", templateName);
                return HARD_FALLBACK_STATE;
            }

            String json = templateOpt.get().getManifestJson();
            if (json == null || json.isEmpty()) {
                return HARD_FALLBACK_STATE;
            }

            JsonNode rootNode = objectMapper.readTree(json);
            if (rootNode.has("InitState")) {
                return rootNode.get("InitState").asText();
            }

            log.warn("Template {} manifest does not contain InitState", templateName);
            return HARD_FALLBACK_STATE;
        } catch (Exception e) {
            log.error("Failed to parse template manifest for {}", templateName, e);
            return HARD_FALLBACK_STATE;
        }
    }
}
