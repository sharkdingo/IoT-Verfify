package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.DeviceLabelConflictException;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.dto.device.DeviceCreationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeConfigDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

@Slf4j
@Service
@RequiredArgsConstructor
public class NodeServiceImpl implements NodeService {

    private final BoardStorageService boardStorageService;
    private final DeviceTemplateService deviceTemplateService;
    private final ObjectMapper objectMapper;

    private static final String HARD_FALLBACK_STATE = "Working";
    private static final double DEFAULT_POSITION_X = 250.0;
    private static final double DEFAULT_POSITION_Y = 250.0;
    private static final int DEFAULT_WIDTH = 176;
    private static final int DEFAULT_HEIGHT = 128;

    @Override
    public List<DeviceNodeDto> searchNodes(Long userId, String keyword) {
        List<DeviceNodeDto> nodes = boardStorageService.getNodes(userId);
        String query = keyword == null ? "" : keyword.trim();
        if (query.isEmpty() || "all devices".equalsIgnoreCase(query)) {
            return new ArrayList<>(nodes);
        }
        String normalizedQuery = query.toLowerCase(Locale.ROOT);
        return nodes.stream()
                .filter(node -> containsIgnoreCase(node.getLabel(), normalizedQuery)
                        || containsIgnoreCase(node.getTemplateName(), normalizedQuery)
                        || containsIgnoreCase(node.getId(), normalizedQuery))
                .toList();
    }

    @Override
    public DeviceCreationResultDto addNode(Long userId,
                                           String reqTemplate,
                                           String label,
                                           Double x,
                                           Double y,
                                           DeviceRuntimeConfigDto runtime,
                                           Integer w,
                                           Integer h) {

        String rawTemplate = reqTemplate != null ? reqTemplate.trim() : "";
        String finalTemplate = rawTemplate;
        if (rawTemplate.isBlank()) {
            throw new BadRequestException("Create device failed: templateName is required.");
        }
        if (!deviceTemplateService.checkTemplateExists(userId, rawTemplate)) {
            throw new BadRequestException(String.format(
                    "Create device failed: template '%s' does not exist.",
                    rawTemplate));
        }

        DeviceManifest manifest = loadTemplateManifest(userId, finalTemplate);
        String requestedState = normalizeOptionalValue(runtime != null ? runtime.getState() : null);
        InitialStateResolution stateResolution = requestedState != null
                ? new InitialStateResolution(requestedState, "requested", null)
                : resolveInitialState(finalTemplate, manifest);
        String nodeState = stateResolution.state();

        List<String> defaultsApplied = new ArrayList<>();
        DeviceRuntimeConfigDto effectiveRuntime = effectiveRuntime(manifest, nodeState, runtime, defaultsApplied);

        double posX = x != null ? x : DEFAULT_POSITION_X;
        double posY = y != null ? y : DEFAULT_POSITION_Y;
        int width = w != null ? w : DEFAULT_WIDTH;
        int height = h != null ? h : DEFAULT_HEIGHT;
        String requestedLabel = normalizeLabel(label);

        DeviceMutationResultDto mutation = boardStorageService.createNode(userId, currentNodes -> {
            String finalLabel;
            if (requestedLabel != null) {
                String suggestedLabel = chooseAvailableLabel(requestedLabel, currentNodes);
                if (!requestedLabel.equals(suggestedLabel)) {
                    throw new DeviceLabelConflictException(requestedLabel, suggestedLabel);
                }
                finalLabel = requestedLabel;
            } else {
                finalLabel = chooseAvailableLabel(finalTemplate, currentNodes);
            }
            String generatedId = chooseAvailableId(currentNodes);

            DeviceNodeDto node = new DeviceNodeDto();
            node.setId(generatedId);
            node.setTemplateName(finalTemplate);
            node.setLabel(finalLabel);
            DeviceNodeDto.Position position = new DeviceNodeDto.Position();
            position.setX(posX);
            position.setY(posY);
            node.setPosition(position);
            node.setWidth(width);
            node.setHeight(height);
            node.setState(nodeState);
            node.setCurrentStateTrust(effectiveRuntime.getCurrentStateTrust());
            node.setCurrentStatePrivacy(effectiveRuntime.getCurrentStatePrivacy());
            node.setVariables(effectiveRuntime.getVariables());
            node.setPrivacies(effectiveRuntime.getPrivacies());
            return node;
        });
        DeviceNodeDto createdNode = mutation.getAffectedDevices().stream()
                .findFirst()
                .orElseThrow(() -> new IllegalStateException(
                        "Device creation completed without an affected device"));

        if (x == null) defaultsApplied.add("position.x");
        if (y == null) defaultsApplied.add("position.y");
        if (w == null) defaultsApplied.add("width");
        if (h == null) defaultsApplied.add("height");
        if (requestedState == null) defaultsApplied.add("state");
        if (requestedLabel == null) defaultsApplied.add("label");

        List<String> warnings = new ArrayList<>();
        if (stateResolution.warning() != null) {
            warnings.add(stateResolution.warning());
        }

        return DeviceCreationResultDto.builder()
                .device(createdNode)
                .initialStateSource(stateResolution.source())
                .defaultsApplied(defaultsApplied)
                .warnings(warnings)
                .environmentVariables(mutation.getEnvironmentVariables())
                .environmentChanges(mutation.getEnvironmentChanges())
                .build();
    }

    private boolean containsIgnoreCase(String value, String normalizedQuery) {
        return value != null && value.toLowerCase(Locale.ROOT).contains(normalizedQuery);
    }

    private String normalizeLabel(String label) {
        if (label == null || label.isBlank() || "null".equalsIgnoreCase(label.trim())) {
            return null;
        }
        return label.trim();
    }

    private String chooseAvailableId(List<DeviceNodeDto> nodes) {
        String candidate;
        do {
            candidate = "device_" + UUID.randomUUID();
        } while (!isDeviceIdAvailable(candidate, nodes));
        return candidate;
    }

    private String chooseAvailableLabel(String baseLabel, List<DeviceNodeDto> nodes) {
        Set<String> used = new HashSet<>();
        for (DeviceNodeDto node : nodes) {
            if (node != null && node.getLabel() != null) {
                used.add(node.getLabel().trim().toLowerCase(Locale.ROOT));
            }
        }
        String candidate = baseLabel;
        int suffix = 1;
        while (used.contains(candidate.toLowerCase(Locale.ROOT))) {
            candidate = baseLabel + "_" + suffix++;
        }
        return candidate;
    }

    private boolean isDeviceIdAvailable(String candidate, List<DeviceNodeDto> nodes) {
        if (candidate == null || candidate.isBlank()) {
            return false;
        }
        String normalizedCandidate = DeviceNameNormalizer.normalize(candidate);
        for (DeviceNodeDto node : nodes) {
            if (node == null) {
                continue;
            }
            String id = node.getId();
            if (candidate.equals(id)) {
                return false;
            }
            if (id != null && normalizedCandidate.equals(DeviceNameNormalizer.normalize(id))) {
                return false;
            }
        }
        return true;
    }

    private String normalizeOptionalValue(String value) {
        if (value == null || value.isBlank() || "null".equalsIgnoreCase(value.trim())) {
            return null;
        }
        return value.trim();
    }

    private DeviceManifest loadTemplateManifest(Long userId, String templateName) {
        try {
            Optional<DeviceTemplatePo> templateOpt = deviceTemplateService.findTemplateByName(userId, templateName);
            if (templateOpt.isEmpty()) {
                throw new PersistedDataIntegrityException(
                        "device template", templateName, "manifestJson", "template disappeared during device creation");
            }

            String json = templateOpt.get().getManifestJson();
            if (json == null || json.isBlank()) {
                throw new PersistedDataIntegrityException(
                        "device template", templateOpt.get().getId(), "manifestJson", "manifest is missing");
            }
            return objectMapper.readValue(json, DeviceManifest.class);
        } catch (PersistedDataIntegrityException e) {
            throw e;
        } catch (Exception e) {
            throw new PersistedDataIntegrityException("device template", templateName, "manifestJson", e);
        }
    }

    private InitialStateResolution resolveInitialState(String templateName, DeviceManifest manifest) {
        if (manifest != null && manifest.getInitState() != null && !manifest.getInitState().isBlank()) {
            return new InitialStateResolution(manifest.getInitState().trim(), "templateDefault", null);
        }
        log.warn("Template {} manifest has missing or blank InitState", templateName);
        return fallbackState(templateName);
    }

    private DeviceRuntimeConfigDto effectiveRuntime(DeviceManifest manifest,
                                                    String state,
                                                    DeviceRuntimeConfigDto requested,
                                                    List<String> defaultsApplied) {
        DeviceRuntimeConfigDto result = new DeviceRuntimeConfigDto();
        result.setState(state);

        boolean hasStateMachine = manifest != null
                && manifest.getModes() != null && !manifest.getModes().isEmpty()
                && manifest.getWorkingStates() != null && !manifest.getWorkingStates().isEmpty();
        if (hasStateMachine) {
            DeviceManifest.WorkingState workingState = manifest.getWorkingStates().stream()
                    .filter(item -> item != null && item.getName() != null
                            && item.getName().trim().equalsIgnoreCase(state))
                    .findFirst()
                    .orElse(null);
            String defaultTrust = workingState != null ? normalizeTrust(workingState.getTrust()) : "trusted";
            String defaultPrivacy = workingState != null ? normalizePrivacy(workingState.getPrivacy()) : "public";
            result.setCurrentStateTrust(requested != null && normalizeOptionalValue(requested.getCurrentStateTrust()) != null
                    ? requested.getCurrentStateTrust().trim().toLowerCase(Locale.ROOT) : defaultTrust);
            result.setCurrentStatePrivacy(requested != null && normalizeOptionalValue(requested.getCurrentStatePrivacy()) != null
                    ? requested.getCurrentStatePrivacy().trim().toLowerCase(Locale.ROOT) : defaultPrivacy);
            if (requested == null || normalizeOptionalValue(requested.getCurrentStateTrust()) == null) {
                defaultsApplied.add("currentStateTrust");
            }
            if (requested == null || normalizeOptionalValue(requested.getCurrentStatePrivacy()) == null) {
                defaultsApplied.add("currentStatePrivacy");
            }
        } else {
            result.setCurrentStateTrust(requested != null ? requested.getCurrentStateTrust() : null);
            result.setCurrentStatePrivacy(requested != null ? requested.getCurrentStatePrivacy() : null);
        }

        List<VariableStateDto> defaultVariables = defaultLocalVariables(manifest);
        List<PrivacyStateDto> defaultPrivacies = defaultLocalPrivacies(manifest);
        if (requested != null && requested.getVariables() != null) {
            result.setVariables(mergeLocalVariables(
                    requested.getVariables(), defaultVariables, defaultsApplied));
        } else if (!defaultVariables.isEmpty()) {
            result.setVariables(defaultVariables);
            defaultsApplied.add("variables");
        }
        if (requested != null && requested.getPrivacies() != null) {
            result.setPrivacies(mergeLocalPrivacies(
                    requested.getPrivacies(), defaultPrivacies, defaultsApplied));
        } else if (!defaultPrivacies.isEmpty()) {
            result.setPrivacies(defaultPrivacies);
            defaultsApplied.add("privacies");
        }
        return result;
    }

    private List<VariableStateDto> mergeLocalVariables(List<VariableStateDto> requested,
                                                       List<VariableStateDto> defaults,
                                                       List<String> defaultsApplied) {
        Map<String, VariableStateDto> defaultsByName = new LinkedHashMap<>();
        for (VariableStateDto value : defaults) {
            if (value != null && value.getName() != null) {
                defaultsByName.put(value.getName().toLowerCase(Locale.ROOT), value);
            }
        }
        Set<String> supplied = new HashSet<>();
        List<VariableStateDto> result = new ArrayList<>();
        for (VariableStateDto value : requested) {
            if (value == null || value.getName() == null) {
                result.add(value);
                continue;
            }
            String key = value.getName().toLowerCase(Locale.ROOT);
            supplied.add(key);
            VariableStateDto fallback = defaultsByName.get(key);
            String trust = normalizeOptionalValue(value.getTrust()) != null
                    ? value.getTrust().trim().toLowerCase(Locale.ROOT)
                    : fallback == null ? value.getTrust() : fallback.getTrust();
            String name = fallback == null ? value.getName() : fallback.getName();
            result.add(new VariableStateDto(name, value.getValue(), trust));
            if (fallback != null && normalizeOptionalValue(value.getTrust()) == null) {
                defaultsApplied.add("variables." + fallback.getName() + ".trust");
            }
        }
        for (Map.Entry<String, VariableStateDto> entry : defaultsByName.entrySet()) {
            if (!supplied.contains(entry.getKey())) {
                result.add(entry.getValue());
                defaultsApplied.add("variables." + entry.getValue().getName());
            }
        }
        return result;
    }

    private List<PrivacyStateDto> mergeLocalPrivacies(List<PrivacyStateDto> requested,
                                                      List<PrivacyStateDto> defaults,
                                                      List<String> defaultsApplied) {
        Map<String, PrivacyStateDto> defaultsByName = new LinkedHashMap<>();
        for (PrivacyStateDto value : defaults) {
            if (value != null && value.getName() != null) {
                defaultsByName.put(value.getName().toLowerCase(Locale.ROOT), value);
            }
        }
        Set<String> supplied = new HashSet<>();
        List<PrivacyStateDto> result = new ArrayList<>();
        for (PrivacyStateDto value : requested) {
            if (value == null || value.getName() == null) {
                result.add(value);
                continue;
            }
            String key = value.getName().toLowerCase(Locale.ROOT);
            supplied.add(key);
            PrivacyStateDto fallback = defaultsByName.get(key);
            String privacy = normalizeOptionalValue(value.getPrivacy()) != null
                    ? value.getPrivacy().trim().toLowerCase(Locale.ROOT)
                    : fallback == null ? value.getPrivacy() : fallback.getPrivacy();
            String name = fallback == null ? value.getName() : fallback.getName();
            result.add(new PrivacyStateDto(name, privacy));
            if (fallback != null && normalizeOptionalValue(value.getPrivacy()) == null) {
                defaultsApplied.add("privacies." + fallback.getName() + ".privacy");
            }
        }
        for (Map.Entry<String, PrivacyStateDto> entry : defaultsByName.entrySet()) {
            if (!supplied.contains(entry.getKey())) {
                result.add(entry.getValue());
                defaultsApplied.add("privacies." + entry.getValue().getName());
            }
        }
        return result;
    }

    private List<VariableStateDto> defaultLocalVariables(DeviceManifest manifest) {
        if (manifest == null || manifest.getInternalVariables() == null) return List.of();
        List<VariableStateDto> result = new ArrayList<>();
        for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
            if (variable == null || !Boolean.TRUE.equals(variable.getIsInside())
                    || variable.getName() == null || variable.getName().isBlank()) continue;
            String value = null;
            if (variable.getValues() != null && !variable.getValues().isEmpty()) {
                value = variable.getValues().get(0);
            } else if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
                value = String.valueOf(variable.getLowerBound());
            }
            if (value != null) {
                result.add(new VariableStateDto(variable.getName(), value, normalizeTrust(variable.getTrust())));
            }
        }
        return result;
    }

    private List<PrivacyStateDto> defaultLocalPrivacies(DeviceManifest manifest) {
        if (manifest == null || manifest.getInternalVariables() == null) return List.of();
        LinkedHashMap<String, PrivacyStateDto> result = new LinkedHashMap<>();
        for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
            if (variable != null && Boolean.TRUE.equals(variable.getIsInside())
                    && variable.getName() != null && !variable.getName().isBlank()) {
                result.put(variable.getName(),
                        new PrivacyStateDto(variable.getName(), normalizePrivacy(variable.getPrivacy())));
            }
        }
        return new ArrayList<>(result.values());
    }

    private String normalizeTrust(String value) {
        return "untrusted".equalsIgnoreCase(normalizeOptionalValue(value)) ? "untrusted" : "trusted";
    }

    private String normalizePrivacy(String value) {
        return "private".equalsIgnoreCase(normalizeOptionalValue(value)) ? "private" : "public";
    }

    private InitialStateResolution fallbackState(String templateName) {
        return new InitialStateResolution(
                HARD_FALLBACK_STATE,
                "systemFallback",
                "Template '" + templateName + "' has no usable initial state; system fallback '"
                        + HARD_FALLBACK_STATE + "' was applied."
        );
    }

    private record InitialStateResolution(String state, String source, String warning) {
    }
}
