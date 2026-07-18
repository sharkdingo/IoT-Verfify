package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardSemanticSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.board.CollectionMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariablePatchResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeUpdateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceUpdateResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateAffectedDeviceDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetBlockerDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetChangeDto;
import cn.edu.nju.Iot_Verify.dto.device.DefaultTemplateResetResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceMutationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionBlockerDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BoardReplacementStaleException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.exception.TemplateDeletionConflictException;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;
import cn.edu.nju.Iot_Verify.util.EnvironmentDomainUtils;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.po.*;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.util.RuleSemanticSignature;
import cn.edu.nju.Iot_Verify.util.SmvConstants;
import cn.edu.nju.Iot_Verify.util.SpecificationSemanticSignature;
import cn.edu.nju.Iot_Verify.util.SpecificationFormulaPreview;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import cn.edu.nju.Iot_Verify.util.mapper.BoardLayoutMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceTemplateMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

@Slf4j
@Service
@RequiredArgsConstructor
public class BoardStorageServiceImpl implements BoardStorageService {

    private final DeviceNodeRepository nodeRepo;
    private final BoardEnvironmentVariableRepository environmentRepo;
    private final SpecificationRepository specRepo;
    private final RuleRepository ruleRepo;
    private final BoardLayoutRepository layoutRepo;
    private final DeviceTemplateRepository deviceTemplateRepo;
    private final DeviceTemplateService deviceTemplateService;
    private final TransactionTemplate transactionTemplate;
    private final SmvGenerator smvGenerator;
    private final SpecificationMapper specificationMapper;
    private final RuleMapper ruleMapper;
    private final DeviceNodeMapper deviceNodeMapper;
    private final BoardLayoutMapper boardLayoutMapper;
    private final DeviceTemplateMapper deviceTemplateMapper;
    private final DeviceTemplateSchemaValidator deviceTemplateSchemaValidator;
    private final UserRepository userRepository;

    /**
     * The in-process user lock prevents same-instance read-modify-write races. Every write
     * transaction then acquires the user's database row with findByIdForUpdate, which serializes
     * the same user's writes across application instances as well.
     *
     * Uses striped locks (fixed-size array) to bound memory while preserving correctness:
     * - 1024 lock stripes (sufficient for most deployments, ~4KB memory overhead)
     * - userId % stripes → deterministic lock assignment
     * - No eviction → same userId always maps to same lock (correctness preserved)
     */
    private static final int LOCK_STRIPES = 1024;
    private final Object[] userWriteLocks = new Object[LOCK_STRIPES];
    {
        for (int i = 0; i < LOCK_STRIPES; i++) {
            userWriteLocks[i] = new Object();
        }
    }

    private Object getUserWriteLock(Long userId) {
        int stripe = Math.abs((int) (userId % LOCK_STRIPES));
        return userWriteLocks[stripe];
    }

    private void requireActiveUserForWrite(Long userId) {
        if (userId == null || userRepository.findByIdForUpdate(userId).isEmpty()) {
            throw UnauthorizedException.invalidToken();
        }
    }

    @Override
    @Transactional(readOnly = true)
    public List<DeviceNodeDto> getNodes(Long userId) {
        return nodeRepo.findByUserId(userId).stream()
                .map(deviceNodeMapper::toDto)
                .toList();
    }

    @Override
    public BoardSemanticSnapshotDto getSemanticSnapshot(Long userId) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                return getSemanticSnapshotInternal(userId);
            });
        }
    }

    /** Package-private full replacement used by semantic precheck tests; not an external service contract. */
    List<DeviceNodeDto> saveNodes(Long userId, List<DeviceNodeDto> nodes) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, nodes);
                validateBoardReferences(userId, canonicalNodes, getRulesInternal(userId), getSpecsInternal(userId));
                return saveNodesInternal(userId, canonicalNodes);
            });
        }
    }

    @Override
    public DeviceMutationResultDto addNodes(Long userId,
                                            List<DeviceNodeDto> nodes,
                                            List<BoardEnvironmentVariableDto> environmentVariablePatches) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                if (nodes == null || nodes.isEmpty()) {
                    throw new BadRequestException("At least one device is required");
                }

                List<DeviceNodeDto> current = new ArrayList<>(getNodesInternal(userId));
                List<BoardEnvironmentVariableDto> previousEnvironment = getEnvironmentVariablesInternal(userId);
                List<DeviceNodeDto> next = new ArrayList<>(current);
                next.addAll(nodes);
                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, next);
                List<RuleDto> currentRules = getRulesInternal(userId);
                List<SpecificationDto> currentSpecs = getSpecsInternal(userId);
                validateBoardReferences(userId, canonicalNodes, currentRules, currentSpecs);

                List<DeviceNodeDto> savedNodes = saveNodesInternal(userId, canonicalNodes);
                List<BoardEnvironmentVariableDto> savedEnvironment = environmentVariablePatches != null
                        && !environmentVariablePatches.isEmpty()
                        ? patchEnvironmentVariablesInternal(
                                userId, savedNodes, environmentVariablePatches).getEnvironmentVariables()
                        : getEnvironmentVariablesInternal(userId);
                Set<String> createdIds = nodes.stream()
                        .map(DeviceNodeDto::getId)
                        .filter(Objects::nonNull)
                        .collect(Collectors.toCollection(LinkedHashSet::new));
                List<DeviceNodeDto> created = savedNodes.stream()
                        .filter(node -> createdIds.contains(node.getId()))
                        .toList();

                return DeviceMutationResultDto.builder()
                        .operation("created")
                        .affectedDevices(created)
                        .currentNodes(savedNodes)
                        .environmentVariables(savedEnvironment)
                        .environmentChanges(diffEnvironmentVariables(previousEnvironment, savedEnvironment))
                        .currentSpecifications(currentSpecs)
                        .currentCount(savedNodes.size())
                        .build();
            });
        }
    }

    @Override
    public DeviceUpdateResultDto updateNodeLayout(Long userId, String nodeId, DeviceLayoutDto layout) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                String targetId = trimToNull(nodeId);
                if (targetId == null || layout == null) {
                    throw new BadRequestException("Device id and layout are required");
                }
                validateDeviceLayout(layout);
                List<DeviceNodeDto> current = new ArrayList<>(getNodesInternal(userId));
                int index = indexOfNode(current, targetId);
                if (index < 0) {
                    throw new ResourceNotFoundException("Device", targetId);
                }
                DeviceNodeDto previous = copyDeviceNode(current.get(index));
                DeviceNodeDto next = copyDeviceNode(previous);
                next.setPosition(copyPosition(layout.getPosition()));
                next.setWidth(layout.getWidth());
                next.setHeight(layout.getHeight());
                return persistTargetedNodeUpdate(userId, current, index, previous, next, "layout");
            });
        }
    }

    @Override
    public DeviceUpdateResultDto updateNodeRuntime(
            Long userId, String nodeId, DeviceRuntimeUpdateDto runtime) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                String targetId = trimToNull(nodeId);
                if (targetId == null || runtime == null) {
                    throw new BadRequestException("Device id and runtime configuration are required");
                }
                List<DeviceNodeDto> current = new ArrayList<>(getNodesInternal(userId));
                int index = indexOfNode(current, targetId);
                if (index < 0) {
                    throw new ResourceNotFoundException("Device", targetId);
                }
                DeviceNodeDto previous = copyDeviceNode(current.get(index));
                DeviceNodeDto next = copyDeviceNode(previous);
                next.setState(trimToNull(runtime.getState()));
                next.setCurrentStateTrust(trimToNull(runtime.getCurrentStateTrust()));
                next.setCurrentStatePrivacy(trimToNull(runtime.getCurrentStatePrivacy()));
                next.setVariables(copyVariables(runtime.getVariables()));
                next.setPrivacies(copyPrivacies(runtime.getPrivacies()));
                current.set(index, next);

                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, current);
                validateBoardReferences(
                        userId, canonicalNodes, getRulesInternal(userId), getSpecsInternal(userId));
                DeviceNodeDto canonicalNext = requireNode(canonicalNodes, targetId);
                return persistTargetedNodeUpdate(
                        userId, current, index, previous, canonicalNext, "runtime");
            });
        }
    }

    @Override
    public DeviceMutationResultDto renameNode(Long userId, String nodeId, String newLabel) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                String targetId = trimToNull(nodeId);
                String label = trimToNull(newLabel);
                if (targetId == null || label == null) {
                    throw new BadRequestException("Device id and name are required");
                }

                List<DeviceNodeDto> currentNodes = new ArrayList<>(getNodesInternal(userId));
                List<BoardEnvironmentVariableDto> previousEnvironment = getEnvironmentVariablesInternal(userId);
                DeviceNodeDto target = requireNode(currentNodes, targetId);
                String previousLabel = target.getLabel();
                target.setLabel(label);

                List<RuleDto> currentRules = getRulesInternal(userId);
                List<SpecificationDto> currentSpecs = new ArrayList<>(getSpecsInternal(userId));
                int updatedSpecCount = updateSpecificationDeviceLabels(currentSpecs, targetId, label);
                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, currentNodes);
                validateBoardReferences(userId, canonicalNodes, currentRules, currentSpecs);

                List<DeviceNodeDto> savedNodes = saveNodesInternal(userId, canonicalNodes);
                List<SpecificationDto> savedSpecs = updatedSpecCount > 0
                        ? saveSpecsInternal(userId, currentSpecs, savedNodes)
                        : currentSpecs;
                DeviceNodeDto renamed = requireNode(savedNodes, targetId);
                List<BoardEnvironmentVariableDto> savedEnvironment = getEnvironmentVariablesInternal(userId);
                return DeviceMutationResultDto.builder()
                        .operation("renamed")
                        .affectedDevices(List.of(renamed))
                        .currentNodes(savedNodes)
                        .environmentVariables(savedEnvironment)
                        .environmentChanges(diffEnvironmentVariables(previousEnvironment, savedEnvironment))
                        .currentSpecifications(savedSpecs)
                        .previousLabel(previousLabel)
                        .updatedSpecificationCount(updatedSpecCount)
                        .currentCount(savedNodes.size())
                        .build();
            });
        }
    }

    @Override
    public DeviceDeletionResultDto previewNodeDeletion(Long userId, String nodeId) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                String targetId = trimToNull(nodeId);
                if (targetId == null) {
                    throw new BadRequestException("Device id is required");
                }

                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                DeviceNodeDto target = requireNode(currentNodes, targetId);
                List<RuleDto> currentRules = getRulesInternal(userId);
                List<SpecificationDto> currentSpecs = getSpecsInternal(userId);
                List<BoardEnvironmentVariableDto> currentEnvironment = getEnvironmentVariablesInternal(userId);
                List<DeviceNodeDto> projectedNodes = currentNodes.stream()
                        .filter(node -> !targetId.equals(node.getId()))
                        .toList();
                List<BoardEnvironmentVariableDto> projectedEnvironment =
                        projectEnvironmentVariablesForNodes(userId, projectedNodes);
                List<RuleDto> removedRules = currentRules.stream()
                        .filter(rule -> ruleReferencesNode(rule, targetId))
                        .toList();
                List<SpecificationDto> removedSpecifications = currentSpecs.stream()
                        .filter(spec -> specificationReferencesNode(spec, targetId))
                        .toList();
                List<EnvironmentVariableChangeDto> environmentChanges =
                        diffEnvironmentVariables(currentEnvironment, projectedEnvironment);

                return DeviceDeletionResultDto.builder()
                        .operation("preview")
                        .impactToken(deletionImpactToken(
                                target, removedRules, removedSpecifications, environmentChanges))
                        .deletedDevice(target)
                        .removedRules(removedRules)
                        .removedSpecifications(removedSpecifications)
                        .currentNodes(currentNodes)
                        .environmentVariables(currentEnvironment)
                        .environmentChanges(environmentChanges)
                        .currentRules(currentRules)
                        .currentSpecifications(currentSpecs)
                        .build();
            });
        }
    }

    @Override
    public DeviceDeletionResultDto deleteNodeCascade(Long userId,
                                                     String nodeId,
                                                     String expectedImpactToken) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                String targetId = trimToNull(nodeId);
                if (targetId == null) {
                    throw new BadRequestException("Device id is required");
                }

                List<DeviceNodeDto> currentNodes = new ArrayList<>(getNodesInternal(userId));
                List<BoardEnvironmentVariableDto> previousEnvironment = getEnvironmentVariablesInternal(userId);
                DeviceNodeDto deleted = requireNode(currentNodes, targetId);
                currentNodes.removeIf(node -> targetId.equals(node.getId()));

                List<RuleDto> currentRules = getRulesInternal(userId);
                List<RuleDto> removedRules = currentRules.stream()
                        .filter(rule -> ruleReferencesNode(rule, targetId))
                        .toList();
                List<RuleDto> nextRules = currentRules.stream()
                        .filter(rule -> !ruleReferencesNode(rule, targetId))
                        .toList();

                List<SpecificationDto> currentSpecs = getSpecsInternal(userId);
                List<SpecificationDto> removedSpecs = currentSpecs.stream()
                        .filter(spec -> specificationReferencesNode(spec, targetId))
                        .toList();
                List<SpecificationDto> nextSpecs = currentSpecs.stream()
                        .filter(spec -> !specificationReferencesNode(spec, targetId))
                        .toList();

                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, currentNodes);
                validateBoardReferences(userId, canonicalNodes, nextRules, nextSpecs);
                List<BoardEnvironmentVariableDto> projectedEnvironment =
                        projectEnvironmentVariablesForNodes(userId, canonicalNodes);
                List<EnvironmentVariableChangeDto> projectedEnvironmentChanges =
                        diffEnvironmentVariables(previousEnvironment, projectedEnvironment);
                String actualImpactToken = deletionImpactToken(
                        deleted, removedRules, removedSpecs, projectedEnvironmentChanges);
                if (!hasText(expectedImpactToken)
                        || !MessageDigest.isEqual(
                                actualImpactToken.getBytes(StandardCharsets.UTF_8),
                                expectedImpactToken.trim().getBytes(StandardCharsets.UTF_8))) {
                    throw new ConflictException(
                            "Device deletion impact changed after confirmation; review a fresh preview before deleting.");
                }
                List<DeviceNodeDto> savedNodes = saveNodesInternal(userId, canonicalNodes);
                List<RuleDto> savedRules = saveRulesInternal(userId, nextRules);
                List<SpecificationDto> savedSpecs = saveSpecsInternal(userId, nextSpecs, savedNodes);
                List<BoardEnvironmentVariableDto> savedEnvironment = getEnvironmentVariablesInternal(userId);

                return DeviceDeletionResultDto.builder()
                        .operation("deleted")
                        .impactToken(actualImpactToken)
                        .deletedDevice(deleted)
                        .removedRules(removedRules)
                        .removedSpecifications(removedSpecs)
                        .currentNodes(savedNodes)
                        .environmentVariables(savedEnvironment)
                        .environmentChanges(diffEnvironmentVariables(previousEnvironment, savedEnvironment))
                        .currentRules(savedRules)
                        .currentSpecifications(savedSpecs)
                        .build();
            });
        }
    }

    private int indexOfNode(List<DeviceNodeDto> nodes, String nodeId) {
        for (int index = 0; index < nodes.size(); index++) {
            DeviceNodeDto node = nodes.get(index);
            if (node != null && nodeId.equals(node.getId())) {
                return index;
            }
        }
        return -1;
    }

    private void validateDeviceLayout(DeviceLayoutDto layout) {
        Map<String, String> errors = new LinkedHashMap<>();
        DeviceNodeDto.Position position = layout.getPosition();
        Double x = position != null ? position.getX() : null;
        Double y = position != null ? position.getY() : null;
        if (x == null || !Double.isFinite(x) || Math.abs(x) > DeviceLayoutDto.MAX_ABS_POSITION) {
            errors.put("position.x", "X coordinate must be finite and within -1000000..1000000");
        }
        if (y == null || !Double.isFinite(y) || Math.abs(y) > DeviceLayoutDto.MAX_ABS_POSITION) {
            errors.put("position.y", "Y coordinate must be finite and within -1000000..1000000");
        }
        if (layout.getWidth() == null || layout.getWidth() < DeviceLayoutDto.MIN_WIDTH
                || layout.getWidth() > DeviceLayoutDto.MAX_WIDTH) {
            errors.put("width", "Width must be within 80..2000");
        }
        if (layout.getHeight() == null || layout.getHeight() < DeviceLayoutDto.MIN_HEIGHT
                || layout.getHeight() > DeviceLayoutDto.MAX_HEIGHT) {
            errors.put("height", "Height must be within 60..2000");
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private DeviceUpdateResultDto persistTargetedNodeUpdate(
            Long userId,
            List<DeviceNodeDto> current,
            int index,
            DeviceNodeDto previous,
            DeviceNodeDto requested,
            String mutationType) {
        List<String> changedFields = changedDeviceUpdateFields(previous, requested, mutationType);
        DeviceNodeDto saved = previous;
        if (!changedFields.isEmpty()) {
            DeviceNodePo entity = nodeRepo.findById(new DeviceNodeId(previous.getId(), userId))
                    .orElseThrow(() -> new ResourceNotFoundException("Device", previous.getId()));
            if ("layout".equals(mutationType)) {
                entity.setPosX(requested.getPosition().getX());
                entity.setPosY(requested.getPosition().getY());
                entity.setWidth(requested.getWidth());
                entity.setHeight(requested.getHeight());
            } else {
                DeviceNodePo runtimeValues = Objects.requireNonNull(
                        deviceNodeMapper.toEntity(requested, userId),
                        "device runtime patch entity must not be null");
                entity.setState(runtimeValues.getState());
                entity.setCurrentStateTrust(runtimeValues.getCurrentStateTrust());
                entity.setCurrentStatePrivacy(runtimeValues.getCurrentStatePrivacy());
                entity.setVariablesJson(runtimeValues.getVariablesJson());
                entity.setPrivaciesJson(runtimeValues.getPrivaciesJson());
            }
            saved = Objects.requireNonNull(
                    deviceNodeMapper.toDto(nodeRepo.save(entity)), "saved device patch must not be null");
            changedFields = changedDeviceUpdateFields(previous, saved, mutationType);
        }
        current.set(index, saved);
        return DeviceUpdateResultDto.builder()
                .operation(changedFields.isEmpty() ? "unchanged" : "updated")
                .mutationType(mutationType)
                .changedFields(changedFields)
                .previousDevice(previous)
                .currentDevice(saved)
                .currentNodes(List.copyOf(current))
                .currentCount(current.size())
                .build();
    }

    private List<String> changedDeviceUpdateFields(
            DeviceNodeDto previous, DeviceNodeDto current, String mutationType) {
        List<String> fields = new ArrayList<>();
        if ("layout".equals(mutationType)) {
            DeviceNodeDto.Position before = previous != null ? previous.getPosition() : null;
            DeviceNodeDto.Position after = current != null ? current.getPosition() : null;
            if (!Objects.equals(before != null ? before.getX() : null, after != null ? after.getX() : null)) {
                fields.add("position.x");
            }
            if (!Objects.equals(before != null ? before.getY() : null, after != null ? after.getY() : null)) {
                fields.add("position.y");
            }
            if (!Objects.equals(previous != null ? previous.getWidth() : null,
                    current != null ? current.getWidth() : null)) {
                fields.add("width");
            }
            if (!Objects.equals(previous != null ? previous.getHeight() : null,
                    current != null ? current.getHeight() : null)) {
                fields.add("height");
            }
        } else {
            if (!Objects.equals(previous != null ? previous.getState() : null,
                    current != null ? current.getState() : null)) {
                fields.add("state");
            }
            if (!Objects.equals(previous != null ? previous.getCurrentStateTrust() : null,
                    current != null ? current.getCurrentStateTrust() : null)) {
                fields.add("currentStateTrust");
            }
            if (!Objects.equals(previous != null ? previous.getCurrentStatePrivacy() : null,
                    current != null ? current.getCurrentStatePrivacy() : null)) {
                fields.add("currentStatePrivacy");
            }
            if (!Objects.equals(
                    previous != null ? safeList(previous.getVariables()) : List.of(),
                    current != null ? safeList(current.getVariables()) : List.of())) {
                fields.add("variables");
            }
            if (!Objects.equals(
                    previous != null ? safeList(previous.getPrivacies()) : List.of(),
                    current != null ? safeList(current.getPrivacies()) : List.of())) {
                fields.add("privacies");
            }
        }
        return List.copyOf(fields);
    }

    private DeviceNodeDto copyDeviceNode(DeviceNodeDto source) {
        DeviceNodeDto copy = new DeviceNodeDto();
        copy.setId(source.getId());
        copy.setTemplateName(source.getTemplateName());
        copy.setLabel(source.getLabel());
        copy.setPosition(copyPosition(source.getPosition()));
        copy.setState(source.getState());
        copy.setWidth(source.getWidth());
        copy.setHeight(source.getHeight());
        copy.setCurrentStateTrust(source.getCurrentStateTrust());
        copy.setCurrentStatePrivacy(source.getCurrentStatePrivacy());
        copy.setVariables(copyVariables(source.getVariables()));
        copy.setPrivacies(copyPrivacies(source.getPrivacies()));
        return copy;
    }

    private DeviceNodeDto.Position copyPosition(DeviceNodeDto.Position source) {
        if (source == null) return null;
        DeviceNodeDto.Position copy = new DeviceNodeDto.Position();
        copy.setX(source.getX());
        copy.setY(source.getY());
        return copy;
    }

    private List<VariableStateDto> copyVariables(List<VariableStateDto> values) {
        if (values == null) return null;
        return values.stream()
                .map(value -> value == null ? null : new VariableStateDto(
                        value.getName(), value.getValue(), value.getTrust()))
                .toList();
    }

    private List<PrivacyStateDto> copyPrivacies(List<PrivacyStateDto> values) {
        if (values == null) return null;
        return values.stream()
                .map(value -> value == null ? null : new PrivacyStateDto(
                        value.getName(), value.getPrivacy()))
                .toList();
    }

    private DeviceNodeDto requireNode(List<DeviceNodeDto> nodes, String nodeId) {
        int index = indexOfNode(nodes, nodeId);
        if (index < 0) {
            throw new ResourceNotFoundException("Device", nodeId);
        }
        return nodes.get(index);
    }

    private int updateSpecificationDeviceLabels(List<SpecificationDto> specs,
                                                String nodeId,
                                                String newLabel) {
        int updated = 0;
        for (SpecificationDto spec : specs) {
            boolean changed = updateConditionLabels(spec.getAConditions(), nodeId, newLabel)
                    | updateConditionLabels(spec.getIfConditions(), nodeId, newLabel)
                    | updateConditionLabels(spec.getThenConditions(), nodeId, newLabel);
            for (SpecificationDto.DeviceRefDto ref : safeList(spec.getDevices())) {
                if (ref != null && nodeId.equals(ref.getDeviceId())
                        && !Objects.equals(newLabel, ref.getDeviceLabel())) {
                    ref.setDeviceLabel(newLabel);
                    changed = true;
                }
            }
            if (changed) updated++;
        }
        return updated;
    }

    private boolean updateConditionLabels(List<SpecConditionDto> conditions,
                                          String nodeId,
                                          String newLabel) {
        boolean changed = false;
        for (SpecConditionDto condition : safeList(conditions)) {
            if (condition != null && nodeId.equals(condition.getDeviceId())
                    && !Objects.equals(newLabel, condition.getDeviceLabel())) {
                condition.setDeviceLabel(newLabel);
                changed = true;
            }
        }
        return changed;
    }

    private boolean ruleReferencesNode(RuleDto rule, String nodeId) {
        if (rule == null) return false;
        RuleDto.Command command = rule.getCommand();
        if (command != null && (nodeId.equals(command.getDeviceName())
                || nodeId.equals(command.getContentDevice()))) {
            return true;
        }
        return safeList(rule.getConditions()).stream()
                .anyMatch(condition -> condition != null && nodeId.equals(condition.getDeviceName()));
    }

    private boolean specificationReferencesNode(SpecificationDto spec, String nodeId) {
        if (spec == null) return false;
        if (safeList(spec.getDevices()).stream()
                .anyMatch(ref -> ref != null && nodeId.equals(ref.getDeviceId()))) {
            return true;
        }
        return Stream.of(spec.getAConditions(), spec.getIfConditions(), spec.getThenConditions())
                .flatMap(conditions -> safeList(conditions).stream())
                .anyMatch(condition -> condition != null && nodeId.equals(condition.getDeviceId()));
    }

    private <T> List<T> safeList(List<T> values) {
        return values != null ? values : List.of();
    }

    @Override
    public List<BoardEnvironmentVariableDto> getEnvironmentVariables(Long userId) {
        if (environmentRepo == null) {
            return List.of();
        }
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                return refreshEnvironmentVariablesInternal(userId, currentNodes);
            });
        }
    }

    @Override
    public EnvironmentMutationResultDto saveEnvironmentVariables(
            Long userId,
            List<BoardEnvironmentVariableDto> variables) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                return patchEnvironmentVariablesInternal(userId, currentNodes, variables);
            });
        }
    }

    @Override
    public List<BoardEnvironmentVariableDto> updateEnvironmentVariables(
            Long userId,
            java.util.function.UnaryOperator<List<BoardEnvironmentVariableDto>> mutator) {
        Objects.requireNonNull(mutator, "environment mutator must not be null");
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                List<BoardEnvironmentVariableDto> current = new ArrayList<>(
                        refreshEnvironmentVariablesInternal(userId, currentNodes));
                List<BoardEnvironmentVariableDto> mutated = mutator.apply(current);
                List<BoardEnvironmentVariableDto> next = mutated != null ? mutated : current;
                return saveEnvironmentVariablesInternal(userId, currentNodes, next, true);
            });
        }
    }

    @Override
    public DeviceMutationResultDto createNode(
            Long userId,
            java.util.function.Function<List<DeviceNodeDto>, DeviceNodeDto> nodeFactory) {
        Objects.requireNonNull(nodeFactory, "node factory must not be null");
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> current = new ArrayList<>(getNodesInternal(userId));
                List<BoardEnvironmentVariableDto> previousEnvironment = getEnvironmentVariablesInternal(userId);
                DeviceNodeDto createdDraft = Objects.requireNonNull(
                        nodeFactory.apply(List.copyOf(current)), "node factory result must not be null");
                List<DeviceNodeDto> nextNodes = new ArrayList<>(current);
                nextNodes.add(createdDraft);
                List<DeviceNodeDto> canonicalNodes = canonicalizeNodeTemplateNames(userId, nextNodes);
                List<RuleDto> currentRules = getRulesInternal(userId);
                List<SpecificationDto> currentSpecs = getSpecsInternal(userId);
                validateBoardReferences(userId, canonicalNodes, currentRules, currentSpecs);
                List<DeviceNodeDto> savedNodes = saveNodesInternal(userId, canonicalNodes);
                List<BoardEnvironmentVariableDto> savedEnvironment = getEnvironmentVariablesInternal(userId);
                DeviceNodeDto created = requireNode(savedNodes, createdDraft.getId());
                return DeviceMutationResultDto.builder()
                        .operation("created")
                        .affectedDevices(List.of(created))
                        .currentNodes(savedNodes)
                        .environmentVariables(savedEnvironment)
                        .environmentChanges(diffEnvironmentVariables(previousEnvironment, savedEnvironment))
                        .currentSpecifications(currentSpecs)
                        .currentCount(savedNodes.size())
                        .build();
            });
        }
    }

    /** Lock-free/transaction-free node save; safe to call inside transactionTemplate lambdas. */
    private List<DeviceNodeDto> saveNodesInternal(Long userId, List<DeviceNodeDto> nodes) {
        nodeRepo.deleteByUserId(userId);
        List<DeviceNodePo> pos = nodes.stream()
                .map(dto -> deviceNodeMapper.toEntity(dto, userId))
                .toList();
        List<DeviceNodePo> saved = nodeRepo.saveAll(Objects.requireNonNull(pos, "nodes to save must not be null"));
        syncEnvironmentPoolForNodes(userId, nodes);
        return saved.stream().map(deviceNodeMapper::toDto).toList();
    }

    @Override
    @Transactional(readOnly = true)
    public List<SpecificationDto> getSpecs(Long userId) {
        return getSpecsInternal(userId);
    }

    /** Non-transactional read; safe to call inside transactionTemplate lambdas. */
    private List<SpecificationDto> getSpecsInternal(Long userId) {
        return specRepo.findByUserId(userId).stream()
                .map(specificationMapper::toDto)
                .toList();
    }

    @Override
    public CollectionMutationResultDto<SpecificationDto> addSpec(Long userId, SpecificationDto spec) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                List<SpecificationDto> existing = new ArrayList<>(getSpecsInternal(userId));
                existing.add(spec);
                validateBoardReferences(userId, currentNodes, null, existing);
                List<SpecificationDto> saved = saveSpecsInternal(userId, existing, currentNodes);
                SpecificationDto created = saved.stream()
                        .filter(candidate -> Objects.equals(candidate.getId(), spec.getId()))
                        .findFirst()
                        .orElse(spec);
                return CollectionMutationResultDto.of("created", created, saved);
            });
        }
    }

    @Override
    public CollectionMutationResultDto<SpecificationDto> removeSpec(Long userId, String specId) {
        return removeSpecIfUnchanged(userId, specId, null);
    }

    @Override
    public CollectionMutationResultDto<SpecificationDto> removeSpecIfUnchanged(
            Long userId, String specId, SpecificationDto expected) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                List<SpecificationDto> existing = new ArrayList<>(getSpecsInternal(userId));
                SpecificationDto removed = existing.stream()
                        .filter(candidate -> specId.equals(candidate.getId()))
                        .findFirst()
                        .orElseThrow(() -> new ResourceNotFoundException("Specification", specId));
                if (expected != null && !Objects.equals(expected, removed)) {
                    throw new ConflictException(
                            "The specification changed after confirmation. Review the current specification before deleting it.");
                }
                existing.removeIf(candidate -> specId.equals(candidate.getId()));
                List<SpecificationDto> saved = saveSpecsInternal(userId, existing, currentNodes);
                return CollectionMutationResultDto.of("deleted", removed, saved);
            });
        }
    }

    /** Internal save without re-acquiring the lock. */
    private List<SpecificationDto> saveSpecsInternal(Long userId,
                                                     List<SpecificationDto> specs,
                                                     List<DeviceNodeDto> nodes) {
        validateNoIdenticalSpecifications(specs, nodes);
        specRepo.deleteByUserId(userId);
        SpecificationFormulaPreview.Context previewContext = SpecificationFormulaPreview.context(
                nodes,
                deviceTemplateRepo.findByUserId(userId).stream()
                        .map(deviceTemplateMapper::toDto)
                        .toList());
        List<SpecificationPo> pos = new ArrayList<>(specs.size());
        for (int listOrder = 0; listOrder < specs.size(); listOrder++) {
            SpecificationDto canonical = canonicalizeSpecificationForStorage(
                    specs.get(listOrder), previewContext);
            SpecificationPo po = specificationMapper.toEntity(canonical, userId);
            po.setListOrder(listOrder);
            pos.add(po);
        }
        specRepo.saveAll(Objects.requireNonNull(pos, "specs to save must not be null"));
        return pos.stream()
                .map(specificationMapper::toDto)
                .toList();
    }

    @Override
    @Transactional(readOnly = true)
    public List<RuleDto> getRules(Long userId) {
        return getRulesInternal(userId);
    }

    /** Non-transactional read; safe to call inside transactionTemplate lambdas. */
    private List<RuleDto> getRulesInternal(Long userId) {
        // This order is user-controlled model semantics, not incidental database iteration order.
        return ruleRepo.findByUserIdOrderByExecutionOrderAscIdAsc(userId).stream()
                .map(ruleMapper::toDto)
                .toList();
    }

    @Override
    public List<RuleDto> updateRulesAgainstSnapshot(
            Long userId,
            java.util.function.Function<BoardSemanticSnapshotDto, List<RuleDto>> mutator) {
        Objects.requireNonNull(mutator, "rule snapshot mutator must not be null");
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                BoardSemanticSnapshotDto snapshot = getSemanticSnapshotInternal(userId);
                List<RuleDto> next = Objects.requireNonNull(
                        mutator.apply(snapshot), "rule snapshot mutator result must not be null");
                validateBoardReferences(
                        userId,
                        snapshot.nodes(),
                        next,
                        snapshot.specifications(),
                        templateManifestMap(snapshot.deviceTemplates()));
                return saveRulesInternal(userId, next);
            });
        }
    }

    /**
     * Lock-free/transaction-free identity-preserving full-list rule save.
     * Existing ids in the request are updated in place; missing existing ids are deleted.
     */
    private List<RuleDto> saveRulesInternal(Long userId, List<RuleDto> rules) {
        validateNoIdenticalRules(rules, getNodesInternal(userId));
        // Read existing rules so surviving ids keep createdAt and omitted ids can be deleted.
        Map<Long, RulePo> existingRules = ruleRepo.findByUserId(userId).stream()
                .collect(Collectors.toMap(RulePo::getId, r -> r));

        // Rule ids present in this complete desired rule list.
        Set<Long> newRuleIds = new HashSet<>();

        for (int executionOrder = 0; executionOrder < rules.size(); executionOrder++) {
            RuleDto r = rules.get(executionOrder);
            Long ruleId = r.getId();
            if (ruleId != null) {
                newRuleIds.add(ruleId);
            }

            RuleDto canonicalRule = canonicalizeRuleRelationsForStorage(r);
            RulePo po = ruleMapper.toEntity(canonicalRule, userId);
            po.setExecutionOrder(executionOrder);
            if (ruleId == null) {
                ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
            } else if (existingRules.containsKey(ruleId)) {
                po.setId(ruleId);
                po.setCreatedAt(existingRules.get(ruleId).getCreatedAt());
                ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
            } else {
                log.warn("Rule id {} does not belong to user {}, inserting as new rule", ruleId, userId);
                po.setId(null);
                ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
            }
        }

        // Existing rules omitted from the request are intentionally deleted.
        for (Long existingId : existingRules.keySet()) {
            if (!newRuleIds.contains(existingId)) {
                ruleRepo.deleteById(Objects.requireNonNull(existingId, "rule id to delete must not be null"));
            }
        }

        return getRulesInternal(userId);
    }

    private RuleDto canonicalizeRuleRelationsForStorage(RuleDto source) {
        if (source == null) {
            return null;
        }
        RuleDto target = new RuleDto();
        target.setId(source.getId());
        target.setUserId(source.getUserId());
        target.setRuleString(source.getRuleString());
        target.setCreatedAt(source.getCreatedAt());
        if (source.getConditions() == null) {
            target.setConditions(Collections.emptyList());
        } else {
            target.setConditions(source.getConditions().stream()
                    .filter(Objects::nonNull)
                    .map(condition -> RuleDto.Condition.builder()
                            .deviceName(condition.getDeviceName())
                            .attribute(condition.getAttribute())
                            .targetType(canonicalRuleTargetTypeOrOriginal(condition.getTargetType()))
                            .relation(canonicalRelationOrOriginal(condition.getRelation()))
                            .value(condition.getValue())
                            .build())
                    .toList());
        }
        RuleDto.Command command = source.getCommand();
        if (command != null) {
            target.setCommand(RuleDto.Command.builder()
                    .deviceName(command.getDeviceName())
                    .action(command.getAction())
                    .contentDevice(command.getContentDevice())
                    .content(command.getContent())
                    .build());
        }
        return target;
    }

    private SpecificationDto canonicalizeSpecificationForStorage(
            SpecificationDto source,
            SpecificationFormulaPreview.Context previewContext) {
        if (source == null) {
            return null;
        }
        Map<String, String> labelsById = previewContext.labelsById();
        SpecificationDto target = new SpecificationDto();
        target.setId(source.getId());
        target.setTemplateId(source.getTemplateId());
        target.setTemplateLabel(SpecificationFormulaPreview.templateLabel(source.getTemplateId()));
        target.setAConditions(canonicalizeSpecConditionsForStorage(source.getAConditions(), labelsById));
        target.setIfConditions(canonicalizeSpecConditionsForStorage(source.getIfConditions(), labelsById));
        target.setThenConditions(canonicalizeSpecConditionsForStorage(source.getThenConditions(), labelsById));
        target.setDevices(buildSpecificationDeviceRefs(target, labelsById));
        target.setFormula(SpecificationFormulaPreview.format(target, previewContext));
        return target;
    }

    private List<SpecConditionDto> canonicalizeSpecConditionsForStorage(
            List<SpecConditionDto> conditions,
            Map<String, String> labelsById) {
        if (conditions == null) {
            return Collections.emptyList();
        }
        return conditions.stream()
                .filter(Objects::nonNull)
                .map(condition -> {
                    String targetType = canonicalSpecTargetTypeOrOriginal(condition.getTargetType());
                    String relation = canonicalRelationOrOriginal(condition.getRelation());
                    SpecConditionDto copy = new SpecConditionDto();
                    copy.setId(condition.getId());
                    copy.setSide(condition.getSide());
                    copy.setDeviceId(condition.getDeviceId());
                    copy.setDeviceLabel(labelsById.getOrDefault(
                            condition.getDeviceId(), condition.getDeviceLabel()));
                    copy.setTargetType(targetType);
                    copy.setKey(condition.getKey());
                    copy.setPropertyScope(("trust".equals(targetType) || "privacy".equals(targetType))
                            ? normalizePropertyScope(condition.getPropertyScope())
                            : null);
                    copy.setRelation(relation);
                    copy.setValue(canonicalSpecLabelValue(
                            targetType, relation, condition.getValue()));
                    return copy;
                })
                .toList();
    }

    private String canonicalSpecLabelValue(String targetType, String relation, String rawValue) {
        if (!("trust".equals(targetType) || "privacy".equals(targetType)) || !hasText(rawValue)) {
            return rawValue;
        }
        if ("in".equals(relation) || "not in".equals(relation)) {
            return SmvRelationUtils.splitRuleValues(rawValue).stream()
                    .map(value -> value.trim().toLowerCase(Locale.ROOT))
                    .collect(Collectors.joining(", "));
        }
        return rawValue.trim().toLowerCase(Locale.ROOT);
    }

    private List<SpecificationDto.DeviceRefDto> buildSpecificationDeviceRefs(
            SpecificationDto specification,
            Map<String, String> labelsById) {
        Map<String, SpecificationDto.DeviceRefDto> refs = new LinkedHashMap<>();
        for (SpecConditionDto condition : allSpecificationConditions(specification)) {
            if (condition == null || !hasText(condition.getDeviceId())) {
                continue;
            }
            String deviceId = condition.getDeviceId().trim();
            SpecificationDto.DeviceRefDto ref = refs.computeIfAbsent(deviceId,
                    id -> new SpecificationDto.DeviceRefDto(
                            id,
                            labelsById.getOrDefault(id, id),
                            new ArrayList<>()));
            if ("api".equalsIgnoreCase(condition.getTargetType()) && hasText(condition.getKey())
                    && !ref.getSelectedApis().contains(condition.getKey().trim())) {
                ref.getSelectedApis().add(condition.getKey().trim());
            }
        }
        return new ArrayList<>(refs.values());
    }

    private List<SpecConditionDto> allSpecificationConditions(SpecificationDto specification) {
        List<SpecConditionDto> conditions = new ArrayList<>();
        if (specification.getAConditions() != null) conditions.addAll(specification.getAConditions());
        if (specification.getIfConditions() != null) conditions.addAll(specification.getIfConditions());
        if (specification.getThenConditions() != null) conditions.addAll(specification.getThenConditions());
        return conditions;
    }

    private String canonicalRelationOrOriginal(String rawRelation) {
        String normalized = SmvRelationUtils.normalizeRelation(rawRelation);
        return SmvRelationUtils.isSupportedRelation(normalized) ? normalized : rawRelation;
    }

    private String canonicalRuleTargetTypeOrOriginal(String rawTargetType) {
        String normalized = normalizeTargetType(rawTargetType);
        return normalized != null ? normalized : rawTargetType;
    }

    private String canonicalSpecTargetTypeOrOriginal(String rawTargetType) {
        String normalized = normalizeSpecTargetType(rawTargetType);
        return normalized != null ? normalized : rawTargetType;
    }

    @Override
    public BoardReplacementPreviewDto previewBoardReplacement(Long userId) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                return currentBoardReplacementPreview(userId);
            });
        }
    }

    @Override
    public BoardBatchDto saveBoardBatch(Long userId, BoardBatchDto batch) {
        // Atomic save of nodes + environment + rules + specs in ONE transaction under the user write lock.
        // Scene import depends on this so a new topology cannot be persisted with an old environment pool.
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                validateCompleteSceneBatch(batch);
                BoardReplacementPreviewDto currentPreview = currentBoardReplacementPreview(userId);
                if (!hasText(batch.getImpactToken()) || !MessageDigest.isEqual(
                        currentPreview.getImpactToken().getBytes(StandardCharsets.UTF_8),
                        batch.getImpactToken().trim().getBytes(StandardCharsets.UTF_8))) {
                    throw new BoardReplacementStaleException(currentPreview);
                }
                List<DeviceTemplateDto> createdTemplates = batch.getTemplateSnapshots() != null
                        ? resolveSceneTemplateSnapshots(userId, batch.getTemplateSnapshots(), batch.getNodes())
                        : List.of();
                List<DeviceNodeDto> nextNodes = canonicalizeNodeTemplateNames(userId, batch.getNodes());
                List<RuleDto> nextRules = batch.getRules();
                List<SpecificationDto> nextSpecs = batch.getSpecs();
                validateNoIdenticalRules(nextRules, nextNodes);
                validateNoIdenticalSpecifications(nextSpecs, nextNodes);
                validateBoardReferences(userId, nextNodes, nextRules, nextSpecs);
                if (batch.getTemplateSnapshots() != null) {
                    validateCompleteSceneEnvironment(userId, nextNodes, batch.getEnvironmentVariables());
                }

                List<DeviceNodeDto> savedNodes = saveNodesInternal(userId, nextNodes);
                List<BoardEnvironmentVariableDto> savedEnvironment = saveEnvironmentVariablesInternal(
                        userId, savedNodes, batch.getEnvironmentVariables(), batch.getTemplateSnapshots() == null);
                List<RuleDto> savedRules = saveRulesInternal(userId, batch.getRules());
                List<SpecificationDto> savedSpecs = saveSpecsInternal(userId, batch.getSpecs(), savedNodes);
                BoardBatchDto result = new BoardBatchDto(savedNodes, savedEnvironment, savedRules, savedSpecs);
                result.setCreatedTemplates(createdTemplates);
                return result;
            });
        }
    }

    private void validateCompleteSceneBatch(BoardBatchDto batch) {
        Map<String, String> errors = new LinkedHashMap<>();
        if (batch == null) {
            throw new BadRequestException("Complete scene replacement request is required; no board data was changed.");
        }
        if (batch.getNodes() == null) {
            errors.put("nodes", "Scene replacement must explicitly provide the complete nodes collection");
        }
        if (batch.getEnvironmentVariables() == null) {
            errors.put("environmentVariables",
                    "Scene replacement must explicitly provide the complete environmentVariables collection");
        }
        if (batch.getRules() == null) {
            errors.put("rules", "Scene replacement must explicitly provide the complete rules collection");
        }
        if (batch.getSpecs() == null) {
            errors.put("specs", "Scene replacement must explicitly provide the complete specs collection");
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private BoardReplacementPreviewDto currentBoardReplacementPreview(Long userId) {
        List<DeviceNodeDto> nodes = new ArrayList<>(getNodesInternal(userId));
        nodes.sort(Comparator.comparing(
                node -> node == null || node.getId() == null ? "" : node.getId(),
                String.CASE_INSENSITIVE_ORDER));
        List<BoardEnvironmentVariableDto> environmentVariables = getEnvironmentVariablesInternal(userId);
        List<RuleDto> rules = getRulesInternal(userId);
        List<SpecificationDto> specifications = getSpecsInternal(userId);

        Map<String, Object> impact = new LinkedHashMap<>();
        impact.put("contract", "board-replacement-v1");
        impact.put("nodes", nodes);
        impact.put("environmentVariables", environmentVariables);
        impact.put("rules", rules);
        impact.put("specifications", specifications);
        String source = JsonUtils.toJson(impact);
        try {
            String impactToken = HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256")
                    .digest(source.getBytes(StandardCharsets.UTF_8)));
            return BoardReplacementPreviewDto.builder()
                    .impactToken(impactToken)
                    .deviceCount(nodes.size())
                    .environmentVariableCount(environmentVariables.size())
                    .ruleCount(rules.size())
                    .specificationCount(specifications.size())
                    .build();
        } catch (NoSuchAlgorithmException e) {
            throw new InternalServerException("Unable to create board-replacement impact token", e);
        }
    }

    private void validateCompleteSceneEnvironment(Long userId,
                                                  List<DeviceNodeDto> nodes,
                                                  List<BoardEnvironmentVariableDto> variables) {
        Map<String, DeviceManifest> templateManifests = loadTemplateManifestMap(userId);
        Map<String, DeviceManifest.InternalVariable> required = collectRequiredEnvironmentVariables(
                nodes, templateManifests);
        validateSubmittedEnvironmentNames(variables, required);
        validateCompleteEnvironmentSubmission(variables, required);
        validateEnvironmentVariables(variables, required);
    }

    /**
     * Resolve scene-import template dependencies inside the same transaction as the board replacement.
     * A snapshot is never silently ignored: a mismatched existing template is a conflict, and a missing
     * referenced template without a snapshot rejects the whole batch before board collections are saved.
     */
    private List<DeviceTemplateDto> resolveSceneTemplateSnapshots(Long userId,
                                                                    List<DeviceTemplateDto> snapshots,
                                                                    List<DeviceNodeDto> nodes) {
        if (nodes == null) {
            throw new BadRequestException("Scene import requires a complete nodes collection.");
        }
        Map<String, DeviceTemplateDto> snapshotsByAlias = sceneTemplateSnapshotsByAlias(snapshots);
        Map<String, DeviceTemplateDto> existingByAlias = currentTemplatesByAlias(userId);
        Set<String> referencedTemplateNames = new LinkedHashSet<>();
        for (DeviceNodeDto node : nodes == null ? List.<DeviceNodeDto>of() : nodes) {
            if (node != null && hasText(node.getTemplateName())) {
                referencedTemplateNames.add(node.getTemplateName().trim());
            }
        }

        List<DeviceTemplateDto> created = new ArrayList<>();
        Set<DeviceTemplateDto> usedSnapshots = Collections.newSetFromMap(new IdentityHashMap<>());
        for (String requestedName : referencedTemplateNames) {
            String key = templateAliasKey(requestedName);
            DeviceTemplateDto existing = existingByAlias.get(key);
            DeviceTemplateDto snapshot = snapshotsByAlias.get(key);
            if (snapshot == null) {
                throw new BadRequestException("Scene references device template '" + requestedName
                        + "' without a matching template snapshot. Scene files must be self-contained.");
            }
            usedSnapshots.add(snapshot);
            if (existing != null) {
                if (!sameTemplateManifest(existing, snapshot)) {
                    throw new ConflictException("Scene template snapshot does not match the existing template: "
                            + requestedName);
                }
                continue;
            }
            DeviceTemplateDto added = addDeviceTemplate(userId, snapshot);
            created.add(added);
            addTemplateAliases(existingByAlias, added);
        }
        for (DeviceTemplateDto snapshot : snapshots) {
            if (!usedSnapshots.contains(snapshot)) {
                String name = trimToNull(snapshot.getName());
                if (name == null && snapshot.getManifest() != null) {
                    name = trimToNull(snapshot.getManifest().getName());
                }
                throw new BadRequestException("Scene contains an unreferenced template snapshot: "
                        + (name != null ? name : "<unnamed>"));
            }
        }
        return created;
    }

    private Map<String, DeviceTemplateDto> sceneTemplateSnapshotsByAlias(List<DeviceTemplateDto> snapshots) {
        Map<String, DeviceTemplateDto> byAlias = new LinkedHashMap<>();
        for (DeviceTemplateDto snapshot : snapshots == null ? List.<DeviceTemplateDto>of() : snapshots) {
            if (snapshot == null) {
                throw new BadRequestException("Scene template snapshot item cannot be null.");
            }
            String name = trimToNull(snapshot.getName());
            String manifestName = snapshot.getManifest() == null ? null : trimToNull(snapshot.getManifest().getName());
            if (name == null || manifestName == null) {
                throw new BadRequestException(
                        "Scene template snapshot requires both name and manifest.Name.");
            }
            if (!name.equals(manifestName)) {
                throw new BadRequestException("Scene template snapshot name '" + name
                        + "' must exactly match manifest.Name '" + manifestName
                        + "'. Portable scenes cannot rename a template while importing it.");
            }
            addSceneTemplateSnapshotAlias(byAlias, name, snapshot);
        }
        return byAlias;
    }

    private void addSceneTemplateSnapshotAlias(Map<String, DeviceTemplateDto> snapshots,
                                               String alias,
                                               DeviceTemplateDto snapshot) {
        if (!hasText(alias)) {
            return;
        }
        String key = templateAliasKey(alias);
        DeviceTemplateDto previous = snapshots.putIfAbsent(key, snapshot);
        if (previous != null && previous != snapshot && !sameTemplateManifest(previous, snapshot)) {
            throw new BadRequestException("Scene contains conflicting template snapshots for '" + alias + "'.");
        }
    }

    private Map<String, DeviceTemplateDto> currentTemplatesByAlias(Long userId) {
        Map<String, DeviceTemplateDto> byAlias = new LinkedHashMap<>();
        List<DeviceTemplatePo> currentTemplates = deviceTemplateRepo.findByUserId(userId);
        for (DeviceTemplatePo template : currentTemplates == null ? List.<DeviceTemplatePo>of() : currentTemplates) {
            if (template != null) {
                addTemplateAliases(byAlias, deviceTemplateMapper.toDto(template));
            }
        }
        return byAlias;
    }

    private void addTemplateAliases(Map<String, DeviceTemplateDto> aliases, DeviceTemplateDto template) {
        if (template == null) {
            return;
        }
        if (hasText(template.getName())) {
            aliases.putIfAbsent(templateAliasKey(template.getName()), template);
        }
        if (template.getManifest() != null && hasText(template.getManifest().getName())) {
            aliases.putIfAbsent(templateAliasKey(template.getManifest().getName()), template);
        }
    }

    private String templateAliasKey(String value) {
        return value.trim().toLowerCase(Locale.ROOT);
    }

    private boolean sameTemplateManifest(DeviceTemplateDto first, DeviceTemplateDto second) {
        if (first == null || second == null || first.getManifest() == null || second.getManifest() == null) {
            return first == second;
        }
        return Objects.equals(JsonUtils.toJson(first.getManifest()), JsonUtils.toJson(second.getManifest()));
    }

    /** Non-transactional node read; safe to call inside transactionTemplate lambdas. */
    private List<DeviceNodeDto> getNodesInternal(Long userId) {
        return nodeRepo.findByUserId(userId).stream()
                .map(deviceNodeMapper::toDto)
                .toList();
    }

    private BoardSemanticSnapshotDto getSemanticSnapshotInternal(Long userId) {
        return new BoardSemanticSnapshotDto(
                getNodesInternal(userId),
                getEnvironmentVariablesInternal(userId),
                getRulesInternal(userId),
                getSpecsInternal(userId),
                getDeviceTemplatesInternal(userId));
    }

    private List<BoardEnvironmentVariableDto> getEnvironmentVariablesInternal(Long userId) {
        if (environmentRepo == null) {
            return List.of();
        }
        return environmentRepo.findByUserIdOrderByNameAsc(userId).stream()
                .map(this::environmentToDto)
                .toList();
    }

    private BoardEnvironmentVariableDto environmentToDto(BoardEnvironmentVariablePo po) {
        if (po == null) {
            return null;
        }
        return new BoardEnvironmentVariableDto(
                po.getName(),
                po.getValue(),
                po.getTrust(),
                po.getPrivacy()
        );
    }

    private BoardEnvironmentVariablePo environmentToEntity(Long userId, BoardEnvironmentVariableDto dto) {
        return BoardEnvironmentVariablePo.builder()
                .userId(userId)
                .name(trimToNull(dto.getName()))
                .value(trimToNull(dto.getValue()))
                .trust(normalizeTrustPrivacyOrDefault(dto.getTrust(), "untrusted"))
                .privacy(normalizeTrustPrivacyOrDefault(dto.getPrivacy(), "public"))
                .build();
    }

    private List<BoardEnvironmentVariableDto> replaceEnvironmentVariablesInternal(
            Long userId,
            List<BoardEnvironmentVariableDto> variables) {
        if (environmentRepo == null) {
            return variables == null ? List.of() : variables;
        }
        environmentRepo.deleteByUserId(userId);
        List<BoardEnvironmentVariablePo> entities = (variables == null ? List.<BoardEnvironmentVariableDto>of() : variables)
                .stream()
                .map(dto -> environmentToEntity(userId, dto))
                .filter(po -> hasText(po.getName()))
                .toList();
        List<BoardEnvironmentVariablePo> saved = environmentRepo.saveAll(entities);
        return saved.stream()
                .map(this::environmentToDto)
                .filter(Objects::nonNull)
                .toList();
    }

    private List<BoardEnvironmentVariableDto> refreshEnvironmentVariablesInternal(
            Long userId,
            List<DeviceNodeDto> nodes) {
        List<BoardEnvironmentVariableDto> merged = projectEnvironmentVariablesForNodes(userId, nodes);
        return replaceEnvironmentVariablesInternal(userId, merged);
    }

    private List<BoardEnvironmentVariableDto> projectEnvironmentVariablesForNodes(
            Long userId,
            List<DeviceNodeDto> nodes) {
        return projectEnvironmentVariablesForNodes(
                userId, nodes, loadTemplateManifestMap(userId), false);
    }

    private List<BoardEnvironmentVariableDto> projectEnvironmentVariablesForNodes(
            Long userId,
            List<DeviceNodeDto> nodes,
            Map<String, DeviceManifest> templateManifests,
            boolean resetValuesOutsideNewDomains) {
        Map<String, DeviceManifest.InternalVariable> required = collectRequiredEnvironmentVariables(
                nodes, templateManifests);
        List<BoardEnvironmentVariableDto> merged = mergeEnvironmentVariables(
                List.of(), getEnvironmentVariablesInternal(userId), required);
        if (resetValuesOutsideNewDomains) {
            merged = merged.stream().map(variable -> {
                DeviceManifest.InternalVariable definition = required.get(variable.getName());
                if (isLegalEnvironmentValue(variable.getValue(), definition)) {
                    return variable;
                }
                return new BoardEnvironmentVariableDto(
                        variable.getName(),
                        defaultEnvironmentValue(definition),
                        variable.getTrust(),
                        variable.getPrivacy());
            }).toList();
        }
        validateEnvironmentVariables(merged, required);
        return merged;
    }

    private boolean isLegalEnvironmentValue(String value, DeviceManifest.InternalVariable definition) {
        if (!hasText(value) || definition == null) {
            return false;
        }
        Map<String, String> errors = new LinkedHashMap<>();
        validateVariableValues(errors, "value", definition, "=", value);
        return errors.isEmpty();
    }

    private List<EnvironmentVariableChangeDto> diffEnvironmentVariables(
            List<BoardEnvironmentVariableDto> previous,
            List<BoardEnvironmentVariableDto> current) {
        Map<String, BoardEnvironmentVariableDto> previousByName = environmentDtoMap(previous);
        Map<String, BoardEnvironmentVariableDto> currentByName = environmentDtoMap(current);
        Set<String> names = new TreeSet<>();
        names.addAll(previousByName.keySet());
        names.addAll(currentByName.keySet());

        List<EnvironmentVariableChangeDto> changes = new ArrayList<>();
        for (String name : names) {
            BoardEnvironmentVariableDto before = previousByName.get(name);
            BoardEnvironmentVariableDto after = currentByName.get(name);
            EnvironmentVariableChangeDto.ChangeType changeType;
            if (before == null) {
                changeType = EnvironmentVariableChangeDto.ChangeType.ADDED;
            } else if (after == null) {
                changeType = EnvironmentVariableChangeDto.ChangeType.REMOVED;
            } else if (!before.equals(after)) {
                changeType = EnvironmentVariableChangeDto.ChangeType.UPDATED;
            } else {
                continue;
            }
            changes.add(EnvironmentVariableChangeDto.builder()
                    .changeType(changeType)
                    .name(name)
                    .previousValue(before)
                    .currentValue(after)
                    .build());
        }
        return List.copyOf(changes);
    }

    private String deletionImpactToken(DeviceNodeDto device,
                                       List<RuleDto> removedRules,
                                       List<SpecificationDto> removedSpecifications,
                                       List<EnvironmentVariableChangeDto> environmentChanges) {
        Map<String, Object> impact = new LinkedHashMap<>();
        impact.put("device", device);
        impact.put("removedRules", removedRules != null ? removedRules : List.of());
        impact.put("removedSpecifications",
                removedSpecifications != null ? removedSpecifications : List.of());
        impact.put("environmentChanges", environmentChanges != null ? environmentChanges : List.of());
        String source = JsonUtils.toJson(impact);
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256")
                    .digest(source.getBytes(StandardCharsets.UTF_8));
            return HexFormat.of().formatHex(digest);
        } catch (NoSuchAlgorithmException e) {
            throw new InternalServerException("Unable to create device-deletion impact token", e);
        }
    }

    /**
     * A complete internal read-modify-write may use null fields to restore template defaults. A
     * scene import is stricter: every required environment variable and label must be explicit.
     */
    private List<BoardEnvironmentVariableDto> saveEnvironmentVariablesInternal(
            Long userId,
            List<DeviceNodeDto> nodes,
            List<BoardEnvironmentVariableDto> variables,
            boolean preserveExistingValues) {
        Map<String, DeviceManifest> templateManifests = loadTemplateManifestMap(userId);
        Map<String, DeviceManifest.InternalVariable> required = collectRequiredEnvironmentVariables(
                nodes, templateManifests);
        validateSubmittedEnvironmentNames(variables, required);
        if (!preserveExistingValues) {
            validateCompleteEnvironmentSubmission(variables, required);
        }
        List<BoardEnvironmentVariableDto> merged = mergeEnvironmentVariables(
                variables, preserveExistingValues ? getEnvironmentVariablesInternal(userId) : List.of(), required);
        validateEnvironmentVariables(merged, required);
        return replaceEnvironmentVariablesInternal(userId, merged);
    }

    /**
     * Applies only non-null fields from each submitted item. Omitted fields retain the materialized
     * current value, so a UI edit of one label cannot reset the value or the other label.
     */
    private EnvironmentMutationResultDto patchEnvironmentVariablesInternal(
            Long userId,
            List<DeviceNodeDto> nodes,
            List<BoardEnvironmentVariableDto> patches) {
        if (patches == null || patches.isEmpty()) {
            throw new BadRequestException("At least one environment variable patch is required");
        }
        Map<String, DeviceManifest> templateManifests = loadTemplateManifestMap(userId);
        Map<String, DeviceManifest.InternalVariable> required = collectRequiredEnvironmentVariables(
                nodes, templateManifests);
        validateSubmittedEnvironmentNames(patches, required);
        validateEnvironmentPatchFields(patches);

        List<BoardEnvironmentVariableDto> persistedBefore = getEnvironmentVariablesInternal(userId);
        List<BoardEnvironmentVariableDto> materializedBefore = mergeEnvironmentVariables(
                List.of(), persistedBefore, required);
        validateEnvironmentVariables(materializedBefore, required);

        List<BoardEnvironmentVariableDto> merged = mergeEnvironmentVariablePatches(
                patches, materializedBefore, required);
        validateEnvironmentVariables(merged, required);
        List<BoardEnvironmentVariableDto> saved = replaceEnvironmentVariablesInternal(userId, merged);
        List<EnvironmentVariableChangeDto> changes = diffEnvironmentVariables(persistedBefore, saved);

        return EnvironmentMutationResultDto.builder()
                .operation(changes.isEmpty() ? "unchanged" : "updated")
                .patchResults(describeEnvironmentVariablePatches(patches, materializedBefore, saved))
                .environmentVariables(saved)
                .environmentChanges(changes)
                .currentCount(saved.size())
                .build();
    }

    private void validateEnvironmentPatchFields(List<BoardEnvironmentVariableDto> patches) {
        Map<String, String> errors = new LinkedHashMap<>();
        for (int i = 0; i < patches.size(); i++) {
            BoardEnvironmentVariableDto patch = patches.get(i);
            if (patch != null
                    && patch.getValue() == null
                    && patch.getTrust() == null
                    && patch.getPrivacy() == null) {
                errors.put("environmentVariables[" + i + "]",
                        "At least one of value, trust or privacy must be provided");
            }
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private void syncEnvironmentPoolForNodes(Long userId, List<DeviceNodeDto> nodes) {
        if (environmentRepo == null) {
            return;
        }
        refreshEnvironmentVariablesInternal(userId, nodes);
    }

    private Map<String, DeviceManifest.InternalVariable> collectRequiredEnvironmentVariables(
            List<DeviceNodeDto> nodes,
            Map<String, DeviceManifest> templateManifests) {
        Map<String, DeviceManifest.InternalVariable> required = new TreeMap<>();
        if (nodes == null || nodes.isEmpty() || templateManifests == null || templateManifests.isEmpty()) {
            return required;
        }
        for (DeviceNodeDto node : nodes) {
            if (node == null || !hasText(node.getTemplateName())) {
                continue;
            }
            DeviceManifest manifest = manifestForTemplateName(node.getTemplateName(), templateManifests);
            if (manifest == null) {
                continue;
            }
            if (manifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                    if (variable == null || !hasText(variable.getName()) || !isEnvironmentVariable(variable)) {
                        continue;
                    }
                    required.putIfAbsent(variable.getName(), variable);
                }
            }
            if (manifest.getImpactedVariables() != null) {
                for (String impacted : manifest.getImpactedVariables()) {
                    DeviceManifest.InternalVariable definition =
                            EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted);
                    if (definition != null) {
                        required.putIfAbsent(impacted, definition);
                    }
                }
            }
        }
        return required;
    }

    private List<BoardEnvironmentVariableDto> mergeEnvironmentVariables(
            List<BoardEnvironmentVariableDto> submitted,
            List<BoardEnvironmentVariableDto> existing,
            Map<String, DeviceManifest.InternalVariable> required) {
        Map<String, BoardEnvironmentVariableDto> existingByName = environmentDtoMap(existing);
        Map<String, BoardEnvironmentVariableDto> submittedByName = environmentDtoMap(submitted);
        List<BoardEnvironmentVariableDto> merged = new ArrayList<>();
        for (Map.Entry<String, DeviceManifest.InternalVariable> entry : required.entrySet()) {
            String name = entry.getKey();
            DeviceManifest.InternalVariable definition = entry.getValue();
            BoardEnvironmentVariableDto candidate = submittedByName.get(name);
            if (candidate == null) {
                candidate = existingByName.get(name);
            }
            String value = candidate != null ? candidate.getValue() : defaultEnvironmentValue(definition);
            if (!hasText(value) && hasText(defaultEnvironmentValue(definition))) {
                value = defaultEnvironmentValue(definition);
            }
            String trust = candidate != null ? candidate.getTrust() : definition.getTrust();
            String privacy = candidate != null ? candidate.getPrivacy() : definition.getPrivacy();
            merged.add(new BoardEnvironmentVariableDto(
                    name,
                    value,
                    normalizeTrustPrivacyOrDefault(trust, normalizeTrustPrivacyOrDefault(definition.getTrust(), "untrusted")),
                    normalizeTrustPrivacyOrDefault(privacy, normalizeTrustPrivacyOrDefault(definition.getPrivacy(), "public"))
            ));
        }
        return merged;
    }

    private List<BoardEnvironmentVariableDto> mergeEnvironmentVariablePatches(
            List<BoardEnvironmentVariableDto> patches,
            List<BoardEnvironmentVariableDto> existing,
            Map<String, DeviceManifest.InternalVariable> required) {
        Map<String, BoardEnvironmentVariableDto> existingByName = environmentDtoMap(existing);
        Map<String, BoardEnvironmentVariableDto> patchByName = environmentDtoMap(patches);
        List<BoardEnvironmentVariableDto> merged = new ArrayList<>();
        for (Map.Entry<String, DeviceManifest.InternalVariable> entry : required.entrySet()) {
            String name = entry.getKey();
            DeviceManifest.InternalVariable definition = entry.getValue();
            BoardEnvironmentVariableDto current = existingByName.get(name);
            if (current == null) {
                current = new BoardEnvironmentVariableDto(
                        name,
                        defaultEnvironmentValue(definition),
                        normalizeTrustPrivacyOrDefault(definition.getTrust(), "untrusted"),
                        normalizeTrustPrivacyOrDefault(definition.getPrivacy(), "public"));
            }
            BoardEnvironmentVariableDto patch = patchByName.get(name);
            merged.add(new BoardEnvironmentVariableDto(
                    name,
                    patch != null && patch.getValue() != null ? patch.getValue() : current.getValue(),
                    patch != null && patch.getTrust() != null ? patch.getTrust() : current.getTrust(),
                    patch != null && patch.getPrivacy() != null ? patch.getPrivacy() : current.getPrivacy()));
        }
        return merged;
    }

    private List<EnvironmentVariablePatchResultDto> describeEnvironmentVariablePatches(
            List<BoardEnvironmentVariableDto> patches,
            List<BoardEnvironmentVariableDto> previous,
            List<BoardEnvironmentVariableDto> current) {
        Map<String, BoardEnvironmentVariableDto> previousByName = environmentDtoMap(previous);
        Map<String, BoardEnvironmentVariableDto> currentByName = environmentDtoMap(current);
        List<EnvironmentVariablePatchResultDto> results = new ArrayList<>();
        for (BoardEnvironmentVariableDto rawPatch : patches == null
                ? List.<BoardEnvironmentVariableDto>of() : patches) {
            String name = rawPatch.getName().trim();
            BoardEnvironmentVariableDto before = previousByName.get(name);
            BoardEnvironmentVariableDto after = currentByName.get(name);
            List<String> suppliedFields = environmentPatchFields(rawPatch);
            List<String> changedFields = suppliedFields.stream()
                    .filter(field -> !Objects.equals(
                            environmentFieldValue(before, field), environmentFieldValue(after, field)))
                    .toList();
            List<String> preservedFields = List.of("value", "trust", "privacy").stream()
                    .filter(field -> !suppliedFields.contains(field))
                    .toList();
            results.add(EnvironmentVariablePatchResultDto.builder()
                    .name(name)
                    .suppliedFields(suppliedFields)
                    .changedFields(changedFields)
                    .preservedFields(preservedFields)
                    .previousValue(before)
                    .currentValue(after)
                    .build());
        }
        return List.copyOf(results);
    }

    private List<String> environmentPatchFields(BoardEnvironmentVariableDto patch) {
        List<String> fields = new ArrayList<>();
        if (patch.getValue() != null) fields.add("value");
        if (patch.getTrust() != null) fields.add("trust");
        if (patch.getPrivacy() != null) fields.add("privacy");
        return List.copyOf(fields);
    }

    private String environmentFieldValue(BoardEnvironmentVariableDto variable, String field) {
        if (variable == null) return null;
        return switch (field) {
            case "value" -> variable.getValue();
            case "trust" -> variable.getTrust();
            case "privacy" -> variable.getPrivacy();
            default -> null;
        };
    }

    private Map<String, BoardEnvironmentVariableDto> environmentDtoMap(List<BoardEnvironmentVariableDto> values) {
        Map<String, BoardEnvironmentVariableDto> result = new LinkedHashMap<>();
        if (values == null) {
            return result;
        }
        for (BoardEnvironmentVariableDto value : values) {
            if (value == null || !hasText(value.getName())) {
                continue;
            }
            String name = value.getName().trim();
            result.putIfAbsent(name, new BoardEnvironmentVariableDto(
                    name,
                    trimToNull(value.getValue()),
                    trimToNull(value.getTrust()),
                    trimToNull(value.getPrivacy())
            ));
        }
        return result;
    }

    private void validateEnvironmentVariables(List<BoardEnvironmentVariableDto> variables,
                                              Map<String, DeviceManifest.InternalVariable> required) {
        Map<String, String> errors = new LinkedHashMap<>();
        Set<String> seen = new HashSet<>();
        for (int i = 0; i < (variables == null ? 0 : variables.size()); i++) {
            BoardEnvironmentVariableDto variable = variables.get(i);
            String prefix = "environmentVariables[" + i + "]";
            if (variable == null) {
                errors.putIfAbsent(prefix, "Environment variable item cannot be null");
                continue;
            }
            String name = trimToNull(variable.getName());
            if (name == null) {
                errors.putIfAbsent(prefix + ".name", "Environment variable name is required");
                continue;
            }
            if (!seen.add(name)) {
                errors.putIfAbsent(prefix + ".name", "Duplicate environment variable: " + name);
            }
            DeviceManifest.InternalVariable definition = required.get(name);
            if (definition == null) {
                errors.putIfAbsent(prefix + ".name", "Environment variable is not required by the current board: " + name);
                continue;
            }
            validateNodeTrust(errors, prefix + ".trust", variable.getTrust());
            validatePrivacyValues(errors, prefix + ".privacy", "=", variable.getPrivacy());
            String value = trimToNull(variable.getValue());
            if (hasEnvironmentValueDomain(definition) && value == null) {
                errors.putIfAbsent(prefix + ".value", "Environment variable value is required for " + name);
            } else if (value != null) {
                validateVariableValues(errors, prefix + ".value", definition, "=", value);
            }
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private void validateSubmittedEnvironmentNames(List<BoardEnvironmentVariableDto> submitted,
                                                   Map<String, DeviceManifest.InternalVariable> required) {
        if (submitted == null || submitted.isEmpty()) {
            return;
        }
        Map<String, String> errors = new LinkedHashMap<>();
        Set<String> seen = new HashSet<>();
        for (int i = 0; i < submitted.size(); i++) {
            BoardEnvironmentVariableDto variable = submitted.get(i);
            String prefix = "environmentVariables[" + i + "]";
            if (variable == null) {
                errors.putIfAbsent(prefix, "Environment variable item cannot be null");
                continue;
            }
            String name = trimToNull(variable.getName());
            if (name == null) {
                errors.putIfAbsent(prefix + ".name", "Environment variable name is required");
                continue;
            }
            if (!seen.add(name)) {
                errors.putIfAbsent(prefix + ".name", "Duplicate environment variable: " + name);
            }
            if (!required.containsKey(name)) {
                errors.putIfAbsent(prefix + ".name",
                        "Environment variable is not required by the current board: " + name);
                continue;
            }
            validateNodeTrust(errors, prefix + ".trust", variable.getTrust());
            if (variable.getPrivacy() != null) {
                validatePrivacyValues(errors, prefix + ".privacy", "=", variable.getPrivacy());
            }
            if (variable.getValue() != null && !hasText(variable.getValue())) {
                errors.putIfAbsent(prefix + ".value",
                        "Environment variable value cannot be blank when provided");
            } else if (hasText(variable.getValue())) {
                validateVariableValues(errors, prefix + ".value", required.get(name), "=", variable.getValue());
            }
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private void validateCompleteEnvironmentSubmission(
            List<BoardEnvironmentVariableDto> submitted,
            Map<String, DeviceManifest.InternalVariable> required) {
        Map<String, String> errors = new LinkedHashMap<>();
        Set<String> provided = new HashSet<>();
        List<BoardEnvironmentVariableDto> values = submitted == null ? List.of() : submitted;
        for (int index = 0; index < values.size(); index++) {
            BoardEnvironmentVariableDto variable = values.get(index);
            if (variable == null) {
                continue;
            }
            String name = trimToNull(variable.getName());
            if (name != null) {
                provided.add(name);
            }
            String prefix = "environmentVariables[" + index + "]";
            if (!hasText(variable.getValue())) {
                errors.putIfAbsent(prefix + ".value",
                        "Scene environment variable value must be explicit and non-blank");
            }
            if (!hasText(variable.getTrust())) {
                errors.putIfAbsent(prefix + ".trust",
                        "Scene environment variable trust must be explicit (trusted or untrusted)");
            }
            if (!hasText(variable.getPrivacy())) {
                errors.putIfAbsent(prefix + ".privacy",
                        "Scene environment variable privacy must be explicit (public or private)");
            }
        }
        Set<String> missing = new TreeSet<>(required.keySet());
        missing.removeAll(provided);
        if (!missing.isEmpty()) {
            errors.put("environmentVariables",
                    "Scene is missing required environment variables: " + String.join(", ", missing));
        }
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private boolean hasEnvironmentValueDomain(DeviceManifest.InternalVariable variable) {
        if (variable == null) {
            return false;
        }
        return (variable.getValues() != null && !variable.getValues().isEmpty())
                || (variable.getLowerBound() != null && variable.getUpperBound() != null);
    }

    private boolean isEnvironmentVariable(DeviceManifest.InternalVariable variable) {
        return variable != null && !Boolean.TRUE.equals(variable.getIsInside());
    }

    private String defaultEnvironmentValue(DeviceManifest.InternalVariable variable) {
        if (variable == null) {
            return null;
        }
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            return trimToNull(variable.getValues().get(0));
        }
        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            return String.valueOf(variable.getLowerBound());
        }
        return null;
    }

    private String normalizeTrustPrivacyOrDefault(String value, String fallback) {
        String normalized = DeviceSmvDataFactory.normalizeTrustPrivacy(value);
        if (normalized != null) {
            return normalized;
        }
        return fallback;
    }

    private void validateBoardReferences(Long userId,
                                         List<DeviceNodeDto> nodes,
                                         List<RuleDto> rules,
                                         List<SpecificationDto> specs) {
        validateBoardReferences(userId, nodes, rules, specs, loadTemplateManifestMap(userId));
    }

    private void validateBoardReferences(Long userId,
                                         List<DeviceNodeDto> nodes,
                                         List<RuleDto> rules,
                                         List<SpecificationDto> specs,
                                         Map<String, DeviceManifest> templateManifests) {
        Set<String> nodeIds = nodeIds(nodes);
        Map<String, DeviceNodeDto> nodesById = nodesById(nodes);
        Map<String, String> errors = new LinkedHashMap<>();
        validateNodeLayouts(nodes, errors);
        validateNodeTemplateRefs(nodes, errors, templateManifests);
        validateNodeRuntimeSemantics(errors, nodes, templateManifests);
        validateActiveEnvironmentDomainConsistency(errors, nodes, templateManifests);
        validateGeneratedMainNamespace(errors, nodes, rules, templateManifests);

        if (rules != null) {
            for (int ruleIndex = 0; ruleIndex < rules.size(); ruleIndex++) {
                RuleDto rule = rules.get(ruleIndex);
                if (rule == null) {
                    continue;
                }
                RuleDto.Command command = rule.getCommand();
                if (command != null) {
                    requireBoardNodeRef(errors, "rules[" + ruleIndex + "].command.deviceName",
                            command.getDeviceName(), nodeIds, "Unknown command device");
                    if (hasText(command.getContentDevice())) {
                        requireBoardNodeRef(errors, "rules[" + ruleIndex + "].command.contentDevice",
                                command.getContentDevice(), nodeIds, "Unknown content device");
                    }
                }
                List<RuleDto.Condition> conditions = rule.getConditions();
                if (conditions == null) {
                    continue;
                }
                for (int conditionIndex = 0; conditionIndex < conditions.size(); conditionIndex++) {
                    RuleDto.Condition condition = conditions.get(conditionIndex);
                    if (condition == null) {
                        continue;
                    }
                    requireBoardNodeRef(errors,
                            "rules[" + ruleIndex + "].conditions[" + conditionIndex + "].deviceName",
                            condition.getDeviceName(), nodeIds, "Unknown condition device");
                }
                validateRuleSemantics(errors, "rules[" + ruleIndex + "]",
                        rule, nodesById, templateManifests);
            }
        }

        if (specs != null) {
            for (int specIndex = 0; specIndex < specs.size(); specIndex++) {
                SpecificationDto spec = specs.get(specIndex);
                if (spec == null) {
                    continue;
                }
                validateSpecTemplateShape(errors, "specs[" + specIndex + "]", spec);
                validateSpecConditionRefs(errors, "specs[" + specIndex + "].aConditions",
                        spec.getAConditions(), nodeIds, nodesById, templateManifests);
                validateSpecConditionRefs(errors, "specs[" + specIndex + "].ifConditions",
                        spec.getIfConditions(), nodeIds, nodesById, templateManifests);
                validateSpecConditionRefs(errors, "specs[" + specIndex + "].thenConditions",
                        spec.getThenConditions(), nodeIds, nodesById, templateManifests);
                validateSafetySourceCapabilities(errors, "specs[" + specIndex + "]",
                        spec, nodesById, templateManifests);
            }
        }

        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private void validateNodeLayouts(List<DeviceNodeDto> nodes, Map<String, String> errors) {
        if (nodes == null) {
            return;
        }
        for (int index = 0; index < nodes.size(); index++) {
            DeviceNodeDto node = nodes.get(index);
            if (node == null) {
                continue;
            }
            String prefix = "nodes[" + index + "]";
            DeviceNodeDto.Position position = node.getPosition();
            Double x = position != null ? position.getX() : null;
            Double y = position != null ? position.getY() : null;
            if (x == null || !Double.isFinite(x) || Math.abs(x) > DeviceLayoutDto.MAX_ABS_POSITION) {
                errors.putIfAbsent(prefix + ".position.x",
                        "X coordinate must be finite and within -1000000..1000000");
            }
            if (y == null || !Double.isFinite(y) || Math.abs(y) > DeviceLayoutDto.MAX_ABS_POSITION) {
                errors.putIfAbsent(prefix + ".position.y",
                        "Y coordinate must be finite and within -1000000..1000000");
            }
            if (node.getWidth() == null || node.getWidth() < DeviceLayoutDto.MIN_WIDTH
                    || node.getWidth() > DeviceLayoutDto.MAX_WIDTH) {
                errors.putIfAbsent(prefix + ".width", "Width must be within 80..2000");
            }
            if (node.getHeight() == null || node.getHeight() < DeviceLayoutDto.MIN_HEIGHT
                    || node.getHeight() > DeviceLayoutDto.MAX_HEIGHT) {
                errors.putIfAbsent(prefix + ".height", "Height must be within 60..2000");
            }
        }
    }

    private List<DeviceNodeDto> canonicalizeNodeTemplateNames(Long userId, List<DeviceNodeDto> nodes) {
        if (nodes == null || nodes.isEmpty() || deviceTemplateRepo == null) {
            return nodes;
        }
        Map<String, String> canonicalTemplateNames = templateAliasToCanonicalName(userId);
        if (canonicalTemplateNames.isEmpty()) {
            return nodes;
        }
        for (DeviceNodeDto node : nodes) {
            if (node == null || !hasText(node.getTemplateName())) {
                continue;
            }
            String raw = node.getTemplateName().trim();
            String canonical = canonicalTemplateNames.get(raw.toLowerCase(Locale.ROOT));
            if (canonical != null) {
                node.setTemplateName(canonical);
            }
        }
        return nodes;
    }

    private void validateSpecTemplateShape(Map<String, String> errors,
                                           String field,
                                           SpecificationDto spec) {
        String templateId = spec.getTemplateId();
        if (!hasText(templateId) || !templateId.matches("^[1-7]$")) {
            return;
        }
        int aCount = sizeOf(spec.getAConditions());
        int ifCount = sizeOf(spec.getIfConditions());
        int thenCount = sizeOf(spec.getThenConditions());
        if (Set.of("1", "2", "3", "7").contains(templateId)) {
            if (aCount == 0) {
                errors.putIfAbsent(field + ".aConditions",
                        "Template " + templateId + " requires at least one A condition");
            }
            if (ifCount > 0 || thenCount > 0) {
                errors.putIfAbsent(field + ".templateId",
                        "Template " + templateId + " uses A conditions only");
            }
            if ("7".equals(templateId)) {
                validateUntrustedSourceSafetyConditions(errors, field, spec.getAConditions());
            }
            return;
        }
        if (aCount > 0) {
            errors.putIfAbsent(field + ".aConditions",
                    "Template " + templateId + " uses IF/THEN conditions only");
        }
        if (ifCount == 0 || thenCount == 0) {
            errors.putIfAbsent(field + ".ifConditions",
                    "Template " + templateId + " requires both IF and THEN conditions");
        }
    }

    private int sizeOf(List<?> values) {
        return values == null ? 0 : values.size();
    }

    private void validateUntrustedSourceSafetyConditions(Map<String, String> errors,
                                                          String field,
                                                          List<SpecConditionDto> conditions) {
        if (conditions == null) {
            return;
        }
        for (int index = 0; index < conditions.size(); index++) {
            SpecConditionDto condition = conditions.get(index);
            if (condition == null) {
                continue;
            }
            String prefix = field + ".aConditions[" + index + "]";
            String targetType = condition.getTargetType() == null
                    ? "" : condition.getTargetType().trim().toLowerCase(Locale.ROOT);
            String relation = SmvRelationUtils.normalizeRelation(condition.getRelation());
            if ("trust".equals(targetType) || "privacy".equals(targetType)) {
                errors.putIfAbsent(prefix + ".targetType",
                        "Template 7 associates the MEDIC control-source label automatically; use template 3 for explicit trust/privacy predicates");
            } else if (("state".equals(targetType) || "mode".equals(targetType))
                    && !"=".equals(relation)) {
                errors.putIfAbsent(prefix + ".relation",
                        "Template 7 state and mode conditions require '=' so the protected event has one source label");
            } else if ("api".equals(targetType)
                    && (!"=".equals(relation) || !"TRUE".equalsIgnoreCase(condition.getValue()))) {
                errors.putIfAbsent(prefix + ".value",
                        "Template 7 API conditions require '= TRUE'");
            }
        }
    }

    private void validateSafetySourceCapabilities(Map<String, String> errors,
                                                  String field,
                                                  SpecificationDto spec,
                                                  Map<String, DeviceNodeDto> nodesById,
                                                  Map<String, DeviceManifest> templateManifests) {
        if (spec == null || !"7".equals(spec.getTemplateId()) || spec.getAConditions() == null) {
            return;
        }
        for (int index = 0; index < spec.getAConditions().size(); index++) {
            SpecConditionDto condition = spec.getAConditions().get(index);
            if (condition == null || !"api".equals(normalizeSpecTargetType(condition.getTargetType()))) {
                continue;
            }
            DeviceManifest manifest = manifestForDeviceRef(condition.getDeviceId(), nodesById, templateManifests);
            DeviceManifest.API api = signalApi(manifest, condition.getKey());
            if (api != null && !hasText(api.getEndState())) {
                errors.putIfAbsent(field + ".aConditions[" + index + "].key",
                        "Template 7 cannot derive a MEDIC control-source label for API '"
                                + condition.getKey() + "' because its device template has no EndState");
            }
        }
    }

    private DeviceManifest.API signalApi(DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || !hasText(apiName)) return null;
        return manifest.getApis().stream()
                .filter(api -> api != null && Boolean.TRUE.equals(api.getSignal())
                        && apiName.trim().equals(api.getName()))
                .findFirst()
                .orElse(null);
    }

    private void validateSpecConditionRefs(Map<String, String> errors,
                                           String field,
                                           List<SpecConditionDto> conditions,
                                           Set<String> nodeIds,
                                           Map<String, DeviceNodeDto> nodesById,
                                           Map<String, DeviceManifest> templateManifests) {
        if (conditions == null) {
            return;
        }
        for (int i = 0; i < conditions.size(); i++) {
            SpecConditionDto condition = conditions.get(i);
            if (condition == null) {
                continue;
            }
            requireBoardNodeRef(errors, field + "[" + i + "].deviceId",
                    condition.getDeviceId(), nodeIds, "Unknown spec condition device");
            validateSpecConditionSemantics(errors, field + "[" + i + "]",
                    condition, nodesById, templateManifests);
        }
    }

    private void validateNodeTemplateRefs(List<DeviceNodeDto> nodes,
                                          Map<String, String> errors,
                                          Map<String, DeviceManifest> templateManifests) {
        if (nodes == null || nodes.isEmpty() || deviceTemplateRepo == null) {
            return;
        }

        Map<Integer, String> nodeTemplateRefs = new LinkedHashMap<>();
        for (int nodeIndex = 0; nodeIndex < nodes.size(); nodeIndex++) {
            DeviceNodeDto node = nodes.get(nodeIndex);
            if (node == null || !hasText(node.getTemplateName())) {
                continue;
            }
            String templateName = node.getTemplateName().trim();
            nodeTemplateRefs.put(nodeIndex, templateName);
        }
        if (nodeTemplateRefs.isEmpty()) {
            return;
        }

        for (Map.Entry<Integer, String> entry : nodeTemplateRefs.entrySet()) {
            int nodeIndex = entry.getKey();
            String templateName = entry.getValue();
            if (templateManifests == null
                    || !templateManifests.containsKey(templateName.toLowerCase(Locale.ROOT))) {
                errors.putIfAbsent("nodes[" + nodeIndex + "].templateName",
                        "Unknown device template: " + templateName);
            }
        }
    }

    private Map<String, String> templateAliasToCanonicalName(Long userId) {
        if (deviceTemplateRepo == null) {
            return Collections.emptyMap();
        }
        List<DeviceTemplatePo> templates = deviceTemplateRepo.findByUserId(userId);
        if (templates == null || templates.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<String, String> result = new LinkedHashMap<>();
        for (DeviceTemplatePo template : templates) {
            if (template == null || !hasText(template.getName())) {
                continue;
            }
            String canonical = template.getName().trim();
            putTemplateAlias(result, canonical, canonical);
            DeviceTemplateDto dto = deviceTemplateMapper.toDto(template);
            if (dto != null && dto.getManifest() != null) {
                putTemplateAlias(result, dto.getManifest().getName(), canonical);
            }
        }
        return result;
    }

    private void putTemplateAlias(Map<String, String> aliases, String rawName, String canonical) {
        if (!hasText(rawName) || !hasText(canonical)) {
            return;
        }
        aliases.putIfAbsent(rawName.trim().toLowerCase(Locale.ROOT), canonical.trim());
    }

    private void validateNodeRuntimeSemantics(Map<String, String> errors,
                                               List<DeviceNodeDto> nodes,
                                               Map<String, DeviceManifest> templateManifests) {
        if (nodes == null || nodes.isEmpty()) {
            return;
        }

        Set<String> seenIds = new HashSet<>();
        Set<String> seenModelIds = new HashSet<>();
        Set<String> seenLabels = new HashSet<>();
        for (int nodeIndex = 0; nodeIndex < nodes.size(); nodeIndex++) {
            DeviceNodeDto node = nodes.get(nodeIndex);
            if (node == null) {
                continue;
            }
            String field = "nodes[" + nodeIndex + "]";

            String nodeId = trimToNull(node.getId());
            if (nodeId != null && !seenIds.add(nodeId)) {
                errors.putIfAbsent(field + ".id", "Duplicate device ID: " + nodeId);
            }
            if (nodeId != null) {
                String modelId = DeviceNameNormalizer.normalize(nodeId);
                if (!seenModelIds.add(modelId)) {
                    errors.putIfAbsent(field + ".id",
                            "Device ID collides after NuSMV normalization: " + nodeId + " -> " + modelId);
                }
            }

            String label = trimToNull(node.getLabel());
            if (label != null && !seenLabels.add(label.toLowerCase(Locale.ROOT))) {
                errors.putIfAbsent(field + ".label", "Duplicate device label: " + label);
            }

            DeviceManifest manifest = manifestForTemplateName(node.getTemplateName(), templateManifests);
            if (manifest == null) {
                continue;
            }

            validateImpactedEnvironmentDomains(errors, field, node.getTemplateName(), manifest);
            boolean hasModeStateMachine = hasModeStateMachine(manifest);
            validateNodeState(errors, field, node, manifest);
            validateStatelessNodeFields(errors, field, node, hasModeStateMachine);
            if (hasModeStateMachine) {
                validateNodeTrust(errors, field + ".currentStateTrust", node.getCurrentStateTrust());
                if (node.getCurrentStatePrivacy() != null) {
                    validatePrivacyValues(errors, field + ".currentStatePrivacy", "=", node.getCurrentStatePrivacy());
                }
            }
            validateNodeVariables(errors, field + ".variables", node.getVariables(), manifest);
            validateNodePrivacies(errors, field + ".privacies", node.getPrivacies(), manifest);
        }
    }

    private void validateGeneratedMainNamespace(Map<String, String> errors,
                                                List<DeviceNodeDto> nodes,
                                                List<RuleDto> rules,
                                                Map<String, DeviceManifest> templateManifests) {
        if (nodes == null || nodes.isEmpty()) {
            return;
        }

        Map<String, String> generated = new LinkedHashMap<>();
        Map<String, DeviceManifest.InternalVariable> environment =
                collectRequiredEnvironmentVariables(nodes, templateManifests);
        for (String name : environment.keySet()) {
            registerGeneratedMainIdentifier(generated, "a_" + name,
                    "shared environment value '" + name + "'");
        }

        registerGeneratedMainIdentifier(generated, SmvConstants.NUSMV_COMPROMISED_POINT_COUNT,
                "attack-budget accounting");
        if (rules != null) {
            Map<String, DeviceNodeDto> nodeById = nodesById(nodes);
            for (int ruleIndex = 0; ruleIndex < rules.size(); ruleIndex++) {
                RuleDto rule = rules.get(ruleIndex);
                String ruleLabel = ruleDisplayName(rule, ruleIndex);
                registerGeneratedMainIdentifier(generated,
                        SmvConstants.RULE_EXECUTION_PROBE_PREFIX + ruleIndex,
                        "rule playback tracking for '" + ruleLabel + "'");
                registerGeneratedMainIdentifier(generated,
                        SmvConstants.AUTOMATION_LINK_ATTACK_PREFIX + ruleIndex,
                        "attack analysis for automation rule '" + ruleLabel + "'");

                List<RuleDto.Condition> conditions = rule == null ? null : rule.getConditions();
                if (conditions == null) {
                    continue;
                }
                for (int conditionIndex = 0; conditionIndex < conditions.size(); conditionIndex++) {
                    RuleDto.Condition condition = conditions.get(conditionIndex);
                    if (condition == null) {
                        continue;
                    }
                    registerGeneratedMainIdentifier(generated,
                            "lambda_r" + ruleIndex + "_c" + conditionIndex,
                            "automatic-fix condition selection for '" + ruleLabel + "'");
                    if (isParameterizableBoardCondition(condition, nodeById, templateManifests)) {
                        registerGeneratedMainIdentifier(generated,
                                "param_r" + ruleIndex + "_c" + conditionIndex,
                                "automatic-fix parameter adjustment for '" + ruleLabel + "'");
                    }
                }
            }
        }

        for (int nodeIndex = 0; nodeIndex < nodes.size(); nodeIndex++) {
            DeviceNodeDto node = nodes.get(nodeIndex);
            if (node == null || !hasText(node.getId())) {
                continue;
            }
            String modelId = DeviceNameNormalizer.normalize(node.getId().trim());
            String conflict = generated.get(modelId.toLowerCase(Locale.ROOT));
            if (conflict == null) {
                continue;
            }
            errors.putIfAbsent("nodes[" + nodeIndex + "].id",
                    "Device '" + deviceDisplayName(node) + "' uses a scene reference that conflicts with "
                            + conflict + ". Change this device's devices[].id and matching rule/spec references "
                            + "in the scene JSON, or recreate the device through the UI. Its display name may stay unchanged.");
        }
    }

    private void registerGeneratedMainIdentifier(Map<String, String> generated,
                                                 String identifier,
                                                 String description) {
        if (hasText(identifier)) {
            generated.putIfAbsent(identifier.trim().toLowerCase(Locale.ROOT), description);
        }
    }

    private String ruleDisplayName(RuleDto rule, int ruleIndex) {
        return rule != null && hasText(rule.getRuleString())
                ? rule.getRuleString().trim()
                : "rule " + (ruleIndex + 1);
    }

    private boolean isParameterizableBoardCondition(RuleDto.Condition condition,
                                                     Map<String, DeviceNodeDto> nodeById,
                                                     Map<String, DeviceManifest> templateManifests) {
        String relation = SmvRelationUtils.normalizeRelation(condition.getRelation());
        if (relation == null
                || !Set.of(">", ">=", "<", "<=").contains(relation)
                || !hasText(condition.getValue())) {
            return false;
        }
        try {
            Double.parseDouble(condition.getValue().trim());
        } catch (NumberFormatException e) {
            return false;
        }
        DeviceNodeDto node = nodeById.get(condition.getDeviceName());
        if (node == null) {
            return false;
        }
        DeviceManifest manifest = manifestForTemplateName(node.getTemplateName(), templateManifests);
        if (manifest == null || !hasText(condition.getAttribute())) {
            return false;
        }
        DeviceManifest.InternalVariable variable = internalVariable(manifest, condition.getAttribute());
        if (variable == null) {
            variable = EnvironmentDomainUtils.resolveImpactDomain(manifest, condition.getAttribute());
        }
        return variable != null && variable.getLowerBound() != null && variable.getUpperBound() != null;
    }

    private void validateImpactedEnvironmentDomains(Map<String, String> errors,
                                                    String field,
                                                    String templateName,
                                                    DeviceManifest manifest) {
        if (manifest == null || manifest.getImpactedVariables() == null || manifest.getImpactedVariables().isEmpty()) {
            return;
        }
        for (String impacted : manifest.getImpactedVariables()) {
            if (!hasText(impacted)) {
                continue;
            }
            DeviceManifest.InternalVariable sameName = internalVariable(manifest, impacted);
            if (sameName != null && !isEnvironmentVariable(sameName)) {
                errors.putIfAbsent(field + ".templateName",
                        "Template '" + templateName + "' uses ImpactedVariable '" + impacted
                                + "' with a local InternalVariable of the same name. "
                                + "Use WorkingStates.Dynamics for local device state and reserve "
                                + "ImpactedVariables for shared environment variables.");
                continue;
            }
            if (EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted) == null) {
                errors.putIfAbsent(field + ".templateName",
                        "Template '" + templateName + "' impacts environment variable '" + impacted
                                + "', but its own manifest does not define that domain. Add EnvironmentDomains[].Name='"
                                + impacted + "', or declare a readable InternalVariable with the same name and IsInside=false.");
            }
        }
    }

    private void validateActiveEnvironmentDomainConsistency(Map<String, String> errors,
                                                            List<DeviceNodeDto> nodes,
                                                            Map<String, DeviceManifest> templateManifests) {
        if (nodes == null || templateManifests == null) {
            return;
        }
        Map<String, EnvironmentDomainSource> seen = new LinkedHashMap<>();
        for (int nodeIndex = 0; nodeIndex < nodes.size(); nodeIndex++) {
            DeviceNodeDto node = nodes.get(nodeIndex);
            if (node == null) continue;
            DeviceManifest manifest = manifestForTemplateName(node.getTemplateName(), templateManifests);
            if (manifest == null) continue;
            Set<String> readableNames = new HashSet<>();
            if (manifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                    if (variable == null || !hasText(variable.getName()) || !isEnvironmentVariable(variable)) continue;
                    readableNames.add(variable.getName());
                    registerActiveEnvironmentDomain(errors, seen, nodeIndex, node, variable.getName(), variable);
                }
            }
            if (manifest.getImpactedVariables() != null) {
                for (String impacted : manifest.getImpactedVariables()) {
                    if (!hasText(impacted) || readableNames.contains(impacted)) continue;
                    DeviceManifest.InternalVariable definition =
                            EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted);
                    if (definition != null) {
                        registerActiveEnvironmentDomain(errors, seen, nodeIndex, node, impacted, definition);
                    }
                }
            }
        }
    }

    private void registerActiveEnvironmentDomain(Map<String, String> errors,
                                                 Map<String, EnvironmentDomainSource> seen,
                                                 int nodeIndex,
                                                 DeviceNodeDto node,
                                                 String name,
                                                 DeviceManifest.InternalVariable definition) {
        String normalized = name.trim().toLowerCase(Locale.ROOT);
        EnvironmentDomainSource current = new EnvironmentDomainSource(
                name.trim(), deviceDisplayName(node), node.getTemplateName(), definition);
        EnvironmentDomainSource previous = seen.putIfAbsent(normalized, current);
        if (previous == null) {
            return;
        }
        String mismatch = !previous.literalName().equals(current.literalName())
                ? "name/case mismatch ('" + previous.literalName() + "' versus '" + current.literalName() + "')"
                : EnvironmentDomainUtils.incompatibility(previous.definition(), current.definition());
        if (mismatch != null) {
            errors.putIfAbsent("nodes[" + nodeIndex + "].templateName",
                    "Shared environment variable '" + previous.literalName() + "' has a " + mismatch
                            + " between device '" + previous.deviceLabel() + "' (template '"
                            + previous.templateName() + "') and device '" + current.deviceLabel()
                            + "' (template '" + current.templateName() + "'). Align the two template declarations.");
        }
    }

    private String deviceDisplayName(DeviceNodeDto node) {
        if (hasText(node.getLabel())) return node.getLabel().trim();
        if (hasText(node.getId())) return node.getId().trim();
        return hasText(node.getTemplateName()) ? node.getTemplateName().trim() : "unnamed device";
    }

    private record EnvironmentDomainSource(String literalName,
                                           String deviceLabel,
                                           String templateName,
                                           DeviceManifest.InternalVariable definition) {
    }

    private DeviceManifest manifestForTemplateName(String templateName,
                                                   Map<String, DeviceManifest> templateManifests) {
        if (!hasText(templateName) || templateManifests == null) {
            return null;
        }
        return templateManifests.get(templateName.trim().toLowerCase(Locale.ROOT));
    }

    private void validateNodeState(Map<String, String> errors,
                                   String field,
                                   DeviceNodeDto node,
                                   DeviceManifest manifest) {
        if (!hasModeStateMachine(manifest)) {
            return;
        }
        if (!hasText(node.getState())) {
            errors.putIfAbsent(field + ".state", "State is required for device templates with modes");
            return;
        }
        validateStateValues(errors, field + ".state", manifest, "=", node.getState());
    }

    private void validateStatelessNodeFields(Map<String, String> errors,
                                             String field,
                                             DeviceNodeDto node,
                                             boolean hasModeStateMachine) {
        if (hasModeStateMachine) {
            return;
        }
        if (hasText(node.getCurrentStateTrust())) {
            errors.putIfAbsent(field + ".currentStateTrust",
                    "currentStateTrust is only valid for device templates with modes");
        }
        if (hasText(node.getCurrentStatePrivacy())) {
            errors.putIfAbsent(field + ".currentStatePrivacy",
                    "currentStatePrivacy is only valid for device templates with modes");
        }
        String state = trimToNull(node.getState());
        if (state != null && !"Working".equalsIgnoreCase(state)) {
            errors.putIfAbsent(field + ".state",
                    "No-mode device state must be omitted or the UI placeholder 'Working'");
        }
    }

    private boolean hasModeStateMachine(DeviceManifest manifest) {
        return !modeNames(manifest).isEmpty() && !modeStates(manifest).isEmpty();
    }

    private void validateNodeTrust(Map<String, String> errors, String field, String value) {
        if (value == null) {
            return;
        }
        if (!hasText(value)) {
            errors.putIfAbsent(field, "Trust value cannot be blank when provided");
            return;
        }
        validateTrustValues(errors, field, "=", value);
    }

    private void validateNodeVariables(Map<String, String> errors,
                                       String field,
                                       List<VariableStateDto> variables,
                                       DeviceManifest manifest) {
        if (variables == null) {
            return;
        }
        Set<String> seen = new HashSet<>();
        for (int i = 0; i < variables.size(); i++) {
            VariableStateDto variable = variables.get(i);
            String prefix = field + "[" + i + "]";
            if (variable == null) {
                errors.putIfAbsent(prefix, "Variable item cannot be null");
                continue;
            }
            String name = trimToNull(variable.getName());
            String value = trimToNull(variable.getValue());
            if (name == null) {
                errors.putIfAbsent(prefix + ".name", "Variable name is required");
                continue;
            }
            if (!seen.add(name)) {
                errors.putIfAbsent(prefix + ".name", "Duplicate variable override: " + name);
            }
            if (value == null) {
                errors.putIfAbsent(prefix + ".value", "Variable value is required");
            }
            validateNodeTrust(errors, prefix + ".trust", variable.getTrust());

            DeviceManifest.InternalVariable manifestVariable = internalVariable(manifest, name);
            if (manifestVariable == null) {
                errors.putIfAbsent(prefix + ".name", "Unknown runtime variable for device template: " + name);
            } else if (isEnvironmentVariable(manifestVariable)) {
                errors.putIfAbsent(prefix + ".name",
                        "Environment variable belongs to the board environment pool, not a device instance: " + name);
            } else if (value != null) {
                validateVariableValues(errors, prefix + ".value", manifestVariable, "=", value);
            }
        }
    }

    private void validateNodePrivacies(Map<String, String> errors,
                                       String field,
                                       List<PrivacyStateDto> privacies,
                                       DeviceManifest manifest) {
        if (privacies == null) {
            return;
        }
        Set<String> seen = new HashSet<>();
        for (int i = 0; i < privacies.size(); i++) {
            PrivacyStateDto privacy = privacies.get(i);
            String prefix = field + "[" + i + "]";
            if (privacy == null) {
                errors.putIfAbsent(prefix, "Privacy item cannot be null");
                continue;
            }
            String name = trimToNull(privacy.getName());
            String value = trimToNull(privacy.getPrivacy());
            if (name == null) {
                errors.putIfAbsent(prefix + ".name", "Privacy target name is required");
                continue;
            }
            if (!seen.add(name)) {
                errors.putIfAbsent(prefix + ".name", "Duplicate privacy override: " + name);
            }
            if (value == null) {
                errors.putIfAbsent(prefix + ".privacy", "Privacy value is required");
            } else {
                validatePrivacyValues(errors, prefix + ".privacy", "=", value);
            }
            DeviceManifest.InternalVariable manifestVariable = internalVariable(manifest, name);
            if (manifestVariable == null) {
                errors.putIfAbsent(prefix + ".name",
                        "Unknown device-local variable privacy target: " + name);
            } else if (isEnvironmentVariable(manifestVariable)) {
                errors.putIfAbsent(prefix + ".name",
                        "Environment variable privacy belongs to the board environment pool, not a device instance: " + name);
            }
        }
    }

    private void validateRuleSemantics(Map<String, String> errors,
                                       String field,
                                       RuleDto rule,
                                       Map<String, DeviceNodeDto> nodesById,
                                       Map<String, DeviceManifest> templateManifests) {
        if (rule == null) {
            return;
        }

        RuleDto.Command command = rule.getCommand();
        if (command != null) {
            DeviceManifest commandManifest = manifestForDeviceRef(command.getDeviceName(), nodesById, templateManifests);
            DeviceManifest.API actionApi = findApi(commandManifest, command.getAction());
            if (commandManifest != null && hasText(command.getAction()) && actionApi == null) {
                errors.putIfAbsent(field + ".command.action",
                        "Unknown command API for device template: " + command.getAction());
            }
            if (hasText(command.getContentDevice()) != hasText(command.getContent())) {
                errors.putIfAbsent(field + ".command.content",
                        "contentDevice and content must be provided together");
            } else if (hasText(command.getContent())) {
                if (actionApi != null && !Boolean.TRUE.equals(actionApi.getAcceptsContent())) {
                    errors.putIfAbsent(field + ".command.content",
                            "Command API '" + actionApi.getName()
                                    + "' does not accept a content-sensitivity input");
                }
                DeviceManifest contentManifest = manifestForDeviceRef(command.getContentDevice(), nodesById, templateManifests);
                if (contentManifest != null && !hasContent(contentManifest, command.getContent())) {
                    errors.putIfAbsent(field + ".command.content",
                            "Unknown content for device template: " + command.getContent());
                }
            }
        }

        List<RuleDto.Condition> conditions = rule.getConditions();
        if (conditions == null) {
            return;
        }
        for (int conditionIndex = 0; conditionIndex < conditions.size(); conditionIndex++) {
            validateRuleConditionSemantics(errors,
                    field + ".conditions[" + conditionIndex + "]",
                    conditions.get(conditionIndex), nodesById, templateManifests);
        }
    }

    private void validateRuleConditionSemantics(Map<String, String> errors,
                                                String field,
                                                RuleDto.Condition condition,
                                                Map<String, DeviceNodeDto> nodesById,
                                                Map<String, DeviceManifest> templateManifests) {
        if (condition == null) {
            return;
        }
        DeviceManifest manifest = manifestForDeviceRef(condition.getDeviceName(), nodesById, templateManifests);
        if (manifest == null) {
            return;
        }

        String targetType = normalizeTargetType(condition.getTargetType());
        String attribute = trimToNull(condition.getAttribute());
        if (targetType == null) {
            errors.putIfAbsent(field + ".targetType",
                    "Condition targetType must be one of api, variable, mode, state");
            return;
        }
        if (attribute == null) {
            errors.putIfAbsent(field + ".attribute", "Condition attribute is required");
            return;
        }

        if ("api".equals(targetType)) {
            if (hasText(condition.getRelation()) || hasText(condition.getValue())) {
                errors.putIfAbsent(field + ".relation",
                        "API signal conditions must not include relation or value");
            }
            if (!hasSignalApi(manifest, attribute)) {
                errors.putIfAbsent(field + ".attribute",
                        "Unknown or non-signal API for rule condition: " + attribute);
            }
            return;
        }

        String relation = validateRelationValue(errors, field, condition.getRelation(), condition.getValue(), targetType);
        if (relation == null) {
            return;
        }

        switch (targetType) {
            case "variable" -> {
                DeviceManifest.InternalVariable variable = internalVariable(manifest, attribute);
                if (variable == null) {
                    errors.putIfAbsent(field + ".attribute",
                            "Unknown internal variable for rule condition: " + attribute);
                } else {
                    validateVariableValues(errors, field + ".value", variable, relation, condition.getValue());
                }
            }
            case "mode" -> {
                if (!hasMode(manifest, attribute)) {
                    errors.putIfAbsent(field + ".attribute", "Unknown mode for rule condition: " + attribute);
                } else {
                    validateModeValues(errors, field + ".value", manifest, attribute, relation, condition.getValue());
                }
            }
            case "state" -> {
                if (!"state".equalsIgnoreCase(attribute)) {
                    errors.putIfAbsent(field + ".attribute", "State rule conditions must use attribute 'state'");
                } else {
                    validateStateValues(errors, field + ".value", manifest, relation, condition.getValue());
                }
            }
            default -> errors.putIfAbsent(field + ".targetType",
                    "Condition targetType must be one of api, variable, mode, state");
        }
    }

    private void validateSpecConditionSemantics(Map<String, String> errors,
                                                String field,
                                                SpecConditionDto condition,
                                                Map<String, DeviceNodeDto> nodesById,
                                                Map<String, DeviceManifest> templateManifests) {
        if (condition == null) {
            return;
        }
        DeviceManifest manifest = manifestForDeviceRef(condition.getDeviceId(), nodesById, templateManifests);
        if (manifest == null) {
            return;
        }

        String targetType = normalizeSpecTargetType(condition.getTargetType());
        String key = trimToNull(condition.getKey());
        if (targetType == null) {
            errors.putIfAbsent(field + ".targetType",
                    "targetType must be one of: state, mode, variable, api, trust, privacy");
            return;
        }
        if (key == null) {
            errors.putIfAbsent(field + ".key", "Specification condition key is required");
            return;
        }
        String propertyScope = normalizePropertyScope(condition.getPropertyScope());
        if ("trust".equals(targetType) || "privacy".equals(targetType)) {
            if (propertyScope == null) {
                errors.putIfAbsent(field + ".propertyScope",
                        "propertyScope is required for trust/privacy and must be state or variable");
            }
        } else if (hasText(condition.getPropertyScope())) {
            errors.putIfAbsent(field + ".propertyScope",
                    "propertyScope is only valid for trust/privacy conditions");
        }

        String relation = validateRelationValue(errors, field, condition.getRelation(), condition.getValue(), targetType);
        if (relation == null) {
            return;
        }

        switch (targetType) {
            case "api" -> {
                validateEnumRelation(errors, field + ".relation", relation, "API signal");
                if (!hasSignalApi(manifest, key)) {
                    errors.putIfAbsent(field + ".key", "Unknown or non-signal API for specification: " + key);
                }
                validateBooleanValues(errors, field + ".value", relation, condition.getValue());
            }
            case "state" -> {
                validateEnumRelation(errors, field + ".relation", relation, "state");
                if (!"state".equalsIgnoreCase(key)) {
                    errors.putIfAbsent(field + ".key", "State specification conditions must use key 'state'");
                }
                validateStateValues(errors, field + ".value", manifest, relation, condition.getValue());
            }
            case "mode" -> {
                validateEnumRelation(errors, field + ".relation", relation, "mode");
                if (!hasMode(manifest, key)) {
                    errors.putIfAbsent(field + ".key", "Unknown mode for specification: " + key);
                } else {
                    validateModeValues(errors, field + ".value", manifest, key, relation, condition.getValue());
                }
            }
            case "variable" -> {
                DeviceManifest.InternalVariable variable = variableOrEnvKey(manifest, key);
                if (variable == null) {
                    errors.putIfAbsent(field + ".key",
                            "Unknown internal or environment variable for specification: " + key);
                } else {
                    validateVariableValues(errors, field + ".value", variable, relation, condition.getValue());
                }
            }
            case "trust" -> {
                validateEnumRelation(errors, field + ".relation", relation, "trust");
                validatePropertyReference(errors, field, propertyScope, key, manifest);
                validateTrustValues(errors, field + ".value", relation, condition.getValue());
            }
            case "privacy" -> {
                validateEnumRelation(errors, field + ".relation", relation, "privacy");
                validatePropertyReference(errors, field, propertyScope, key, manifest);
                validatePrivacyValues(errors, field + ".value", relation, condition.getValue());
            }
            default -> errors.putIfAbsent(field + ".targetType",
                    "targetType must be one of: state, mode, variable, api, trust, privacy");
        }
    }

    private Map<String, DeviceManifest> loadTemplateManifestMap(Long userId) {
        if (deviceTemplateRepo == null) {
            return Collections.emptyMap();
        }
        List<DeviceTemplatePo> templates = deviceTemplateRepo.findByUserId(userId);
        if (templates == null || templates.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<String, DeviceManifest> manifests = new HashMap<>();
        for (DeviceTemplatePo template : templates) {
            if (template == null || !hasText(template.getName())) {
                continue;
            }
            DeviceTemplateDto dto = deviceTemplateMapper.toDto(template);
            if (dto == null || dto.getManifest() == null) {
                continue;
            }
            DeviceManifest manifest = dto.getManifest();
            manifests.put(template.getName().trim().toLowerCase(Locale.ROOT), manifest);
            if (hasText(manifest.getName())) {
                manifests.put(manifest.getName().trim().toLowerCase(Locale.ROOT), manifest);
            }
        }
        return manifests;
    }

    private Map<String, DeviceNodeDto> nodesById(List<DeviceNodeDto> nodes) {
        if (nodes == null || nodes.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<String, DeviceNodeDto> result = new HashMap<>();
        for (DeviceNodeDto node : nodes) {
            if (node != null && hasText(node.getId())) {
                result.put(node.getId().trim(), node);
            }
        }
        return result;
    }

    private DeviceManifest manifestForDeviceRef(String deviceRef,
                                                Map<String, DeviceNodeDto> nodesById,
                                                Map<String, DeviceManifest> templateManifests) {
        if (!hasText(deviceRef) || nodesById == null || templateManifests == null) {
            return null;
        }
        DeviceNodeDto node = nodesById.get(deviceRef.trim());
        if (node == null || !hasText(node.getTemplateName())) {
            return null;
        }
        return templateManifests.get(node.getTemplateName().trim().toLowerCase(Locale.ROOT));
    }

    private String validateRelationValue(Map<String, String> errors,
                                         String field,
                                         String rawRelation,
                                         String rawValue,
                                         String targetType) {
        if (!hasText(rawRelation) || !hasText(rawValue)) {
            errors.putIfAbsent(field + ".relation",
                    "Condition relation and value are required for targetType '" + targetType + "'");
            return null;
        }
        String relation = SmvRelationUtils.normalizeRelation(rawRelation);
        if (!SmvRelationUtils.isSupportedRelation(relation)) {
            errors.putIfAbsent(field + ".relation", "Unsupported relation: " + rawRelation);
            return null;
        }
        if (("in".equals(relation) || "not in".equals(relation))
                && SmvRelationUtils.splitRuleValues(rawValue).isEmpty()) {
            errors.putIfAbsent(field + ".value", "Condition value list cannot be empty");
            return null;
        }
        return relation;
    }

    private void validateEnumRelation(Map<String, String> errors,
                                      String field,
                                      String relation,
                                      String label) {
        if (!"=".equals(relation) && !"!=".equals(relation)
                && !"in".equals(relation) && !"not in".equals(relation)) {
            errors.putIfAbsent(field,
                    label + " conditions support only =, !=, IN, and NOT_IN");
        }
    }

    private void validateStateValues(Map<String, String> errors,
                                     String field,
                                     DeviceManifest manifest,
                                     String relation,
                                     String rawValue) {
        Map<String, List<String>> modeStates = modeStates(manifest);
        List<String> modes = modeNames(manifest);
        if (modes.isEmpty() || modeStates.isEmpty()) {
            errors.putIfAbsent(field, "Device template has no legal states");
            return;
        }
        List<String> candidates = ("in".equals(relation) || "not in".equals(relation))
                ? SmvRelationUtils.splitStateRuleValues(rawValue, modes.size())
                : List.of(rawValue.trim());
        if (candidates.isEmpty()) {
            errors.putIfAbsent(field, "State condition value cannot be empty");
            return;
        }
        if (("=".equals(relation) || "!=".equals(relation)) && candidates.size() != 1) {
            errors.putIfAbsent(field, "State relation '" + relation + "' requires exactly one value");
            return;
        }
        for (String candidate : candidates) {
            if (!isLegalStateCandidate(candidate, modes, modeStates)) {
                errors.putIfAbsent(field, "Illegal state value for device template: " + candidate);
                return;
            }
        }
    }

    private void validateModeValues(Map<String, String> errors,
                                    String field,
                                    DeviceManifest manifest,
                                    String mode,
                                    String relation,
                                    String rawValue) {
        Map<String, List<String>> modeStates = modeStates(manifest);
        List<String> legalStates = modeStates.get(mode);
        if (legalStates == null || legalStates.isEmpty()) {
            errors.putIfAbsent(field, "Mode has no legal values: " + mode);
            return;
        }
        List<String> candidates = ("in".equals(relation) || "not in".equals(relation))
                ? SmvRelationUtils.splitRuleValues(rawValue)
                : List.of(rawValue.trim());
        if (candidates.isEmpty()) {
            errors.putIfAbsent(field, "Mode condition value cannot be empty");
            return;
        }
        if (("=".equals(relation) || "!=".equals(relation)) && candidates.size() != 1) {
            errors.putIfAbsent(field, "Mode relation '" + relation + "' requires exactly one value");
            return;
        }
        for (String candidate : candidates) {
            String cleaned = DeviceSmvDataFactory.cleanStateName(candidate);
            if (cleaned == null || !legalStates.contains(cleaned)) {
                errors.putIfAbsent(field, "Illegal mode value '" + candidate + "' for mode '" + mode + "'");
                return;
            }
        }
    }

    private boolean isLegalStateCandidate(String rawCandidate,
                                          List<String> modes,
                                          Map<String, List<String>> modeStates) {
        if (!hasText(rawCandidate)) {
            return false;
        }
        String candidate = rawCandidate.trim();
        if (candidate.contains(";")) {
            String[] segments = candidate.split(";", -1);
            if (segments.length != modes.size()) {
                return false;
            }
            boolean hasConcreteSegment = false;
            for (int i = 0; i < modes.size(); i++) {
                String cleaned = DeviceSmvDataFactory.cleanStateName(segments[i]);
                if (!hasText(cleaned) || "_".equals(cleaned)) {
                    continue;
                }
                List<String> legalStates = modeStates.get(modes.get(i));
                if (legalStates == null || !legalStates.contains(cleaned)) {
                    return false;
                }
                hasConcreteSegment = true;
            }
            return hasConcreteSegment;
        }

        String cleaned = DeviceSmvDataFactory.cleanStateName(candidate);
        if (!hasText(cleaned)) {
            return false;
        }
        int matches = 0;
        for (String mode : modes) {
            List<String> legalStates = modeStates.get(mode);
            if (legalStates != null && legalStates.contains(cleaned)) {
                matches++;
            }
        }
        return matches == 1;
    }

    private void validateBooleanValues(Map<String, String> errors,
                                       String field,
                                       String relation,
                                       String rawValue) {
        validateLiteralValues(errors, field, relation, rawValue, Set.of("TRUE", "FALSE"), "TRUE or FALSE");
    }

    private void validateTrustValues(Map<String, String> errors,
                                     String field,
                                     String relation,
                                     String rawValue) {
        validateLiteralValues(errors, field, relation, rawValue,
                Set.of("trusted", "untrusted"), "trusted or untrusted");
    }

    private void validatePrivacyValues(Map<String, String> errors,
                                       String field,
                                       String relation,
                                       String rawValue) {
        validateLiteralValues(errors, field, relation, rawValue,
                Set.of("public", "private"), "public or private");
    }

    private void validateLiteralValues(Map<String, String> errors,
                                       String field,
                                       String relation,
                                       String rawValue,
                                       Set<String> allowed,
                                       String label) {
        List<String> candidates = ("in".equals(relation) || "not in".equals(relation))
                ? SmvRelationUtils.splitRuleValues(rawValue)
                : List.of(rawValue.trim());
        for (String candidate : candidates) {
            String normalized = candidate.trim();
            boolean found = allowed.stream().anyMatch(v -> v.equalsIgnoreCase(normalized));
            if (!found) {
                errors.putIfAbsent(field, "Value must be " + label + ": " + candidate);
                return;
            }
        }
    }

    private void validateVariableValues(Map<String, String> errors,
                                        String field,
                                        DeviceManifest.InternalVariable variable,
                                        String relation,
                                        String rawValue) {
        if (variable == null || !hasText(rawValue)) {
            return;
        }
        List<String> candidates = ("in".equals(relation) || "not in".equals(relation))
                ? SmvRelationUtils.splitRuleValues(rawValue)
                : List.of(rawValue.trim());
        if (candidates.isEmpty()) {
            errors.putIfAbsent(field, "Variable condition value cannot be empty");
            return;
        }
        if (("=".equals(relation) || "!=".equals(relation)) && candidates.size() != 1) {
            errors.putIfAbsent(field, "Variable relation '" + relation + "' requires exactly one value");
            return;
        }

        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            validateEnumRelation(errors, field, relation, "enum variable");
            Set<String> allowed = new HashSet<>();
            for (String value : variable.getValues()) {
                if (hasText(value)) {
                    allowed.add(cleanEnumLiteral(value));
                }
            }
            for (String candidate : candidates) {
                if (!allowed.contains(cleanEnumLiteral(candidate))) {
                    errors.putIfAbsent(field,
                            "Illegal enum value for variable '" + variable.getName() + "': " + candidate);
                    return;
                }
            }
            return;
        }

        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            int lower = variable.getLowerBound();
            int upper = variable.getUpperBound();
            for (String candidate : candidates) {
                try {
                    int parsed = Integer.parseInt(candidate.trim());
                    if (parsed < lower || parsed > upper) {
                        errors.putIfAbsent(field, "Variable value out of range for '" + variable.getName()
                                + "': " + candidate + " (allowed " + lower + ".." + upper + ")");
                        return;
                    }
                } catch (NumberFormatException e) {
                    errors.putIfAbsent(field,
                            "Variable value must be an integer for '" + variable.getName() + "': " + candidate);
                    return;
                }
            }
        }
    }

    private boolean hasApi(DeviceManifest manifest, String apiName) {
        return findApi(manifest, apiName) != null;
    }

    private DeviceManifest.API findApi(DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || !hasText(apiName)) {
            return null;
        }
        for (DeviceManifest.API api : manifest.getApis()) {
            if (api != null && apiName.trim().equals(api.getName())) {
                return api;
            }
        }
        return null;
    }

    private boolean hasSignalApi(DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || !hasText(apiName)) {
            return false;
        }
        for (DeviceManifest.API api : manifest.getApis()) {
            if (api != null && apiName.trim().equals(api.getName()) && Boolean.TRUE.equals(api.getSignal())) {
                return true;
            }
        }
        return false;
    }

    private boolean hasContent(DeviceManifest manifest, String contentName) {
        if (manifest == null || manifest.getContents() == null || !hasText(contentName)) {
            return false;
        }
        for (DeviceManifest.Content content : manifest.getContents()) {
            if (content != null && contentName.trim().equals(content.getName())) {
                return true;
            }
        }
        return false;
    }

    private boolean hasInternalVariable(DeviceManifest manifest, String variableName) {
        return internalVariable(manifest, variableName) != null;
    }

    private boolean hasVariableOrEnvKey(DeviceManifest manifest, String key) {
        return variableOrEnvKey(manifest, key) != null;
    }

    private DeviceManifest.InternalVariable variableOrEnvKey(DeviceManifest manifest, String key) {
        if (!hasText(key)) {
            return null;
        }
        String normalized = key.trim();
        return internalVariable(manifest, normalized);
    }

    private DeviceManifest.InternalVariable internalVariable(DeviceManifest manifest, String variableName) {
        if (manifest == null || manifest.getInternalVariables() == null || !hasText(variableName)) {
            return null;
        }
        String normalized = variableName.trim();
        for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
            if (variable != null && normalized.equals(variable.getName())) {
                return variable;
            }
        }
        return null;
    }

    private boolean hasMode(DeviceManifest manifest, String modeName) {
        if (!hasText(modeName)) {
            return false;
        }
        return modeNames(manifest).contains(modeName.trim());
    }

    private List<String> modeNames(DeviceManifest manifest) {
        if (manifest == null || manifest.getModes() == null) {
            return List.of();
        }
        return manifest.getModes().stream()
                .filter(this::hasText)
                .map(String::trim)
                .toList();
    }

    private Map<String, List<String>> modeStates(DeviceManifest manifest) {
        List<String> modes = modeNames(manifest);
        if (modes.isEmpty() || manifest == null || manifest.getWorkingStates() == null) {
            return Collections.emptyMap();
        }
        Map<String, List<String>> result = new LinkedHashMap<>();
        for (String mode : modes) {
            result.put(mode, new ArrayList<>());
        }

        boolean singleMode = modes.size() == 1;
        for (DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || !hasText(state.getName())) {
                continue;
            }
            if (singleMode) {
                addUniqueState(result.get(modes.get(0)), DeviceSmvDataFactory.cleanStateName(state.getName()));
                continue;
            }
            String[] parts = state.getName().split(";");
            for (int i = 0; i < parts.length && i < modes.size(); i++) {
                addUniqueState(result.get(modes.get(i)), DeviceSmvDataFactory.cleanStateName(parts[i]));
            }
        }
        return result;
    }

    private void addUniqueState(List<String> states, String state) {
        if (states != null && hasText(state) && !states.contains(state)) {
            states.add(state);
        }
    }

    private void validatePropertyReference(Map<String, String> errors,
                                           String field,
                                           String scope,
                                           String key,
                                           DeviceManifest manifest) {
        if (scope == null) {
            return;
        }
        if ("variable".equals(scope)) {
            if (!hasInternalVariable(manifest, key)) {
                errors.putIfAbsent(field + ".key", "Unknown property variable for specification: " + key);
            }
            return;
        }
        if (!hasMode(manifest, key)) {
            errors.putIfAbsent(field + ".key", "Unknown state-label mode for specification: " + key);
        }
    }

    private String normalizePropertyScope(String value) {
        if (!hasText(value)) {
            return null;
        }
        String normalized = value.trim().toLowerCase(Locale.ROOT);
        return "state".equals(normalized) || "variable".equals(normalized) ? normalized : null;
    }

    private String normalizeTargetType(String targetType) {
        if (!hasText(targetType)) {
            return null;
        }
        String normalized = targetType.trim().toLowerCase(Locale.ROOT);
        return Set.of("api", "variable", "mode", "state").contains(normalized) ? normalized : null;
    }

    private String normalizeSpecTargetType(String targetType) {
        if (!hasText(targetType)) {
            return null;
        }
        String normalized = targetType.trim().toLowerCase(Locale.ROOT);
        return Set.of("state", "mode", "variable", "api", "trust", "privacy").contains(normalized)
                ? normalized : null;
    }

    private String trimToNull(String value) {
        if (!hasText(value)) {
            return null;
        }
        return value.trim();
    }

    private String cleanEnumLiteral(String value) {
        return value == null ? "" : value.trim().replace(" ", "");
    }

    private Set<String> nodeIds(List<DeviceNodeDto> nodes) {
        Set<String> ids = new HashSet<>();
        if (nodes == null) {
            return ids;
        }
        for (DeviceNodeDto node : nodes) {
            if (node == null || !hasText(node.getId())) {
                continue;
            }
            ids.add(node.getId().trim());
        }
        return ids;
    }

    private void requireBoardNodeRef(Map<String, String> errors,
                                     String field,
                                     String value,
                                     Set<String> nodeIds,
                                     String message) {
        if (!hasText(value)) {
            return;
        }
        String ref = value.trim();
        if (!nodeIds.contains(ref)) {
            errors.putIfAbsent(field, message + ": " + ref);
        }
    }

    private boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    @Override
    public CollectionMutationResultDto<RuleDto> addRule(Long userId, RuleDto rule) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                RuleDto canonicalRule = canonicalizeRuleRelationsForStorage(rule);
                canonicalRule.setId(null); // new rule, let DB assign ID
                List<RuleDto> nextRules = new ArrayList<>(getRulesInternal(userId));
                nextRules.add(canonicalRule);
                List<DeviceNodeDto> currentNodes = getNodesInternal(userId);
                validateNoIdenticalRules(nextRules, currentNodes);
                validateBoardReferences(userId, currentNodes, nextRules, null);
                RulePo po = ruleMapper.toEntity(canonicalRule, userId);
                po.setExecutionOrder(nextRules.size() - 1);
                RulePo saved = ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
                RuleDto created = ruleMapper.toDto(saved);
                return CollectionMutationResultDto.of("created", created, getRulesInternal(userId));
            });
        }
    }

    @Override
    public List<RuleDto> reorderRules(Long userId, List<Long> ruleIds) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<RuleDto> current = getRulesInternal(userId);
                List<Long> requested = ruleIds == null ? List.of() : List.copyOf(ruleIds);
                Set<Long> uniqueRequested = new LinkedHashSet<>(requested);
                if (uniqueRequested.size() != requested.size()) {
                    throw new BadRequestException("Rule execution order contains duplicate rule ids.");
                }

                Map<Long, RuleDto> currentById = current.stream()
                        .filter(Objects::nonNull)
                        .filter(rule -> rule.getId() != null)
                        .collect(Collectors.toMap(RuleDto::getId, rule -> rule, (first, ignored) -> first,
                                LinkedHashMap::new));
                if (requested.size() != current.size()
                        || !currentById.keySet().equals(uniqueRequested)) {
                    throw new ConflictException(
                            "The rule list changed before its execution order was saved. Refresh the board and try again.");
                }

                List<RuleDto> reordered = requested.stream().map(currentById::get).toList();
                return saveRulesInternal(userId, reordered);
            });
        }
    }

    private void validateNoIdenticalRules(List<RuleDto> rules, List<DeviceNodeDto> nodes) {
        List<RuleDto> safeRules = rules == null ? List.of() : rules;
        for (int left = 0; left < safeRules.size(); left++) {
            RuleDto candidate = safeRules.get(left);
            for (int right = 0; right < left; right++) {
                RuleDto existing = safeRules.get(right);
                if (RuleSemanticSignature.exactlyMatches(candidate, existing)) {
                    throw new ConflictException(
                            "The board cannot contain two identical automation rules: "
                                    + describeRuleForUser(existing, nodes)
                                    + ". Change the trigger or action, or remove the duplicate.");
                }
            }
        }
    }

    private String describeRuleForUser(RuleDto rule, List<DeviceNodeDto> nodes) {
        Map<String, String> labelsById = (nodes == null ? List.<DeviceNodeDto>of() : nodes).stream()
                .filter(Objects::nonNull)
                .filter(node -> hasText(node.getId()))
                .collect(Collectors.toMap(
                        node -> node.getId().trim(),
                        node -> hasText(node.getLabel()) ? node.getLabel().trim() : "device",
                        (first, ignored) -> first));
        String conditions = (rule == null || rule.getConditions() == null
                ? List.<RuleDto.Condition>of()
                : rule.getConditions()).stream()
                .filter(Objects::nonNull)
                .map(condition -> {
                    String device = labelsById.getOrDefault(condition.getDeviceName(), "device");
                    String key = hasText(condition.getAttribute()) ? condition.getAttribute().trim() : "condition";
                    if ("api".equalsIgnoreCase(condition.getTargetType())) {
                        return device + " triggers " + key;
                    }
                    return device + "." + key + " "
                            + (hasText(condition.getRelation()) ? condition.getRelation().trim() : "=") + " "
                            + (hasText(condition.getValue()) ? condition.getValue().trim() : "value");
                })
                .collect(Collectors.joining(" AND "));
        RuleDto.Command command = rule == null ? null : rule.getCommand();
        String target = command == null
                ? "device.action"
                : labelsById.getOrDefault(command.getDeviceName(), "device") + "."
                    + (hasText(command.getAction()) ? command.getAction().trim() : "action");
        return "IF " + (conditions.isBlank() ? "condition" : conditions) + " THEN " + target;
    }

    private void validateNoIdenticalSpecifications(List<SpecificationDto> specs, List<DeviceNodeDto> nodes) {
        List<SpecificationDto> safeSpecs = specs == null ? List.of() : specs;
        for (int left = 0; left < safeSpecs.size(); left++) {
            SpecificationDto candidate = safeSpecs.get(left);
            for (int right = 0; right < left; right++) {
                SpecificationDto existing = safeSpecs.get(right);
                if (SpecificationSemanticSignature.exactlyMatches(candidate, existing)) {
                    throw new ConflictException(
                            "The board cannot contain two identical specifications: "
                                    + describeSpecificationForUser(existing, nodes)
                                    + ". Change a checked condition or remove the duplicate.");
                }
            }
        }
    }

    private String describeSpecificationForUser(SpecificationDto spec, List<DeviceNodeDto> nodes) {
        Map<String, String> labelsById = (nodes == null ? List.<DeviceNodeDto>of() : nodes).stream()
                .filter(Objects::nonNull)
                .filter(node -> hasText(node.getId()))
                .collect(Collectors.toMap(
                        node -> node.getId().trim(),
                        node -> hasText(node.getLabel()) ? node.getLabel().trim() : "device",
                        (first, ignored) -> first));
        List<String> descriptions = new ArrayList<>();
        appendSpecificationConditionDescriptions(descriptions, "A", spec.getAConditions(), labelsById);
        appendSpecificationConditionDescriptions(descriptions, "IF", spec.getIfConditions(), labelsById);
        appendSpecificationConditionDescriptions(descriptions, "THEN", spec.getThenConditions(), labelsById);
        String template = hasText(spec.getTemplateLabel()) ? spec.getTemplateLabel().trim() : "Formal specification";
        return descriptions.isEmpty() ? template : template + " [" + String.join("; ", descriptions) + "]";
    }

    private void appendSpecificationConditionDescriptions(List<String> output,
                                                           String side,
                                                           List<SpecConditionDto> conditions,
                                                           Map<String, String> labelsById) {
        for (SpecConditionDto condition : conditions == null ? List.<SpecConditionDto>of() : conditions) {
            if (condition == null) {
                continue;
            }
            String device = labelsById.getOrDefault(condition.getDeviceId(), "device");
            output.add(side + ": " + device + "."
                    + (hasText(condition.getKey()) ? condition.getKey().trim() : "condition") + " "
                    + (hasText(condition.getRelation()) ? condition.getRelation().trim() : "=") + " "
                    + (hasText(condition.getValue()) ? condition.getValue().trim() : "value"));
        }
    }

    @Override
    public CollectionMutationResultDto<RuleDto> removeRule(Long userId, long ruleId) {
        return removeRuleIfUnchanged(userId, ruleId, null);
    }

    @Override
    public CollectionMutationResultDto<RuleDto> removeRuleIfUnchanged(
            Long userId, long ruleId, RuleDto expected) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                List<RulePo> existing = ruleRepo.findByUserId(userId);
                RulePo removed = existing.stream()
                        .filter(rule -> rule.getId() != null && rule.getId() == ruleId)
                        .findFirst()
                        .orElseThrow(() -> new ResourceNotFoundException("Rule", ruleId));
                RuleDto current = ruleMapper.toDto(removed);
                if (expected != null && !Objects.equals(expected, current)) {
                    throw new ConflictException(
                            "The rule changed after confirmation. Review the current rule before deleting it.");
                }
                ruleRepo.deleteById(ruleId);
                List<RuleDto> remaining = getRulesInternal(userId);
                return CollectionMutationResultDto.of("deleted", current, remaining);
            });
        }
    }

    @Override
    @Transactional
    public BoardLayoutDto getLayout(Long userId) {
        requireActiveUserForWrite(userId);
        BoardLayoutPo po = layoutRepo.findByUserId(userId).orElseGet(() -> {
            BoardLayoutPo created = BoardLayoutPo.builder()
                    .userId(userId)
                    .canvasPanX(0.0).canvasPanY(0.0).canvasZoom(1.0)
                    .controlPanelCollapsed(false).controlPanelWidth(320.0)
                    .controlPanelActiveSection("templates")
                    .inspectorPanelCollapsed(false).inspectorPanelWidth(320.0)
                    .inspectorPanelActiveSection("devices")
                    .build();
            return layoutRepo.save(Objects.requireNonNull(created, "layout to save must not be null"));
        });

        return boardLayoutMapper.toDto(po);
    }

    @Transactional
    @Override
    public BoardLayoutDto saveLayout(Long userId, BoardLayoutDto layout) {
        requireActiveUserForWrite(userId);
        BoardLayoutPo existing = layoutRepo.findByUserId(userId).orElse(null);
        Long id = existing != null ? existing.getId() : null;

        BoardLayoutPo po = boardLayoutMapper.toEntity(layout, id, userId);
        layoutRepo.save(Objects.requireNonNull(po, "layout to save must not be null"));

        return getLayout(userId);
    }

    @Override
    @Transactional(readOnly = true)
    public List<DeviceTemplateDto> getDeviceTemplates(Long userId) {
        if (userId == null || userRepository.findById(userId).isEmpty()) {
            throw UnauthorizedException.invalidToken();
        }
        return getDeviceTemplatesInternal(userId);
    }

    private List<DeviceTemplateDto> getDeviceTemplatesInternal(Long userId) {
        return deviceTemplateRepo.findByUserId(userId).stream()
                .map(deviceTemplateMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public DeviceTemplateDto addDeviceTemplate(Long userId, DeviceTemplateDto dto) {
        requireActiveUserForWrite(userId);
        DeviceTemplateDto safeDto = Objects.requireNonNull(dto, "template dto must not be null");
        if (safeDto.getManifest() == null) {
            throw new BadRequestException("Template manifest is required");
        }

        String rawName = safeDto.getName() != null ? safeDto.getName().trim() : null;
        if (rawName == null || rawName.isBlank()) {
            throw new BadRequestException("Template name is required");
        }
        if (rawName.length() > 100) {
            throw new BadRequestException("Template name must be at most 100 characters");
        }

        final String canonicalName = rawName;
        if (!SAFE_TEMPLATE_NAME.matcher(canonicalName).matches()) {
            throw new BadRequestException(
                    "Template name '" + canonicalName
                    + "' contains non-ASCII characters. Only printable ASCII characters are allowed.");
        }
        safeDto.setName(canonicalName);
        safeDto.getManifest().setName(canonicalName);
        deviceTemplateSchemaValidator.validateManifest(canonicalName, safeDto.getManifest());
        validateTemplateManifestForNuSmv(canonicalName, safeDto.getManifest());

        boolean duplicated = deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(userId, canonicalName);
        if (duplicated) {
            throw ConflictException.duplicateTemplate(canonicalName);
        }

        String json = deviceTemplateSchemaValidator.toCanonicalJson(safeDto.getManifest());

        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .userId(userId)
                .name(canonicalName)
                .manifestJson(json)
                .defaultTemplate(false)
                .build();

        DeviceTemplatePo saved;
        try {
            saved = deviceTemplateRepo.saveAndFlush(Objects.requireNonNull(po, "template to save must not be null"));
        } catch (DataIntegrityViolationException e) {
            throw ConflictException.duplicateTemplate(canonicalName);
        }
        runTemplateNuSmvPrecheck(userId, canonicalName, safeDto.getManifest());

        return deviceTemplateMapper.toDto(saved);
    }

    @Override
    public DeviceTemplateDeletionResultDto previewDeviceTemplateDeletion(Long userId, Long templateId) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                return buildTemplateDeletionPlan(userId, templateId).preview();
            });
        }
    }

    @Override
    public DeviceTemplateDeletionResultDto deleteDeviceTemplate(
            Long userId, Long templateId, String expectedImpactToken) {
        if (!hasText(expectedImpactToken)) {
            throw new BadRequestException("Template-deletion impact token is required.");
        }
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                DeviceTemplateDeletionPlan plan = buildTemplateDeletionPlan(userId, templateId);
                DeviceTemplateDeletionResultDto preview = plan.preview();
                if (!MessageDigest.isEqual(
                        preview.getImpactToken().getBytes(StandardCharsets.UTF_8),
                        expectedImpactToken.trim().getBytes(StandardCharsets.UTF_8))) {
                    throw new TemplateDeletionConflictException(
                            "TEMPLATE_DELETION_PREVIEW_STALE",
                            "The device type or its usage changed after preview. Review the current impact before deleting.",
                            preview);
                }
                if (!preview.isCanDelete()) {
                    throw new TemplateDeletionConflictException(
                            "TEMPLATE_DELETION_BLOCKED",
                            "This device type is still used by canvas devices.",
                            preview);
                }

                deviceTemplateRepo.delete(plan.templatePo());
                deviceTemplateRepo.flush();
                return DeviceTemplateDeletionResultDto.builder()
                        .operation("deleted")
                        .impactToken(preview.getImpactToken())
                        .canDelete(true)
                        .template(preview.getTemplate())
                        .deletedTemplate(preview.getTemplate())
                        .blockers(List.of())
                        .currentTemplates(getDeviceTemplatesInternal(userId))
                        .build();
            });
        }
    }

    private DeviceTemplateDeletionPlan buildTemplateDeletionPlan(Long userId, Long templateId) {
        if (templateId == null || templateId <= 0) {
            throw new BadRequestException("Template id must be a positive integer");
        }
        DeviceTemplatePo po = deviceTemplateRepo.findById(templateId)
                .orElseThrow(() -> new ResourceNotFoundException("Template", templateId));
        if (!Objects.equals(po.getUserId(), userId)) {
            throw new ForbiddenException("Access denied to this template");
        }

        DeviceTemplateDto target = deviceTemplateMapper.toDto(po);
        List<DeviceTemplateDeletionBlockerDto> blockers = nodeRepo.findByUserId(userId).stream()
                .filter(Objects::nonNull)
                .filter(node -> hasText(node.getTemplateName())
                        && node.getTemplateName().trim().equalsIgnoreCase(po.getName()))
                .sorted(Comparator.comparing(DeviceNodePo::getId, Comparator.nullsLast(String.CASE_INSENSITIVE_ORDER)))
                .map(node -> DeviceTemplateDeletionBlockerDto.builder()
                        .reasonCode("DEVICE_INSTANCE_USES_TEMPLATE")
                        .itemId(node.getId())
                        .itemLabel(firstText(node.getLabel(), node.getId()))
                        .reason("This canvas device instance uses the device type.")
                        .build())
                .toList();
        List<DeviceTemplateDto> currentTemplates = getDeviceTemplatesInternal(userId);
        String impactToken = templateDeletionImpactToken(target, blockers);
        DeviceTemplateDeletionResultDto preview = DeviceTemplateDeletionResultDto.builder()
                .operation("preview")
                .impactToken(impactToken)
                .canDelete(blockers.isEmpty())
                .template(target)
                .blockers(blockers)
                .currentTemplates(currentTemplates)
                .build();
        return new DeviceTemplateDeletionPlan(po, preview);
    }

    private String templateDeletionImpactToken(
            DeviceTemplateDto template, List<DeviceTemplateDeletionBlockerDto> blockers) {
        Map<String, Object> impact = new LinkedHashMap<>();
        impact.put("contract", "device-template-deletion-v1");
        impact.put("template", template);
        impact.put("blockers", blockers != null ? blockers : List.of());
        try {
            return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256")
                    .digest(JsonUtils.toJson(impact).getBytes(StandardCharsets.UTF_8)));
        } catch (NoSuchAlgorithmException e) {
            throw new InternalServerException("Unable to create template-deletion impact token", e);
        }
    }

    private record DeviceTemplateDeletionPlan(
            DeviceTemplatePo templatePo, DeviceTemplateDeletionResultDto preview) {
    }

    @Override
    public DefaultTemplateResetResultDto previewDefaultTemplateReset(Long userId) {
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                return buildDefaultTemplateResetPlan(userId).preview();
            });
        }
    }

    @Override
    public DefaultTemplateResetResultDto resetDefaultTemplates(Long userId, String expectedImpactToken) {
        if (!hasText(expectedImpactToken)) {
            throw new BadRequestException("Default-template reset impact token is required.");
        }
        synchronized (getUserWriteLock(userId)) {
            return transactionTemplate.execute(status -> {
                requireActiveUserForWrite(userId);
                DefaultTemplateResetPlan plan = buildDefaultTemplateResetPlan(userId);
                if (!Objects.equals(plan.preview().getImpactToken(), expectedImpactToken.trim())) {
                    throw new ConflictException(
                            "The device types or board changed after the reset preview. Review the current impact before resetting.");
                }
                if (!plan.validationErrors().isEmpty()) {
                    throw new ValidationException(plan.validationErrors());
                }

                Set<String> defaultNames = plan.defaultDefinitions().stream()
                        .map(DeviceTemplatePo::getName)
                        .filter(this::hasText)
                        .map(name -> name.trim().toLowerCase(Locale.ROOT))
                        .collect(Collectors.toCollection(LinkedHashSet::new));
                int deleted = deviceTemplateRepo.deleteDefaultsForReset(userId, List.copyOf(defaultNames));
                List<DeviceTemplatePo> savedDefaults = deviceTemplateRepo.saveAllAndFlush(
                        plan.defaultDefinitions());
                if (savedDefaults.size() != plan.defaultDefinitions().size()) {
                    throw new InternalServerException(
                            "Default device type reset was incomplete; the transaction was rolled back.");
                }
                log.info("Reset default templates for user {}: deleted {}, imported {}",
                        userId, deleted, savedDefaults.size());

                for (DeviceTemplatePo saved : savedDefaults) {
                    DeviceTemplateDto dto = deviceTemplateMapper.toDto(saved);
                    validateTemplateManifestForNuSmv(dto.getName(), dto.getManifest());
                    runTemplateNuSmvPrecheck(userId, dto.getName(), dto.getManifest());
                }

                List<DeviceNodeDto> nodes = getNodesInternal(userId);
                validateBoardReferences(userId, nodes, getRulesInternal(userId), getSpecsInternal(userId));
                List<BoardEnvironmentVariableDto> savedEnvironment =
                        replaceEnvironmentVariablesInternal(userId, plan.projectedEnvironment());
                List<DeviceTemplateDto> currentTemplates = deviceTemplateRepo.findByUserId(userId).stream()
                        .map(deviceTemplateMapper::toDto)
                        .toList();

                DefaultTemplateResetResultDto preview = plan.preview();
                return DefaultTemplateResetResultDto.builder()
                        .operation("reset")
                        .impactToken(preview.getImpactToken())
                        .canApply(true)
                        .templateChanges(preview.getTemplateChanges())
                        .affectedDevices(preview.getAffectedDevices())
                        .blockers(List.of())
                        .environmentChanges(preview.getEnvironmentChanges())
                        .currentTemplates(currentTemplates)
                        .environmentVariables(savedEnvironment)
                        .build();
            });
        }
    }

    private DefaultTemplateResetPlan buildDefaultTemplateResetPlan(Long userId) {
        List<DeviceTemplatePo> defaultDefinitions = new ArrayList<>(
                deviceTemplateService.getDefaultTemplateDefinitions(userId));
        if (defaultDefinitions.isEmpty()) {
            throw new InternalServerException("No bundled default device types are available to reset.");
        }
        defaultDefinitions.sort(Comparator.comparing(
                template -> firstText(template.getName(), ""), String.CASE_INSENSITIVE_ORDER));
        List<DeviceTemplateDto> defaultDtos = defaultDefinitions.stream()
                .map(deviceTemplateMapper::toDto)
                .toList();
        for (DeviceTemplateDto dto : defaultDtos) {
            validateTemplateManifestForNuSmv(dto.getName(), dto.getManifest());
        }

        List<DeviceTemplatePo> currentEntities = new ArrayList<>(deviceTemplateRepo.findByUserId(userId));
        currentEntities.sort(Comparator.comparing(
                template -> firstText(template != null ? template.getName() : null, ""),
                String.CASE_INSENSITIVE_ORDER));
        List<DeviceTemplateDto> currentTemplates = currentEntities.stream()
                .map(deviceTemplateMapper::toDto)
                .toList();
        Map<String, DeviceTemplatePo> currentByName = currentEntities.stream()
                .filter(Objects::nonNull)
                .filter(template -> hasText(template.getName()))
                .collect(Collectors.toMap(
                        template -> template.getName().trim().toLowerCase(Locale.ROOT),
                        template -> template,
                        (first, ignored) -> first,
                        LinkedHashMap::new));
        Set<String> defaultNames = defaultDefinitions.stream()
                .map(DeviceTemplatePo::getName)
                .filter(this::hasText)
                .map(name -> name.trim().toLowerCase(Locale.ROOT))
                .collect(Collectors.toCollection(LinkedHashSet::new));

        List<DefaultTemplateResetChangeDto> changes = new ArrayList<>();
        Map<String, Boolean> semanticsChangedByName = new HashMap<>();
        for (int index = 0; index < defaultDefinitions.size(); index++) {
            DeviceTemplatePo definition = defaultDefinitions.get(index);
            DeviceTemplateDto replacement = defaultDtos.get(index);
            String key = definition.getName().trim().toLowerCase(Locale.ROOT);
            DeviceTemplatePo existing = currentByName.get(key);
            DefaultTemplateResetChangeDto.ChangeType changeType;
            boolean semanticsChanged;
            if (existing == null) {
                changeType = DefaultTemplateResetChangeDto.ChangeType.RESTORE_MISSING;
                semanticsChanged = true;
            } else {
                DeviceTemplateDto current = deviceTemplateMapper.toDto(existing);
                semanticsChanged = !sameTemplateManifest(current, replacement);
                changeType = Boolean.TRUE.equals(existing.getDefaultTemplate())
                        ? DefaultTemplateResetChangeDto.ChangeType.REFRESH_DEFAULT
                        : DefaultTemplateResetChangeDto.ChangeType.REPLACE_CUSTOM_NAME_COLLISION;
            }
            changes.add(DefaultTemplateResetChangeDto.builder()
                    .templateName(definition.getName())
                    .changeType(changeType)
                    .semanticsChanged(semanticsChanged)
                    .build());
            semanticsChangedByName.put(key, semanticsChanged);
        }
        for (DeviceTemplatePo current : currentEntities) {
            if (current != null && Boolean.TRUE.equals(current.getDefaultTemplate())
                    && hasText(current.getName())
                    && !defaultNames.contains(current.getName().trim().toLowerCase(Locale.ROOT))) {
                String key = current.getName().trim().toLowerCase(Locale.ROOT);
                changes.add(DefaultTemplateResetChangeDto.builder()
                        .templateName(current.getName())
                        .changeType(DefaultTemplateResetChangeDto.ChangeType.REMOVE_OBSOLETE_DEFAULT)
                        .semanticsChanged(true)
                        .build());
                semanticsChangedByName.put(key, true);
            }
        }
        changes.sort(Comparator.comparing(DefaultTemplateResetChangeDto::getTemplateName,
                String.CASE_INSENSITIVE_ORDER));

        List<DeviceTemplateDto> prospectiveTemplates = new ArrayList<>();
        currentEntities.stream()
                .filter(Objects::nonNull)
                .filter(template -> !Boolean.TRUE.equals(template.getDefaultTemplate()))
                .filter(template -> hasText(template.getName()))
                .filter(template -> !defaultNames.contains(template.getName().trim().toLowerCase(Locale.ROOT)))
                .map(deviceTemplateMapper::toDto)
                .forEach(prospectiveTemplates::add);
        prospectiveTemplates.addAll(defaultDtos);
        Map<String, DeviceManifest> prospectiveManifests = templateManifestMap(prospectiveTemplates);

        List<DeviceNodeDto> nodes = getNodesInternal(userId).stream()
                .sorted(Comparator.comparing(node -> firstText(node != null ? node.getId() : null, "")))
                .toList();
        List<RuleDto> rules = getRulesInternal(userId);
        List<SpecificationDto> specs = getSpecsInternal(userId).stream()
                .sorted(Comparator.comparing(spec -> firstText(spec != null ? spec.getId() : null, "")))
                .toList();
        List<BoardEnvironmentVariableDto> previousEnvironment = getEnvironmentVariablesInternal(userId);
        List<BoardEnvironmentVariableDto> projectedEnvironment = projectEnvironmentVariablesForNodes(
                userId, nodes, prospectiveManifests, true);
        List<EnvironmentVariableChangeDto> environmentChanges =
                diffEnvironmentVariables(previousEnvironment, projectedEnvironment);

        List<DefaultTemplateAffectedDeviceDto> affectedDevices = nodes.stream()
                .filter(Objects::nonNull)
                .filter(node -> hasText(node.getTemplateName()))
                .filter(node -> Boolean.TRUE.equals(semanticsChangedByName.get(
                        node.getTemplateName().trim().toLowerCase(Locale.ROOT))))
                .map(node -> DefaultTemplateAffectedDeviceDto.builder()
                        .deviceId(node.getId())
                        .deviceLabel(hasText(node.getLabel()) ? node.getLabel() : node.getTemplateName())
                        .templateName(node.getTemplateName())
                        .build())
                .toList();

        Map<String, String> validationErrors = new LinkedHashMap<>();
        try {
            validateBoardReferences(userId, nodes, rules, specs, prospectiveManifests);
        } catch (ValidationException e) {
            validationErrors.putAll(e.getErrors());
        }
        List<DefaultTemplateResetBlockerDto> blockers = resetBlockers(
                validationErrors, nodes, rules, specs);
        String impactToken = defaultTemplateResetImpactToken(
                currentTemplates, defaultDtos, nodes, rules, specs, previousEnvironment,
                changes, environmentChanges, validationErrors);

        DefaultTemplateResetResultDto preview = DefaultTemplateResetResultDto.builder()
                .operation("preview")
                .impactToken(impactToken)
                .canApply(validationErrors.isEmpty())
                .templateChanges(List.copyOf(changes))
                .affectedDevices(affectedDevices)
                .blockers(blockers)
                .environmentChanges(environmentChanges)
                .currentTemplates(currentTemplates)
                .environmentVariables(previousEnvironment)
                .build();
        return new DefaultTemplateResetPlan(
                preview, List.copyOf(defaultDefinitions), projectedEnvironment,
                Map.copyOf(validationErrors));
    }

    private Map<String, DeviceManifest> templateManifestMap(List<DeviceTemplateDto> templates) {
        Map<String, DeviceManifest> manifests = new HashMap<>();
        for (DeviceTemplateDto template : templates == null ? List.<DeviceTemplateDto>of() : templates) {
            if (template == null || template.getManifest() == null || !hasText(template.getName())) {
                continue;
            }
            manifests.put(template.getName().trim().toLowerCase(Locale.ROOT), template.getManifest());
            if (hasText(template.getManifest().getName())) {
                manifests.put(template.getManifest().getName().trim().toLowerCase(Locale.ROOT),
                        template.getManifest());
            }
        }
        return manifests;
    }

    private List<DefaultTemplateResetBlockerDto> resetBlockers(
            Map<String, String> errors,
            List<DeviceNodeDto> nodes,
            List<RuleDto> rules,
            List<SpecificationDto> specs) {
        if (errors == null || errors.isEmpty()) {
            return List.of();
        }
        LinkedHashMap<String, DefaultTemplateResetBlockerDto> blockers = new LinkedHashMap<>();
        for (Map.Entry<String, String> entry : errors.entrySet()) {
            String label = resetBlockerLabel(entry.getKey(), nodes, rules, specs);
            String key = label + "\n" + entry.getValue();
            blockers.putIfAbsent(key, DefaultTemplateResetBlockerDto.builder()
                    .itemLabel(label)
                    .reasonCode(resetBlockerReasonCode(entry.getKey()))
                    .reason(entry.getValue())
                    .build());
        }
        return List.copyOf(blockers.values());
    }

    private String resetBlockerReasonCode(String field) {
        String normalized = field == null ? "" : field.trim().toLowerCase(Locale.ROOT);
        if (normalized.startsWith("nodes[")) return "DEVICE_INSTANCE_INCOMPATIBLE";
        if (normalized.startsWith("rules[")) return "AUTOMATION_RULE_INCOMPATIBLE";
        if (normalized.startsWith("specs[") || normalized.startsWith("specifications[")) {
            return "SPECIFICATION_INCOMPATIBLE";
        }
        if (normalized.startsWith("environmentvariables[") || normalized.startsWith("environment.")) {
            return "ENVIRONMENT_POOL_INCOMPATIBLE";
        }
        return "BOARD_MODEL_INCOMPATIBLE";
    }

    private String resetBlockerLabel(String field,
                                     List<DeviceNodeDto> nodes,
                                     List<RuleDto> rules,
                                     List<SpecificationDto> specs) {
        java.util.regex.Matcher matcher = java.util.regex.Pattern
                .compile("^(nodes|rules|specs)\\[(\\d+)]")
                .matcher(field == null ? "" : field);
        if (!matcher.find()) {
            return "Board model";
        }
        int index = Integer.parseInt(matcher.group(2));
        return switch (matcher.group(1)) {
            case "nodes" -> index < nodes.size() && nodes.get(index) != null
                    ? "Device: " + firstText(nodes.get(index).getLabel(), nodes.get(index).getTemplateName())
                    : "Device";
            case "rules" -> index < rules.size() && rules.get(index) != null
                    ? "Rule: " + firstText(rules.get(index).getRuleString(), "Rule " + (index + 1))
                    : "Rule " + (index + 1);
            case "specs" -> index < specs.size() && specs.get(index) != null
                    ? "Specification: " + firstText(specs.get(index).getTemplateLabel(), specs.get(index).getId())
                    : "Specification " + (index + 1);
            default -> "Board model";
        };
    }

    private String firstText(String preferred, String fallback) {
        return hasText(preferred) ? preferred.trim() : (hasText(fallback) ? fallback.trim() : "Unknown item");
    }

    private String defaultTemplateResetImpactToken(
            List<DeviceTemplateDto> currentTemplates,
            List<DeviceTemplateDto> defaultTemplates,
            List<DeviceNodeDto> nodes,
            List<RuleDto> rules,
            List<SpecificationDto> specs,
            List<BoardEnvironmentVariableDto> environment,
            List<DefaultTemplateResetChangeDto> changes,
            List<EnvironmentVariableChangeDto> environmentChanges,
            Map<String, String> validationErrors) {
        Map<String, Object> impact = new LinkedHashMap<>();
        impact.put("currentTemplates", currentTemplates);
        impact.put("defaultTemplates", defaultTemplates);
        impact.put("nodes", nodes);
        impact.put("rules", rules);
        impact.put("specifications", specs);
        impact.put("environmentVariables", environment);
        impact.put("templateChanges", changes);
        impact.put("environmentChanges", environmentChanges);
        impact.put("validationErrors", validationErrors);
        try {
            return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256")
                    .digest(JsonUtils.toJson(impact).getBytes(StandardCharsets.UTF_8)));
        } catch (NoSuchAlgorithmException e) {
            throw new InternalServerException("Unable to create default-template reset impact token", e);
        }
    }

    private record DefaultTemplateResetPlan(
            DefaultTemplateResetResultDto preview,
            List<DeviceTemplatePo> defaultDefinitions,
            List<BoardEnvironmentVariableDto> projectedEnvironment,
            Map<String, String> validationErrors) {
    }

    private static final java.util.regex.Pattern SAFE_SMV_TOKEN =
            java.util.regex.Pattern.compile("^[a-zA-Z_][a-zA-Z0-9_]*$");

    /** Template names must be printable ASCII (spaces allowed) so that
     *  Locale.ROOT toLowerCase and MySQL LOWER() produce identical results. */
    private static final java.util.regex.Pattern SAFE_TEMPLATE_NAME =
            java.util.regex.Pattern.compile("^[\\x20-\\x7E]+$");
    private static final int MAX_TEMPLATE_ICON_LENGTH = 262_144;
    private static final java.util.regex.Pattern SAFE_TEMPLATE_ICON =
            java.util.regex.Pattern.compile(
                    "^(data:image/(svg\\+xml|png|jpe?g|webp|gif)(;[^,]+)?,.+|https://\\S+)$",
                    java.util.regex.Pattern.CASE_INSENSITIVE);

    private void validateTemplateManifestForNuSmv(String templateName, DeviceManifest manifest) {
        validateTemplateIcon(templateName, manifest.getIcon());

        // ── Validate InternalVariable / ImpactedVariable names FIRST ──
        // These apply to ALL templates (including no-mode sensors), because the NuSMV
        // generation pipeline uses raw variable names (DeviceSmvDataFactory:83, :267).
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                validateSmvIdentifier(templateName, "InternalVariable", iv.getName());
                validateTemplateVariableDomain(templateName, "InternalVariable", iv.getName(),
                        iv.getValues(), iv.getLowerBound(), iv.getUpperBound(), iv.getNaturalChangeRate());
                if (!Boolean.TRUE.equals(iv.getIsInside())
                        && (!hasText(iv.getTrust()) || !hasText(iv.getPrivacy()))) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': shared environment InternalVariable '"
                                    + iv.getName() + "' must explicitly define Trust and Privacy.");
                }
            }
        }
        if (manifest.getEnvironmentDomains() != null) {
            for (DeviceManifest.EnvironmentDomain domain : manifest.getEnvironmentDomains()) {
                validateSmvIdentifier(templateName, "EnvironmentDomain", domain.getName());
                validateTemplateVariableDomain(templateName, "EnvironmentDomain", domain.getName(),
                        domain.getValues(), domain.getLowerBound(), domain.getUpperBound(),
                        domain.getNaturalChangeRate());
                if (!hasText(domain.getTrust()) || !hasText(domain.getPrivacy())) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': EnvironmentDomain '" + domain.getName()
                                    + "' must explicitly define Trust and Privacy.");
                }
            }
        }
        if (manifest.getImpactedVariables() != null) {
            for (String impacted : manifest.getImpactedVariables()) {
                validateSmvIdentifier(templateName, "ImpactedVariable", impacted);
            }
        }

        // ── Mode-related validation ──
        boolean hasModes = manifest.getModes() != null && !manifest.getModes().isEmpty();
        boolean hasInitState = manifest.getInitState() != null && !manifest.getInitState().isBlank();
        boolean hasWorkingStates = manifest.getWorkingStates() != null && !manifest.getWorkingStates().isEmpty();

        if (manifest.getApis() != null && !manifest.getApis().isEmpty()) {
            if (!hasModes) {
                throw new BadRequestException("Template '" + templateName
                        + "': APIs require at least one Mode because API commands are modeled as state changes.");
            }
            for (DeviceManifest.API api : manifest.getApis()) {
                if (api != null && api.getAssignments() != null && !api.getAssignments().isEmpty()) {
                    throw new BadRequestException("Template '" + templateName + "': API '" + api.getName()
                            + "' contains Assignments, but API variable assignments are not represented by the "
                            + "formal model. Use EndState or a triggered Transition instead.");
                }
            }
        }
        validateTemplateDynamics(templateName, manifest);

        if (!hasModes && !hasInitState && !hasWorkingStates) {
            // No-mode device template (pure sensor) — collision check among variables only
            checkVariableCollisions(templateName, manifest, Collections.emptyList());
            return;
        }

        // If any mode-related field is present, all three must be present
        if (!hasModes) {
            throw new BadRequestException("Template '" + templateName + "' must contain non-empty Modes.");
        }
        if (!hasInitState) {
            throw new BadRequestException("Template '" + templateName + "' must contain InitState.");
        }
        if (!hasWorkingStates) {
            throw new BadRequestException("Template '" + templateName + "' must contain non-empty WorkingStates.");
        }

        // Validate mode names are legal NuSMV identifiers (after stripping spaces)
        for (String mode : manifest.getModes()) {
            String cleaned = mode == null ? "" : mode.replace(" ", "");
            if (!SAFE_SMV_TOKEN.matcher(cleaned).matches()) {
                throw new BadRequestException(
                        "Template '" + templateName + "': mode name '" + mode
                                + "' contains invalid characters. Only letters, digits and underscores are allowed.");
            }
        }

        // Validate working-state names are legal NuSMV identifiers
        for (DeviceManifest.WorkingState ws : manifest.getWorkingStates()) {
            if (ws.getName() == null) continue;
            // Multi-mode states can be semicolon-separated; validate each segment
            String[] segments = ws.getName().split(";", -1);
            for (String seg : segments) {
                String cleaned = seg.trim().replace(" ", "");
                if (cleaned.isEmpty()) continue; // empty segment in ";cool" is allowed
                if (!SAFE_SMV_TOKEN.matcher(cleaned).matches()) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': state name '" + ws.getName()
                                    + "' contains invalid characters. Only letters, digits and underscores are allowed.");
                }
            }
        }

        // Check for identifier collisions (modes + variables)
        checkVariableCollisions(templateName, manifest, manifest.getModes());
    }

    private void validateTemplateVariableDomain(String templateName,
                                                String kind,
                                                String name,
                                                List<String> values,
                                                Integer lowerBound,
                                                Integer upperBound,
                                                String naturalChangeRate) {
        if (lowerBound != null && upperBound != null && lowerBound > upperBound) {
            throw new BadRequestException("Template '" + templateName + "': " + kind + " '"
                    + name + "' has LowerBound " + lowerBound + " greater than UpperBound " + upperBound + ".");
        }
        if (values != null) {
            Set<String> normalizedValues = new LinkedHashSet<>();
            for (String rawValue : values) {
                String value = rawValue == null ? "" : rawValue.replace(" ", "");
                if (value.isEmpty() || !normalizedValues.add(value)) {
                    throw new BadRequestException("Template '" + templateName + "': " + kind + " '"
                            + name + "' contains empty or duplicate enum values after model normalization.");
                }
            }
        }
        boolean numeric = lowerBound != null && upperBound != null;
        if (hasText(naturalChangeRate) && !numeric) {
            throw new BadRequestException("Template '" + templateName + "': " + kind + " '"
                    + name + "' declares NaturalChangeRate, but only numeric ranges can change by a rate.");
        }
        if (hasText(naturalChangeRate)) {
            String[] parts = naturalChangeRate.replace("[", "").replace("]", "").split(",", -1);
            try {
                int lowerRate;
                int upperRate;
                if (parts.length == 1) {
                    int rate = Integer.parseInt(parts[0].trim());
                    lowerRate = Math.min(0, rate);
                    upperRate = Math.max(0, rate);
                } else if (parts.length == 2) {
                    lowerRate = Integer.parseInt(parts[0].trim());
                    upperRate = Integer.parseInt(parts[1].trim());
                } else {
                    throw new NumberFormatException("wrong number of rate values");
                }
                if (lowerRate > upperRate) {
                    throw new BadRequestException("Template '" + templateName + "': " + kind + " '"
                            + name + "' has invalid or descending NaturalChangeRate '" + naturalChangeRate + "'.");
                }
            } catch (NumberFormatException exception) {
                throw new BadRequestException("Template '" + templateName + "': " + kind + " '"
                        + name + "' has invalid NaturalChangeRate '" + naturalChangeRate + "'.");
            }
        }
    }

    private void validateTemplateDynamics(String templateName, DeviceManifest manifest) {
        if (manifest.getWorkingStates() == null) {
            return;
        }
        Map<String, DeviceManifest.InternalVariable> writableDomains = new LinkedHashMap<>();
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                if (variable != null && Boolean.TRUE.equals(variable.getIsInside())) {
                    writableDomains.putIfAbsent(variable.getName(), variable);
                }
            }
        }
        if (manifest.getImpactedVariables() != null) {
            for (String impacted : manifest.getImpactedVariables()) {
                DeviceManifest.InternalVariable domain = EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted);
                if (domain != null) {
                    writableDomains.putIfAbsent(impacted, domain);
                }
            }
        }
        for (DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || state.getDynamics() == null) {
                continue;
            }
            Set<String> seen = new LinkedHashSet<>();
            for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                String variableName = dynamic == null ? null : dynamic.getVariableName();
                if (!hasText(variableName)) {
                    throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                            + state.getName() + "' Dynamics requires VariableName.");
                }
                if (!seen.add(variableName)) {
                    throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                            + state.getName() + "' defines Dynamics for '" + variableName + "' more than once.");
                }
                DeviceManifest.InternalVariable domain = writableDomains.get(variableName);
                if (domain == null) {
                    throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                            + state.getName() + "' has Dynamics for unknown or non-writable variable '"
                            + variableName + "'.");
                }
                boolean numeric = domain.getLowerBound() != null && domain.getUpperBound() != null;
                if (numeric) {
                    if (!hasText(dynamic.getChangeRate()) || dynamic.getValue() != null) {
                        throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                                + state.getName() + "' must use ChangeRate for numeric Dynamics target '"
                                + variableName + "'.");
                    }
                    try {
                        Integer.parseInt(dynamic.getChangeRate().trim());
                    } catch (NumberFormatException exception) {
                        throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                                + state.getName() + "' has non-integer ChangeRate '"
                                + dynamic.getChangeRate() + "' for '" + variableName + "'.");
                    }
                } else {
                    if (!hasText(dynamic.getValue()) || dynamic.getChangeRate() != null) {
                        throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                                + state.getName() + "' must use Value for enum/boolean Dynamics target '"
                                + variableName + "'.");
                    }
                    DeviceManifest.Assignment assignment = DeviceManifest.Assignment.builder()
                            .attribute(variableName).value(dynamic.getValue()).build();
                    validateTemplateDiscreteValue(templateName, state.getName(), assignment, domain);
                }
            }
        }
    }

    private void validateTemplateDiscreteValue(String templateName,
                                               String stateName,
                                               DeviceManifest.Assignment assignment,
                                               DeviceManifest.InternalVariable domain) {
        String value = assignment.getValue().replace(" ", "");
        if (domain.getValues() != null && !domain.getValues().isEmpty()) {
            boolean allowed = domain.getValues().stream()
                    .filter(Objects::nonNull)
                    .map(candidate -> candidate.replace(" ", ""))
                    .anyMatch(value::equals);
            if (!allowed) {
                throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                        + stateName + "' sets Dynamics target '" + assignment.getAttribute()
                        + "' outside enum domain " + domain.getValues() + ".");
            }
        } else if (!"TRUE".equalsIgnoreCase(value) && !"FALSE".equalsIgnoreCase(value)) {
            throw new BadRequestException("Template '" + templateName + "': WorkingState '"
                    + stateName + "' sets boolean Dynamics target '" + assignment.getAttribute()
                    + "' to '" + assignment.getValue() + "'; use TRUE or FALSE.");
        }
    }

    private void validateTemplateIcon(String templateName, String icon) {
        if (icon == null || icon.isBlank()) {
            return;
        }
        String trimmed = icon.trim();
        if (trimmed.length() > MAX_TEMPLATE_ICON_LENGTH) {
            throw new BadRequestException("Template '" + templateName
                    + "' Icon is too large. Use a data:image URI or HTTPS image under 256 KB.");
        }
        if (!SAFE_TEMPLATE_ICON.matcher(trimmed).matches()) {
            throw new BadRequestException("Template '" + templateName
                    + "' Icon must be a data:image URI (svg/png/jpeg/webp/gif) or an HTTPS URL.");
        }
    }

    /**
     * Check that mode names, internal variable names, environment domains, and impacted
     * variable names do not
     * collide after case-insensitive normalization. An ImpactedVariable may share a name
     * with an environment InternalVariable (IsInside=false/null), because that means the
     * device can read and affect the same shared environment value. It must not share a
     * name with a local InternalVariable (IsInside=true), which would make a device-private
     * state look like a board-level environment variable.
     */
    private void checkVariableCollisions(String templateName, DeviceManifest manifest, List<String> modes) {
        // Track modes separately - they must not collide with each other
        Set<String> modeNames = new HashSet<>();
        for (String mode : modes) {
            String cleaned = mode == null ? "" : mode.replace(" ", "");
            if (!cleaned.isEmpty() && !modeNames.add(cleaned.toLowerCase())) {
                throw new BadRequestException(
                        "Template '" + templateName + "': duplicate mode name after normalization: '" + mode + "'.");
            }
        }

        // Track internal variables - they must not collide with modes or each other
        Set<String> internalVarNames = new HashSet<>();
        Map<String, Boolean> localInternalVars = new HashMap<>();
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                String cleaned = iv.getName() == null ? "" : iv.getName().replace(" ", "");
                if (cleaned.isEmpty()) continue;

                String normalized = cleaned.toLowerCase();
                localInternalVars.put(normalized, Boolean.TRUE.equals(iv.getIsInside()));
                if (modeNames.contains(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': InternalVariable '" + iv.getName()
                            + "' collides with mode name.");
                }
                if (!internalVarNames.add(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': duplicate InternalVariable name after normalization: '"
                            + iv.getName() + "'.");
                }
            }
        }

        Set<String> environmentDomainNames = new HashSet<>();
        if (manifest.getEnvironmentDomains() != null) {
            for (DeviceManifest.EnvironmentDomain domain : manifest.getEnvironmentDomains()) {
                String cleaned = domain.getName() == null ? "" : domain.getName().replace(" ", "");
                if (cleaned.isEmpty()) continue;

                String normalized = cleaned.toLowerCase(Locale.ROOT);
                if (modeNames.contains(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': EnvironmentDomain '" + domain.getName()
                                    + "' collides with mode name.");
                }
                if (internalVarNames.contains(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': EnvironmentDomain '" + domain.getName()
                                    + "' duplicates an InternalVariable. Use EnvironmentDomains only for "
                                    + "impact-only values; a readable environment variable already supplies its domain.");
                }
                if (!environmentDomainNames.add(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': duplicate EnvironmentDomain name after normalization: '"
                                    + domain.getName() + "'.");
                }
            }
        }

        // Track impacted variables. They may share a name only with environment
        // InternalVariables, never with local InternalVariables.
        Set<String> impactedVarNames = new HashSet<>();
        if (manifest.getImpactedVariables() != null) {
            for (String impacted : manifest.getImpactedVariables()) {
                String cleaned = impacted == null ? "" : impacted.replace(" ", "");
                if (cleaned.isEmpty()) continue;

                String normalized = cleaned.toLowerCase();
                if (modeNames.contains(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': ImpactedVariable '" + impacted
                            + "' collides with mode name.");
                }
                if (!impactedVarNames.add(normalized)) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': duplicate ImpactedVariable name after normalization: '"
                            + impacted + "'.");
                }
                if (Boolean.TRUE.equals(localInternalVars.get(normalized))) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': ImpactedVariable '" + impacted
                            + "' cannot share a name with a local InternalVariable. "
                            + "Use WorkingStates.Dynamics for device-local state changes, and reserve "
                            + "ImpactedVariables for shared environment variables.");
                }
                if (EnvironmentDomainUtils.resolveImpactDomain(manifest, impacted) == null) {
                    throw new BadRequestException(
                            "Template '" + templateName + "': ImpactedVariable '" + impacted
                                    + "' has no domain in this manifest. Add EnvironmentDomains[].Name='" + impacted
                                    + "', or declare a readable InternalVariable with the same name and IsInside=false.");
                }
            }
        }

        for (String domainName : environmentDomainNames) {
            if (!impactedVarNames.contains(domainName)) {
                throw new BadRequestException(
                        "Template '" + templateName + "': EnvironmentDomain '" + domainName
                                + "' is unused. EnvironmentDomains may only describe names listed in ImpactedVariables.");
            }
        }

        checkGeneratedSmvIdentifierCollisions(templateName, manifest, modes);
    }

    /**
     * User-authored identifiers are literal, but the NuSMV backend derives extra
     * variables in the same module namespace. Reject only concrete generated-name
     * collisions; do not reserve broad prefixes such as trust_ or privacy_.
     */
    private void checkGeneratedSmvIdentifierCollisions(String templateName, DeviceManifest manifest, List<String> modes) {
        Map<String, String> identifiers = new LinkedHashMap<>();

        registerSmvIdentifier(templateName, identifiers, "is_attack", "generated attack flag");

        for (String mode : modes) {
            String cleaned = mode == null ? "" : mode.replace(" ", "");
            registerSmvIdentifier(templateName, identifiers, cleaned, "mode '" + mode + "'");
        }

        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                if (iv == null) {
                    continue;
                }
                String name = iv.getName() == null ? "" : iv.getName().replace(" ", "");
                registerSmvIdentifier(templateName, identifiers, name, "InternalVariable '" + iv.getName() + "'");
                registerSmvIdentifier(templateName, identifiers, "trust_" + name,
                        "generated trust for InternalVariable '" + iv.getName() + "'");
                registerSmvIdentifier(templateName, identifiers, "privacy_" + name,
                        "generated privacy for InternalVariable '" + iv.getName() + "'");
            }
        }

        Map<String, List<String>> modeStates = modeStates(manifest);
        for (String mode : modes) {
            List<String> states = modeStates.get(mode);
            if (states == null) {
                continue;
            }
            for (String state : states) {
                String suffix = mode + "_" + state;
                registerSmvIdentifier(templateName, identifiers, "trust_" + suffix,
                        "generated trust for state '" + suffix + "'");
                registerSmvIdentifier(templateName, identifiers, "privacy_" + suffix,
                        "generated privacy for state '" + suffix + "'");
            }
        }

        if (manifest.getImpactedVariables() != null) {
            for (String impacted : manifest.getImpactedVariables()) {
                if (isNumericTemplateVariable(manifest, impacted)) {
                    registerSmvIdentifier(templateName, identifiers, impacted + "_rate",
                            "generated rate for ImpactedVariable '" + impacted + "'");
                }
            }
        }

        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                if (api != null && Boolean.TRUE.equals(api.getSignal())) {
                    registerSmvIdentifier(templateName, identifiers,
                            DeviceSmvDataFactory.formatApiSignalName(api.getName()),
                            "generated signal for API '" + api.getName() + "'");
                }
            }
        }

        if (manifest.getContents() != null) {
            for (DeviceManifest.Content content : manifest.getContents()) {
                if (content != null && hasText(content.getName())) {
                    registerSmvIdentifier(templateName, identifiers, "privacy_" + content.getName(),
                            "generated privacy for Content '" + content.getName() + "'");
                }
            }
        }
    }

    private void registerSmvIdentifier(String templateName,
                                       Map<String, String> identifiers,
                                       String rawIdentifier,
                                       String source) {
        if (!hasText(rawIdentifier)) {
            return;
        }
        String identifier = rawIdentifier.trim();
        String normalized = identifier.toLowerCase(Locale.ROOT);
        String previous = identifiers.putIfAbsent(normalized, source);
        if (previous != null) {
            throw new BadRequestException("Template '" + templateName
                    + "': generated NuSMV identifier '" + identifier
                    + "' from " + source + " collides with " + previous
                    + ". Rename the user-authored item so generated internals do not share a namespace.");
        }
    }

    private boolean isNumericTemplateVariable(DeviceManifest manifest, String rawName) {
        if (!hasText(rawName) || manifest == null) {
            return false;
        }
        DeviceManifest.InternalVariable domain =
                EnvironmentDomainUtils.resolveImpactDomain(manifest, rawName.trim());
        return domain != null && domain.getLowerBound() != null && domain.getUpperBound() != null;
    }

    /**
     * Validate that a name is a legal NuSMV identifier: matches [a-zA-Z_][a-zA-Z0-9_]*
     * and is not a NuSMV reserved word (case-insensitive).
     * IMPORTANT: Does NOT strip spaces — validates the raw name to ensure it's used as-is in NuSMV generation.
     */
    private void validateSmvIdentifier(String templateName, String fieldType, String name) {
        if (name == null || name.isBlank()) {
            throw new BadRequestException(
                    "Template '" + templateName + "': " + fieldType + " name must not be blank.");
        }
        // Reject leading/trailing whitespace and common space character
        // (tab/newline will be caught by regex below as "invalid characters")
        if (name.trim().length() != name.length() || name.contains(" ")) {
            throw new BadRequestException(
                    "Template '" + templateName + "': " + fieldType + " name '" + name
                            + "' contains whitespace. Only letters, digits and underscores are allowed.");
        }
        // Validate against NuSMV identifier pattern
        if (!SAFE_SMV_TOKEN.matcher(name).matches()) {
            throw new BadRequestException(
                    "Template '" + templateName + "': " + fieldType + " name '" + name
                            + "' contains invalid characters. Only letters, digits and underscores are allowed, and must start with a letter or underscore.");
        }
        // Check against NuSMV reserved words (case-insensitive)
        if (DeviceSmvDataFactory.NUSMV_RESERVED_WORDS.contains(name)
                || DeviceSmvDataFactory.NUSMV_RESERVED_WORDS.contains(name.toUpperCase())
                || DeviceSmvDataFactory.NUSMV_RESERVED_WORDS.contains(name.toLowerCase())) {
            throw new BadRequestException(
                    "Template '" + templateName + "': " + fieldType + " name '" + name
                            + "' is a NuSMV reserved word and cannot be used as an identifier.");
        }
    }

    private void runTemplateNuSmvPrecheck(Long userId, String templateName, DeviceManifest manifest) {
        DeviceVerificationDto probe = new DeviceVerificationDto();
        probe.setVarName("__template_probe_device__");
        probe.setTemplateName(templateName);
        probe.setState(manifest.getInitState());

        SmvGenerator.GenerateResult generated = null;
        try {
            generated = smvGenerator.generate(
                    userId,
                    List.of(probe),
                    List.of(),
                    List.of(),
                    false,
                    0,
                    false,
                    SmvGenerator.GeneratePurpose.VERIFICATION
            );
        } catch (SmvGenerationException e) {
            if (SmvGenerationException.ErrorCategories.TEMPLATE_LOAD_ERROR.equals(e.getErrorCategory())
                    || SmvGenerationException.ErrorCategories.MANIFEST_PARSE_ERROR.equals(e.getErrorCategory())
                    || SmvGenerationException.ErrorCategories.TEMPLATE_NOT_FOUND.equals(e.getErrorCategory())
                    || SmvGenerationException.ErrorCategories.MULTIPLE_DEVICES_FAILED.equals(e.getErrorCategory())) {
                throw new InternalServerException(
                        "NuSMV precheck failed for template '" + templateName + "'.", e);
            }
            String reason = (e.getMessage() == null || e.getMessage().isBlank())
                    ? e.getErrorCategory()
                    : "[" + e.getErrorCategory() + "] " + e.getMessage();
            throw new BadRequestException("Template '" + templateName
                    + "' cannot be used in NuSMV flow: " + reason);
        } catch (Exception e) {
            throw new InternalServerException(
                    "NuSMV precheck failed for template '" + templateName + "'.", e);
        } finally {
            cleanupGeneratedSmvFile(generated);
        }
    }

    private void cleanupGeneratedSmvFile(SmvGenerator.GenerateResult generated) {
        if (generated == null || generated.smvFile() == null) {
            return;
        }
        Path smvPath = generated.smvFile().toPath();
        try {
            Files.deleteIfExists(smvPath);
            Path parent = smvPath.getParent();
            if (parent != null) {
                Files.deleteIfExists(parent);
            }
        } catch (Exception e) {
            log.debug("Failed to cleanup template precheck file: {}", smvPath, e);
        }
    }
}
