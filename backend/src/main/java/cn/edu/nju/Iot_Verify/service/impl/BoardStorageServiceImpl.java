package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.*;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

@Slf4j
@Service
@RequiredArgsConstructor
public class BoardStorageServiceImpl implements BoardStorageService {

    private final DeviceNodeRepository nodeRepo;
    private final DeviceEdgeRepository edgeRepo;
    private final SpecificationRepository specRepo;
    private final RuleRepository ruleRepo;
    private final BoardLayoutRepository layoutRepo;
    private final BoardActiveRepository activeRepo;
    private final DeviceTemplateRepository deviceTemplateRepo;
    private final DeviceTemplateService deviceTemplateService;
    private final SmvGenerator smvGenerator;
    private final SpecificationMapper specificationMapper;
    private final RuleMapper ruleMapper;
    private final DeviceNodeMapper deviceNodeMapper;
    private final DeviceEdgeMapper deviceEdgeMapper;

    /**
     * User-level write locks for saveRules/saveSpecs to prevent cross-session
     * read-modify-write races (e.g. two AI tool calls for the same user).
     * Note: only effective for single-instance deployments. Multi-instance requires
     * DB-level optimistic locking or atomic SQL.
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

    @Override
    @Transactional(readOnly = true)
    public List<DeviceNodeDto> getNodes(Long userId) {
        return nodeRepo.findByUserId(userId).stream()
                .map(deviceNodeMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<DeviceNodeDto> saveNodes(Long userId, List<DeviceNodeDto> nodes) {
        nodeRepo.deleteByUserId(userId);
        List<DeviceNodePo> pos = nodes.stream()
                .map(dto -> deviceNodeMapper.toEntity(dto, userId))
                .toList();
        List<DeviceNodePo> saved = nodeRepo.saveAll(Objects.requireNonNull(pos, "nodes to save must not be null"));
        return saved.stream().map(deviceNodeMapper::toDto).toList();
    }

    @Override
    @Transactional(readOnly = true)
    public List<DeviceEdgeDto> getEdges(Long userId) {
        return edgeRepo.findByUserId(userId).stream()
                .map(deviceEdgeMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<DeviceEdgeDto> saveEdges(Long userId, List<DeviceEdgeDto> edges) {
        edgeRepo.deleteByUserId(userId);
        List<DeviceEdgePo> pos = edges.stream()
                .map(dto -> deviceEdgeMapper.toEntity(dto, userId))
                .toList();
        List<DeviceEdgePo> saved = edgeRepo.saveAll(Objects.requireNonNull(pos, "edges to save must not be null"));
        return saved.stream().map(deviceEdgeMapper::toDto).toList();
    }

    @Override
    @Transactional(readOnly = true)
    public List<SpecificationDto> getSpecs(Long userId) {
        return specRepo.findByUserId(userId).stream()
                .map(specificationMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<SpecificationDto> saveSpecs(Long userId, List<SpecificationDto> specs) {
        synchronized (getUserWriteLock(userId)) {
            return saveSpecsInternal(userId, specs);
        }
    }

    @Override
    @Transactional
    public List<SpecificationDto> addSpec(Long userId, SpecificationDto spec) {
        synchronized (getUserWriteLock(userId)) {
            List<SpecificationDto> existing = new ArrayList<>(getSpecs(userId));
            existing.add(spec);
            return saveSpecsInternal(userId, existing);
        }
    }

    @Override
    @Transactional
    public List<SpecificationDto> removeSpec(Long userId, String specId) {
        synchronized (getUserWriteLock(userId)) {
            List<SpecificationDto> existing = new ArrayList<>(getSpecs(userId));
            boolean removed = existing.removeIf(s -> specId.equals(s.getId()));
            if (!removed) {
                return null;
            }
            saveSpecsInternal(userId, existing);
            return existing;
        }
    }

    /** Internal save without re-acquiring the lock. */
    private List<SpecificationDto> saveSpecsInternal(Long userId, List<SpecificationDto> specs) {
        specRepo.deleteByUserId(userId);
        List<SpecificationPo> pos = specs.stream()
                .map(dto -> specificationMapper.toEntity(dto, userId))
                .toList();
        List<SpecificationPo> saved = specRepo.saveAll(Objects.requireNonNull(pos, "specs to save must not be null"));
        return saved.stream().map(specificationMapper::toDto).toList();
    }

    @Override
    @Transactional(readOnly = true)
    public List<RuleDto> getRules(Long userId) {
        return ruleRepo.findByUserId(userId).stream()
                .map(ruleMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<RuleDto> saveRules(Long userId, List<RuleDto> rules) {
        synchronized (getUserWriteLock(userId)) {
            // 增量更新：获取现有规则
            Map<Long, RulePo> existingRules = ruleRepo.findByUserId(userId).stream()
                    .collect(Collectors.toMap(RulePo::getId, r -> r));

            // 新规则 ID 集合
            Set<Long> newRuleIds = new HashSet<>();

            // 处理每个规则
            for (RuleDto r : rules) {
                Long ruleId = r.getId();
                if (ruleId != null) {
                    newRuleIds.add(ruleId);
                }

                RulePo po = ruleMapper.toEntity(r, userId);
                if (ruleId == null) {
                    // 新规则，直接插入
                    ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
                } else if (existingRules.containsKey(ruleId)) {
                    // 已有规则且属于当前用户，更新
                    po.setId(ruleId);
                    ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
                } else {
                    // ruleId 不属于当前用户，忽略该 ID 作为新规则插入
                    log.warn("Rule id {} does not belong to user {}, inserting as new rule", ruleId, userId);
                    po.setId(null);
                    ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
                }
            }

            // 删除不再存在的规则
            for (Long existingId : existingRules.keySet()) {
                if (!newRuleIds.contains(existingId)) {
                    ruleRepo.deleteById(Objects.requireNonNull(existingId, "rule id to delete must not be null"));
                }
            }

            return getRules(userId);
        }
    }

    @Override
    @Transactional
    public List<RuleDto> addRule(Long userId, RuleDto rule) {
        synchronized (getUserWriteLock(userId)) {
            rule.setId(null); // new rule, let DB assign ID
            RulePo po = ruleMapper.toEntity(rule, userId);
            ruleRepo.save(Objects.requireNonNull(po, "rule to save must not be null"));
            return getRules(userId);
        }
    }

    @Override
    @Transactional
    public List<RuleDto> removeRule(Long userId, long ruleId) {
        synchronized (getUserWriteLock(userId)) {
            List<RulePo> existing = ruleRepo.findByUserId(userId);
            boolean found = existing.stream().anyMatch(r -> r.getId() != null && r.getId() == ruleId);
            if (!found) {
                return null;
            }
            ruleRepo.deleteById(ruleId);
            return existing.stream()
                    .filter(r -> r.getId() == null || r.getId() != ruleId)
                    .map(ruleMapper::toDto)
                    .toList();
        }
    }

    @Override
    @Transactional
    public BoardLayoutDto getLayout(Long userId) {
        BoardLayoutPo po = layoutRepo.findByUserId(userId).orElseGet(() -> {
            BoardLayoutPo created = BoardLayoutPo.builder()
                    .userId(userId)
                    .inputX(24.0).inputY(24.0)
                    .statusX(1040.0).statusY(80.0)
                    .canvasPanX(0.0).canvasPanY(0.0).canvasZoom(1.0)
                    .inputIsDocked(false).inputDockSide(null)
                    .inputLastPosX(24.0).inputLastPosY(24.0)
                    .statusIsDocked(false).statusDockSide(null)
                    .statusLastPosX(1040.0).statusLastPosY(80.0)
                    .build();
            return layoutRepo.save(Objects.requireNonNull(created, "layout to save must not be null"));
        });

        return mapLayoutPoToDto(po);
    }

    private BoardLayoutDto mapLayoutPoToDto(BoardLayoutPo po) {
        BoardLayoutDto dto = new BoardLayoutDto();

        BoardLayoutDto.PanelPosition inputPos = new BoardLayoutDto.PanelPosition();
        inputPos.setX(po.getInputX());
        inputPos.setY(po.getInputY());
        dto.setInput(inputPos);

        BoardLayoutDto.PanelPosition statusPos = new BoardLayoutDto.PanelPosition();
        statusPos.setX(po.getStatusX());
        statusPos.setY(po.getStatusY());
        dto.setStatus(statusPos);

        BoardLayoutDto.DockStateWrapper dockWrapper = new BoardLayoutDto.DockStateWrapper();

        BoardLayoutDto.DockState inputDock = new BoardLayoutDto.DockState();
        inputDock.setIsDocked(po.getInputIsDocked() != null ? po.getInputIsDocked() : false);
        inputDock.setSide(po.getInputDockSide());

        BoardLayoutDto.PanelPosition inputLastPos = new BoardLayoutDto.PanelPosition();
        inputLastPos.setX(po.getInputLastPosX() != null ? po.getInputLastPosX() : 24.0);
        inputLastPos.setY(po.getInputLastPosY() != null ? po.getInputLastPosY() : 24.0);
        inputDock.setLastPos(inputLastPos);

        dockWrapper.setInput(inputDock);

        BoardLayoutDto.DockState statusDock = new BoardLayoutDto.DockState();
        statusDock.setIsDocked(po.getStatusIsDocked() != null ? po.getStatusIsDocked() : false);
        statusDock.setSide(po.getStatusDockSide());

        BoardLayoutDto.PanelPosition statusLastPos = new BoardLayoutDto.PanelPosition();
        statusLastPos.setX(po.getStatusLastPosX() != null ? po.getStatusLastPosX() : 1040.0);
        statusLastPos.setY(po.getStatusLastPosY() != null ? po.getStatusLastPosY() : 80.0);
        statusDock.setLastPos(statusLastPos);

        dockWrapper.setStatus(statusDock);

        dto.setDockState(dockWrapper);

        BoardLayoutDto.CanvasPan pan = new BoardLayoutDto.CanvasPan();
        pan.setX(po.getCanvasPanX());
        pan.setY(po.getCanvasPanY());
        dto.setCanvasPan(pan);

        dto.setCanvasZoom(po.getCanvasZoom());

        return dto;
    }

    @Transactional
    @Override
    public BoardLayoutDto saveLayout(Long userId, BoardLayoutDto layout) {
        boolean inDocked = false;
        String inSide = null;
        double inLastX = 24.0;
        double inLastY = 24.0;

        if (layout.getDockState() != null && layout.getDockState().getInput() != null) {
            BoardLayoutDto.DockState ds = layout.getDockState().getInput();
            inDocked = Boolean.TRUE.equals(ds.getIsDocked());
            inSide = ds.getSide();
            if (ds.getLastPos() != null) {
                inLastX = ds.getLastPos().getX() != null ? ds.getLastPos().getX() : 24.0;
                inLastY = ds.getLastPos().getY() != null ? ds.getLastPos().getY() : 24.0;
            }
        }

        boolean stDocked = false;
        String stSide = null;
        double stLastX = 1040.0;
        double stLastY = 80.0;

        if (layout.getDockState() != null && layout.getDockState().getStatus() != null) {
            BoardLayoutDto.DockState ds = layout.getDockState().getStatus();
            stDocked = Boolean.TRUE.equals(ds.getIsDocked());
            stSide = ds.getSide();
            if (ds.getLastPos() != null) {
                stLastX = ds.getLastPos().getX() != null ? ds.getLastPos().getX() : 1040.0;
                stLastY = ds.getLastPos().getY() != null ? ds.getLastPos().getY() : 80.0;
            }
        }

        BoardLayoutPo existing = layoutRepo.findByUserId(userId).orElse(null);
        Long id = existing != null ? existing.getId() : null;

        BoardLayoutPo po = BoardLayoutPo.builder()
                .id(id)
                .userId(userId)
                .inputX(layout.getInput() != null ? layout.getInput().getX() : 24.0)
                .inputY(layout.getInput() != null ? layout.getInput().getY() : 24.0)
                .statusX(layout.getStatus() != null ? layout.getStatus().getX() : 1040.0)
                .statusY(layout.getStatus() != null ? layout.getStatus().getY() : 80.0)
                .canvasPanX(layout.getCanvasPan() != null ? layout.getCanvasPan().getX() : 0.0)
                .canvasPanY(layout.getCanvasPan() != null ? layout.getCanvasPan().getY() : 0.0)
                .canvasZoom(layout.getCanvasZoom() != null ? layout.getCanvasZoom() : 1.0)
                .inputIsDocked(inDocked)
                .inputDockSide(inSide)
                .inputLastPosX(inLastX)
                .inputLastPosY(inLastY)
                .statusIsDocked(stDocked)
                .statusDockSide(stSide)
                .statusLastPosX(stLastX)
                .statusLastPosY(stLastY)
                .build();
        layoutRepo.save(Objects.requireNonNull(po, "layout to save must not be null"));

        return getLayout(userId);
    }

    @Override
    @Transactional(readOnly = true)
    public BoardActiveDto getActive(Long userId) {
        BoardActivePo po = activeRepo.findByUserId(userId).orElse(null);
        BoardActiveDto dto = new BoardActiveDto();

        if (po == null) {
            dto.setInput(List.of("devices", "rules", "specs"));
            dto.setStatus(List.of("devices", "edges", "specs"));
            return dto;
        }

        dto.setInput(JsonUtils.fromJsonToStringList(po.getInputTabsJson()));
        dto.setStatus(JsonUtils.fromJsonToStringList(po.getStatusTabsJson()));
        return dto;
    }

    @Transactional
    @Override
    public BoardActiveDto saveActive(Long userId, BoardActiveDto active) {
        BoardActivePo existing = activeRepo.findByUserId(userId).orElse(null);
        Long id = existing != null ? existing.getId() : null;

        BoardActivePo po = BoardActivePo.builder()
                .id(id)
                .userId(userId)
                .inputTabsJson(JsonUtils.toJsonOrEmpty(active.getInput()))
                .statusTabsJson(JsonUtils.toJsonOrEmpty(active.getStatus()))
                .build();
        activeRepo.save(Objects.requireNonNull(po, "active tabs to save must not be null"));

        return getActive(userId);
    }

    @Override
    @Transactional(readOnly = true)
    public List<DeviceTemplateDto> getDeviceTemplates(Long userId) {
        List<DeviceTemplatePo> poList = deviceTemplateRepo.findByUserId(userId);

        return poList.stream().map(po -> {
            DeviceTemplateDto dto = new DeviceTemplateDto();
            dto.setId(po.getId().toString());
            dto.setName(po.getName());

            DeviceManifest manifest = JsonUtils.fromJsonOrDefault(
                    po.getManifestJson(),
                    new TypeReference<DeviceManifest>() {},
                    new DeviceManifest()
            );
            // Keep DTO-level name as the single source used by business logic.
            manifest.setName(dto.getName());
            dto.setManifest(manifest);
            return dto;
        }).toList();
    }

    @Override
    @Transactional
    public DeviceTemplateDto addDeviceTemplate(Long userId, DeviceTemplateDto dto) {
        DeviceTemplateDto safeDto = Objects.requireNonNull(dto, "template dto must not be null");
        if (safeDto.getManifest() == null) {
            throw new BadRequestException("Template manifest is required");
        }

        String rawName = safeDto.getName() != null ? safeDto.getName().trim() : null;
        if (rawName == null || rawName.isBlank()) {
            throw new BadRequestException("Template name is required");
        }

        final String canonicalName = rawName;
        safeDto.setName(canonicalName);
        safeDto.getManifest().setName(canonicalName);
        validateTemplateManifestForNuSmv(canonicalName, safeDto.getManifest());

        boolean duplicated = deviceTemplateRepo.existsByUserIdAndNameIgnoreCase(userId, canonicalName);
        if (duplicated) {
            throw ConflictException.duplicateTemplate(canonicalName);
        }

        String json = JsonUtils.toJson(safeDto.getManifest());

        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .userId(userId)
                .name(canonicalName)
                .manifestJson(json)
                .build();

        DeviceTemplatePo saved;
        try {
            saved = deviceTemplateRepo.saveAndFlush(Objects.requireNonNull(po, "template to save must not be null"));
        } catch (DataIntegrityViolationException e) {
            throw ConflictException.duplicateTemplate(canonicalName);
        }
        runTemplateNuSmvPrecheck(userId, canonicalName, safeDto.getManifest());

        DeviceTemplateDto result = new DeviceTemplateDto();
        result.setId(saved.getId().toString());
        result.setName(canonicalName);
        result.setManifest(safeDto.getManifest());
        return result;
    }

    @Override
    @Transactional
    public void deleteDeviceTemplate(Long userId, String templateId) {
        Long id;
        try {
            id = Long.parseLong(templateId.trim());
        } catch (NumberFormatException e) {
            throw new BadRequestException("Invalid template ID format: " + templateId);
        }

        DeviceTemplatePo po = deviceTemplateRepo.findById(id)
                .orElseThrow(() -> new ResourceNotFoundException("Template", id));

        if (!po.getUserId().equals(userId)) {
            throw new ForbiddenException("Access denied to this template");
        }

        deviceTemplateRepo.delete(po);
    }

    @Transactional
    @Override
    public int reloadDeviceTemplates(Long userId) {
        // 删除用户现有的所有模板
        List<DeviceTemplatePo> existingTemplates = deviceTemplateRepo.findByUserId(userId);
        if (!existingTemplates.isEmpty()) {
            deviceTemplateRepo.deleteAll(existingTemplates);
            log.info("Deleted {} existing templates for user {}", existingTemplates.size(), userId);
        }

        // 重新初始化默认模板
        return deviceTemplateService.initDefaultTemplates(userId);
    }

    private static final java.util.regex.Pattern SAFE_SMV_TOKEN =
            java.util.regex.Pattern.compile("^[a-zA-Z_][a-zA-Z0-9_]*$");

    private void validateTemplateManifestForNuSmv(String templateName, DeviceManifest manifest) {
        // ── Validate InternalVariable / ImpactedVariable names FIRST ──
        // These apply to ALL templates (including no-mode sensors), because the NuSMV
        // generation pipeline uses raw variable names (DeviceSmvDataFactory:83, :267).
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                validateSmvIdentifier(templateName, "InternalVariable", iv.getName());
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

    /**
     * Check that mode names, internal variable names, and impacted variable names
     * do not collide after case-insensitive normalization.
     *
     * IMPORTANT: InternalVariable and ImpactedVariable are allowed to have the same name,
     * as this represents a common pattern where a device's internal variable affects
     * an environment variable of the same name (e.g., thermostat.temperature -> temperature).
     * This aligns with default templates like Thermostat, Water Heater, Window, and Garage Door.
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
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                String cleaned = iv.getName() == null ? "" : iv.getName().replace(" ", "");
                if (cleaned.isEmpty()) continue;

                String normalized = cleaned.toLowerCase();
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

        // Track impacted variables - they must not collide with modes or each other
        // BUT they CAN collide with internal variables (common pattern: device internal var affects env var)
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
            }
        }
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
