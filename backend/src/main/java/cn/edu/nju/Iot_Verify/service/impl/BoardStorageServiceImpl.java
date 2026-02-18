package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.rule.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.*;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.mapper.RuleMapper;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

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
    private final SpecificationMapper specificationMapper;
    private final RuleMapper ruleMapper;
    private final DeviceNodeMapper deviceNodeMapper;
    private final DeviceEdgeMapper deviceEdgeMapper;

    @Override
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
        List<DeviceNodePo> saved = nodeRepo.saveAll(pos);
        return saved.stream().map(deviceNodeMapper::toDto).toList();
    }

    @Override
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
        List<DeviceEdgePo> saved = edgeRepo.saveAll(pos);
        return saved.stream().map(deviceEdgeMapper::toDto).toList();
    }

    @Override
    public List<SpecificationDto> getSpecs(Long userId) {
        return specRepo.findByUserId(userId).stream()
                .map(specificationMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<SpecificationDto> saveSpecs(Long userId, List<SpecificationDto> specs) {
        specRepo.deleteByUserId(userId);
        List<SpecificationPo> pos = specs.stream()
                .map(dto -> specificationMapper.toEntity(dto, userId))
                .toList();
        List<SpecificationPo> saved = specRepo.saveAll(pos);
        return saved.stream().map(specificationMapper::toDto).toList();
    }

    @Override
    public List<RuleDto> getRules(Long userId) {
        return ruleRepo.findByUserId(userId).stream()
                .map(ruleMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<RuleDto> saveRules(Long userId, List<RuleDto> rules) {
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
                ruleRepo.save(po);
            } else {
                po.setId(ruleId);
                ruleRepo.save(po);
            }
        }

        // 删除不再存在的规则
        for (Long existingId : existingRules.keySet()) {
            if (!newRuleIds.contains(existingId)) {
                ruleRepo.deleteById(existingId);
            }
        }

        return getRules(userId);
    }

    @Override
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
            return layoutRepo.save(created);
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
        layoutRepo.save(po);

        return getLayout(userId);
    }

    @Override
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
        activeRepo.save(po);

        return getActive(userId);
    }

    @Override
    public List<DeviceTemplateDto> getDeviceTemplates(Long userId) {
        List<DeviceTemplatePo> poList = deviceTemplateRepo.findByUserId(userId);

        return poList.stream().map(po -> {
            DeviceTemplateDto dto = new DeviceTemplateDto();
            dto.setId(po.getId().toString());
            dto.setName(po.getName());

            if (po.getManifestJson() != null && !po.getManifestJson().isEmpty()) {
                DeviceManifest manifest = JsonUtils.fromJsonOrDefault(
                        po.getManifestJson(),
                        new TypeReference<DeviceManifest>() {},
                        new DeviceManifest()
                );
                dto.setManifest(manifest);
            }
            return dto;
        }).toList();
    }

    @Override
    @Transactional
    public DeviceTemplateDto addDeviceTemplate(Long userId, DeviceTemplateDto dto) {
        if (deviceTemplateRepo.existsByUserIdAndName(userId, dto.getName())) {
            throw ConflictException.duplicateTemplate(dto.getName());
        }

        String json = JsonUtils.toJson(dto.getManifest());

        DeviceTemplatePo po = DeviceTemplatePo.builder()
                .userId(userId)
                .name(dto.getName())
                .manifestJson(json)
                .build();

        DeviceTemplatePo saved = deviceTemplateRepo.save(po);

        DeviceTemplateDto result = new DeviceTemplateDto();
        result.setId(saved.getId().toString());
        result.setName(saved.getName());
        result.setManifest(dto.getManifest());
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
}
