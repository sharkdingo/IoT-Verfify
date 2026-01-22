package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.*;
import cn.edu.nju.Iot_Verify.dto.manifest.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.po.*;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.SpecificationMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import java.util.*;
import java.util.stream.Collectors;

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

    @Override
    public List<DeviceNodeDto> getNodes(Long userId) {
        return nodeRepo.findByUserId(userId).stream()
                .map(DeviceNodeMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<DeviceNodeDto> saveNodes(Long userId, List<DeviceNodeDto> nodes) {
        nodeRepo.deleteByUserId(userId);
        List<DeviceNodePo> pos = nodes.stream()
                .map(dto -> DeviceNodeMapper.toPo(dto, userId))
                .toList();
        List<DeviceNodePo> saved = nodeRepo.saveAll(pos);
        return saved.stream().map(DeviceNodeMapper::toDto).toList();
    }

    @Override
    public List<DeviceEdgeDto> getEdges(Long userId) {
        return edgeRepo.findByUserId(userId).stream()
                .map(DeviceEdgeMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<DeviceEdgeDto> saveEdges(Long userId, List<DeviceEdgeDto> edges) {
        edgeRepo.deleteByUserId(userId);
        List<DeviceEdgePo> pos = edges.stream()
                .map(dto -> DeviceEdgeMapper.toPo(dto, userId))
                .toList();
        List<DeviceEdgePo> saved = edgeRepo.saveAll(pos);
        return saved.stream().map(DeviceEdgeMapper::toDto).toList();
    }

    @Override
    public List<SpecificationDto> getSpecs(Long userId) {
        return specRepo.findByUserId(userId).stream()
                .map(SpecificationMapper::toDto)
                .toList();
    }

    @Override
    @Transactional
    public List<SpecificationDto> saveSpecs(Long userId, List<SpecificationDto> specs) {
        specRepo.deleteByUserId(userId);
        List<SpecificationPo> pos = specs.stream()
                .map(dto -> SpecificationMapper.toPo(dto, userId))
                .toList();
        List<SpecificationPo> saved = specRepo.saveAll(pos);
        return saved.stream().map(SpecificationMapper::toDto).toList();
    }

    @Override
    public List<RuleDto> getRules(Long userId) {
        return ruleRepo.findByUserId(userId).stream().map(po -> {
            RuleDto dto = new RuleDto();
            dto.setId(po.getId());
            dto.setToId(po.getToId());
            dto.setToApi(po.getToApi());
            dto.setTemplateLabel(po.getTemplateLabel());
            List<SourceEntryDto> sources = JsonUtils.fromJsonOrDefault(
                    po.getSourcesJson(),
                    new TypeReference<List<SourceEntryDto>>() {},
                    List.of()
            );
            dto.setSources(sources);
            return dto;
        }).toList();
    }

    @Override
    @Transactional
    public List<RuleDto> saveRules(Long userId, List<RuleDto> rules) {
        // 增量更新：获取现有规则
        Map<String, RulePo> existingRules = ruleRepo.findByUserId(userId).stream()
                .collect(Collectors.toMap(RulePo::getId, r -> r));

        // 新规则 ID 集合
        Set<String> newRuleIds = new HashSet<>();

        // 处理每个规则
        for (RuleDto r : rules) {
            String ruleId = r.getId() == null ? UUID.randomUUID().toString() : r.getId();
            newRuleIds.add(ruleId);

            RulePo po = existingRules.get(ruleId);
            if (po == null) {
                // 新增
                po = RulePo.builder()
                        .id(ruleId)
                        .userId(userId)
                        .sourcesJson(JsonUtils.toJsonOrEmpty(r.getSources()))
                        .toId(r.getToId())
                        .toApi(r.getToApi())
                        .templateLabel(r.getTemplateLabel())
                        .build();
            } else {
                // 更新
                po.setSourcesJson(JsonUtils.toJsonOrEmpty(r.getSources()));
                po.setToId(r.getToId());
                po.setToApi(r.getToApi());
                po.setTemplateLabel(r.getTemplateLabel());
            }
            ruleRepo.save(po);
        }

        // 删除不再存在的规则
        for (String existingId : existingRules.keySet()) {
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
}
