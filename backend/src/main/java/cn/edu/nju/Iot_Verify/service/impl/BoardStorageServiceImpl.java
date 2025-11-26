// src/main/java/cn/edu/nju/Iot_Verify/service/impl/BoardStorageServiceImpl.java
package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.*;
import cn.edu.nju.Iot_Verify.po.*;
import cn.edu.nju.Iot_Verify.repository.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.DeviceEdgeMapper;
import cn.edu.nju.Iot_Verify.util.DeviceNodeMapper;
import cn.edu.nju.Iot_Verify.util.SpecificationMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Service;

import java.util.Collections;
import java.util.List;

@Service
@RequiredArgsConstructor
public class BoardStorageServiceImpl implements BoardStorageService {

    private final DeviceNodeRepository nodeRepo;
    private final DeviceEdgeRepository edgeRepo;
    private final SpecificationRepository specRepo;
    private final BoardLayoutRepository layoutRepo;
    private final BoardActiveRepository activeRepo;

    private static final ObjectMapper MAPPER = new ObjectMapper();

    /* ===================== NODES ===================== */

    @Override
    public List<DeviceNodeDto> getNodes() {
        return nodeRepo.findAll().stream()
                .map(DeviceNodeMapper::toDto)
                .toList();
    }

    @Override
    public void saveNodes(List<DeviceNodeDto> nodes) {
        nodeRepo.deleteAll();
        List<DeviceNodePo> pos = nodes.stream()
                .map(DeviceNodeMapper::toPo)
                .toList();
        nodeRepo.saveAll(pos);
    }

    /* ===================== EDGES ===================== */

    @Override
    public List<DeviceEdgeDto> getEdges() {
        return edgeRepo.findAll().stream()
                .map(DeviceEdgeMapper::toDto)
                .toList();
    }

    @Override
    public void saveEdges(List<DeviceEdgeDto> edges) {
        edgeRepo.deleteAll();
        List<DeviceEdgePo> pos = edges.stream()
                .map(DeviceEdgeMapper::toPo)
                .toList();
        edgeRepo.saveAll(pos);
    }

    /* ===================== SPECS ===================== */

    @Override
    public List<SpecificationDto> getSpecs() {
        return specRepo.findAll().stream()
                .map(SpecificationMapper::toDto)
                .toList();
    }

    @Override
    public void saveSpecs(List<SpecificationDto> specs) {
        specRepo.deleteAll();
        List<SpecificationPo> pos = specs.stream()
                .map(SpecificationMapper::toPo)
                .toList();
        specRepo.saveAll(pos);
    }

    /* ===================== LAYOUT ===================== */

    @Override
    public BoardLayoutDto getLayout() {
        BoardLayoutPo po = layoutRepo.findById((byte) 1).orElseGet(() -> {
            BoardLayoutPo created = BoardLayoutPo.builder()
                    .id((byte) 1)
                    .inputX(24.0)
                    .inputY(24.0)
                    .statusX(1040.0)
                    .statusY(80.0)
                    .canvasPanX(0.0)
                    .canvasPanY(0.0)
                    .canvasZoom(1.0)
                    .build();
            return layoutRepo.save(created);
        });

        BoardLayoutDto dto = new BoardLayoutDto();

        BoardLayoutDto.PanelPosition input = new BoardLayoutDto.PanelPosition();
        input.setX(po.getInputX());
        input.setY(po.getInputY());
        dto.setInput(input);

        BoardLayoutDto.PanelPosition status = new BoardLayoutDto.PanelPosition();
        status.setX(po.getStatusX());
        status.setY(po.getStatusY());
        dto.setStatus(status);

        BoardLayoutDto.CanvasPan pan = new BoardLayoutDto.CanvasPan();
        pan.setX(po.getCanvasPanX());
        pan.setY(po.getCanvasPanY());
        dto.setCanvasPan(pan);

        dto.setCanvasZoom(po.getCanvasZoom());

        return dto;
    }


    @Override
    public void saveLayout(BoardLayoutDto layout) {
        BoardLayoutPo po = BoardLayoutPo.builder()
                .id((byte) 1)
                .inputX(layout.getInput() != null ? layout.getInput().getX() : 24.0)
                .inputY(layout.getInput() != null ? layout.getInput().getY() : 24.0)
                .statusX(layout.getStatus() != null ? layout.getStatus().getX() : 1040.0)
                .statusY(layout.getStatus() != null ? layout.getStatus().getY() : 80.0)
                .canvasPanX(layout.getCanvasPan() != null ? layout.getCanvasPan().getX() : 0.0)
                .canvasPanY(layout.getCanvasPan() != null ? layout.getCanvasPan().getY() : 0.0)
                .canvasZoom(layout.getCanvasZoom() != null ? layout.getCanvasZoom() : 1.0)
                .build();
        layoutRepo.save(po);
    }

    /* ===================== ACTIVE ===================== */

    @Override
    public BoardActiveDto getActive() {
        BoardActivePo po = activeRepo.findById((byte) 1).orElse(null);
        BoardActiveDto dto = new BoardActiveDto();

        if (po == null) {
            // 第一次使用给个默认展开
            dto.setInput(List.of("devices", "rules", "specs"));
            dto.setStatus(List.of("devices", "edges", "specs"));
            return dto;
        }

        dto.setInput(readStringList(po.getInputTabsJson()));
        dto.setStatus(readStringList(po.getStatusTabsJson()));
        return dto;
    }

    @Override
    public void saveActive(BoardActiveDto active) {
        BoardActivePo po = BoardActivePo.builder()
                .id((byte) 1)
                .inputTabsJson(writeStringList(active.getInput()))
                .statusTabsJson(writeStringList(active.getStatus()))
                .build();
        activeRepo.save(po);
    }

    /* ===================== JSON 小工具 ===================== */

    private List<String> readStringList(String json) {
        if (json == null || json.isBlank()) return Collections.emptyList();
        try {
            return MAPPER.readValue(json, new TypeReference<List<String>>() {});
        } catch (Exception e) {
            return Collections.emptyList();
        }
    }

    private String writeStringList(List<String> list) {
        try {
            return MAPPER.writeValueAsString(list == null ? List.of() : list);
        } catch (Exception e) {
            return "[]";
        }
    }
}
