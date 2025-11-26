// src/main/java/cn/edu/nju/Iot_Verify/controller/BoardStorageController.java
package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.*;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import lombok.RequiredArgsConstructor;
import org.springframework.web.bind.annotation.*;

import java.util.List;

@RestController
@RequestMapping("/api/board")
@RequiredArgsConstructor
@CrossOrigin // 前后端端口不一样时允许跨域
public class BoardStorageController {

    private final BoardStorageService boardService;

    @GetMapping("/nodes")
    public List<DeviceNodeDto> getNodes() {
        return boardService.getNodes();
    }

    @PostMapping("/nodes")
    public void saveNodes(@RequestBody List<DeviceNodeDto> nodes) {
        boardService.saveNodes(nodes);
    }

    @GetMapping("/edges")
    public List<DeviceEdgeDto> getEdges() {
        return boardService.getEdges();
    }

    @PostMapping("/edges")
    public void saveEdges(@RequestBody List<DeviceEdgeDto> edges) {
        boardService.saveEdges(edges);
    }

    @GetMapping("/specs")
    public List<SpecificationDto> getSpecs() {
        return boardService.getSpecs();
    }

    @PostMapping("/specs")
    public void saveSpecs(@RequestBody List<SpecificationDto> specs) {
        boardService.saveSpecs(specs);
    }

    @GetMapping("/layout")
    public BoardLayoutDto getLayout() {
        return boardService.getLayout();
    }

    @PostMapping("/layout")
    public void saveLayout(@RequestBody BoardLayoutDto layout) {
        boardService.saveLayout(layout);
    }

    @GetMapping("/active")
    public BoardActiveDto getActive() {
        return boardService.getActive();
    }

    @PostMapping("/active")
    public void saveActive(@RequestBody BoardActiveDto active) {
        boardService.saveActive(active);
    }
}
