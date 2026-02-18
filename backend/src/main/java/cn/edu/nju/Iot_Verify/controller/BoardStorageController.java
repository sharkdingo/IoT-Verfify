package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.web.bind.annotation.*;

import java.util.List;

@RestController
@RequestMapping("/api/board")
@RequiredArgsConstructor
public class BoardStorageController {

    private final BoardStorageService boardService;

    @GetMapping("/nodes")
    public Result<List<DeviceNodeDto>> getNodes(@CurrentUser Long userId) {
        return Result.success(boardService.getNodes(userId));
    }

    @PostMapping("/nodes")
    public Result<List<DeviceNodeDto>> saveNodes(@CurrentUser Long userId, @Valid @RequestBody List<DeviceNodeDto> nodes) {
        return Result.success(boardService.saveNodes(userId, nodes));
    }

    @GetMapping("/edges")
    public Result<List<DeviceEdgeDto>> getEdges(@CurrentUser Long userId) {
        return Result.success(boardService.getEdges(userId));
    }

    @PostMapping("/edges")
    public Result<List<DeviceEdgeDto>> saveEdges(@CurrentUser Long userId, @Valid @RequestBody List<DeviceEdgeDto> edges) {
        return Result.success(boardService.saveEdges(userId, edges));
    }

    @GetMapping("/specs")
    public Result<List<SpecificationDto>> getSpecs(@CurrentUser Long userId) {
        return Result.success(boardService.getSpecs(userId));
    }

    @PostMapping("/specs")
    public Result<List<SpecificationDto>> saveSpecs(@CurrentUser Long userId, @Valid @RequestBody List<SpecificationDto> specs) {
        return Result.success(boardService.saveSpecs(userId, specs));
    }

    @GetMapping("/rules")
    public Result<List<RuleDto>> getRules(@CurrentUser Long userId) {
        return Result.success(boardService.getRules(userId));
    }

    @PostMapping("/rules")
    public Result<List<RuleDto>> saveRules(@CurrentUser Long userId, @Valid @RequestBody List<RuleDto> rules) {
        return Result.success(boardService.saveRules(userId, rules));
    }

    @GetMapping("/layout")
    public Result<BoardLayoutDto> getLayout(@CurrentUser Long userId) {
        return Result.success(boardService.getLayout(userId));
    }

    @PostMapping("/layout")
    public Result<BoardLayoutDto> saveLayout(@CurrentUser Long userId, @Valid @RequestBody BoardLayoutDto layout) {
        return Result.success(boardService.saveLayout(userId, layout));
    }

    @GetMapping("/active")
    public Result<BoardActiveDto> getActive(@CurrentUser Long userId) {
        return Result.success(boardService.getActive(userId));
    }

    @PostMapping("/active")
    public Result<BoardActiveDto> saveActive(@CurrentUser Long userId, @Valid @RequestBody BoardActiveDto active) {
        return Result.success(boardService.saveActive(userId, active));
    }

    @GetMapping("/templates")
    public Result<List<DeviceTemplateDto>> getTemplates(@CurrentUser Long userId) {
        return Result.success(boardService.getDeviceTemplates(userId));
    }

    @PostMapping("/templates")
    public Result<DeviceTemplateDto> addTemplate(@CurrentUser Long userId, @Valid @RequestBody DeviceTemplateDto dto) {
        return Result.success(boardService.addDeviceTemplate(userId, dto));
    }

    @DeleteMapping("/templates/{id}")
    public Result<Void> deleteTemplate(@CurrentUser Long userId, @PathVariable String id) {
        boardService.deleteDeviceTemplate(userId, id);
        return Result.success();
    }
}
