package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRulesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.RecommendRelatedDevicesTool;
import cn.edu.nju.Iot_Verify.component.aitool.rule.CheckDuplicateRuleTool;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ForbiddenException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

import java.util.List;
import java.util.Map;

@Slf4j
@Validated
@RestController
@RequestMapping("/api/board")
@RequiredArgsConstructor
public class BoardStorageController {

    private final BoardStorageService boardService;
    private final RecommendRulesTool recommendRulesTool;
    private final RecommendRelatedDevicesTool recommendRelatedDevicesTool;
    private final CheckDuplicateRuleTool checkDuplicateRuleTool;
    private final ObjectMapper objectMapper;

    @GetMapping("/nodes")
    public Result<List<DeviceNodeDto>> getNodes(@CurrentUser Long userId) {
        return Result.success(boardService.getNodes(userId));
    }

    @PostMapping("/nodes")
    public Result<List<DeviceNodeDto>> saveNodes(@CurrentUser Long userId, @NotNull @Valid @RequestBody List<DeviceNodeDto> nodes) {
        return Result.success(boardService.saveNodes(userId, nodes));
    }

    @GetMapping("/edges")
    public Result<List<DeviceEdgeDto>> getEdges(@CurrentUser Long userId) {
        return Result.success(boardService.getEdges(userId));
    }

    @PostMapping("/edges")
    public Result<List<DeviceEdgeDto>> saveEdges(@CurrentUser Long userId, @NotNull @Valid @RequestBody List<DeviceEdgeDto> edges) {
        return Result.success(boardService.saveEdges(userId, edges));
    }

    @GetMapping("/specs")
    public Result<List<SpecificationDto>> getSpecs(@CurrentUser Long userId) {
        return Result.success(boardService.getSpecs(userId));
    }

    @PostMapping("/specs")
    public Result<List<SpecificationDto>> saveSpecs(@CurrentUser Long userId, @NotNull @Valid @RequestBody List<SpecificationDto> specs) {
        return Result.success(boardService.saveSpecs(userId, specs));
    }

    @GetMapping("/rules")
    public Result<List<RuleDto>> getRules(@CurrentUser Long userId) {
        return Result.success(boardService.getRules(userId));
    }

    @PostMapping("/rules")
    public Result<List<RuleDto>> saveRules(@CurrentUser Long userId, @NotNull @Valid @RequestBody List<RuleDto> rules) {
        return Result.success(boardService.saveRules(userId, rules));
    }

    @GetMapping("/layout")
    public Result<BoardLayoutDto> getLayout(@CurrentUser Long userId) {
        return Result.success(boardService.getLayout(userId));
    }

    @PostMapping("/layout")
    public Result<BoardLayoutDto> saveLayout(@CurrentUser Long userId, @NotNull @Valid @RequestBody BoardLayoutDto layout) {
        return Result.success(boardService.saveLayout(userId, layout));
    }

    @GetMapping("/active")
    public Result<BoardActiveDto> getActive(@CurrentUser Long userId) {
        return Result.success(boardService.getActive(userId));
    }

    @PostMapping("/active")
    public Result<BoardActiveDto> saveActive(@CurrentUser Long userId, @NotNull @Valid @RequestBody BoardActiveDto active) {
        return Result.success(boardService.saveActive(userId, active));
    }

    @GetMapping("/templates")
    public Result<List<DeviceTemplateDto>> getTemplates(@CurrentUser Long userId) {
        return Result.success(boardService.getDeviceTemplates(userId));
    }

    @PostMapping("/templates")
    public Result<DeviceTemplateDto> addTemplate(@CurrentUser Long userId, @NotNull @Valid @RequestBody DeviceTemplateDto dto) {
        return Result.success(boardService.addDeviceTemplate(userId, dto));
    }

    @DeleteMapping("/templates/{id}")
    public Result<Void> deleteTemplate(@CurrentUser Long userId, @PathVariable Long id) {
        boardService.deleteDeviceTemplate(userId, id);
        return Result.success();
    }

    @PostMapping("/templates/reload")
    public Result<Integer> reloadTemplates(@CurrentUser Long userId) {
        int count = boardService.reloadDeviceTemplates(userId);
        return Result.success(count);
    }

    /**
     * 获取规则推荐
     * @param userId 用户ID
     * @param maxRecommendations 最大推荐数量
     * @param category 分类筛选
     * @return 规则推荐列表
     */
    @GetMapping("/rules/recommend")
    public Result<Map<String, Object>> recommendRules(
            @CurrentUser Long userId,
            @RequestParam(defaultValue = "5") Integer maxRecommendations,
            @RequestParam(defaultValue = "all") String category) {

        try {
            String args = objectMapper.writeValueAsString(Map.of(
                    "maxRecommendations", maxRecommendations,
                    "category", category));
            String result = recommendRulesTool.execute(args);

            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(resultMap);
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process rule recommendations", e);
        }
    }

    /**
     * 根据画布中所有设备推荐新设备
     * @param userId 用户ID
     * @param requestBody 包含设备列表和模板列表的请求体
     * @return 设备推荐列表
     */
    @PostMapping("/devices/recommend")
    public Result<Map<String, Object>> recommendDevices(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody Map<String, Object> requestBody) {

        try {
            String argsJson = objectMapper.writeValueAsString(requestBody);
            String result = recommendRelatedDevicesTool.executeBoardRecommendations(argsJson);

            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(resultMap);
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process device recommendations", e);
        }
    }

    /**
     * 检查规则是否重复
     * 当用户添加一条规则后，检查该规则是否与现有规则重复
     * @param userId 用户ID
     * @param rule 新添加的规则
     * @return 重复检查结果
     */
    @PostMapping("/rules/check-duplicate")
    public Result<Map<String, Object>> checkDuplicateRule(
            @CurrentUser Long userId,
            @NotNull @Valid @RequestBody RuleDto rule) {

        try {
            String ruleJson = objectMapper.writeValueAsString(rule);
            String args = String.format("{\"newRule\": %s}", ruleJson);
            String result = checkDuplicateRuleTool.execute(args);

            @SuppressWarnings("unchecked")
            Map<String, Object> resultMap = objectMapper.readValue(result, Map.class);
            throwIfToolError(resultMap);

            return Result.success(resultMap);
        } catch (BaseException e) {
            throw e;
        } catch (Exception e) {
            throw new InternalServerException("Failed to process duplicate rule check", e);
        }
    }

    /**
     * Check if a Tool response is an error JSON and throw the appropriate exception.
     * Tool error format: {"error":"...", "errorCode":"...", "status": <int>}
     */
    private void throwIfToolError(Map<String, Object> resultMap) {
        if (!resultMap.containsKey("errorCode")) {
            return;
        }
        String message = String.valueOf(resultMap.getOrDefault("error", "AI tool error"));
        Object statusObj = resultMap.get("status");
        int status = (statusObj instanceof Number n) ? n.intValue() : 500;

        switch (status) {
            case 400 -> throw new BadRequestException(message);
            case 401 -> throw new UnauthorizedException(message);
            case 403 -> throw new ForbiddenException(message);
            case 404 -> throw new ResourceNotFoundException(message);
            case 409 -> throw new ConflictException(message);
            case 422 -> throw new ValidationException(message);
            case 503 -> throw new ServiceUnavailableException(message);
            default  -> throw new InternalServerException(message);
        }
    }
}
