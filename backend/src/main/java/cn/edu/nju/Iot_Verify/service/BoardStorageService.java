package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.List;

public interface BoardStorageService {
    List<DeviceNodeDto> getNodes(Long userId);
    List<DeviceNodeDto> saveNodes(Long userId, List<DeviceNodeDto> nodes);

    List<DeviceEdgeDto> getEdges(Long userId);
    List<DeviceEdgeDto> saveEdges(Long userId, List<DeviceEdgeDto> edges);

    List<SpecificationDto> getSpecs(Long userId);
    List<SpecificationDto> saveSpecs(Long userId, List<SpecificationDto> specs);
    /** Atomically add a single spec under user-level lock. */
    List<SpecificationDto> addSpec(Long userId, SpecificationDto spec);
    /** Atomically remove a single spec by ID under user-level lock. Returns remaining specs, or null if not found. */
    List<SpecificationDto> removeSpec(Long userId, String specId);

    List<RuleDto> getRules(Long userId);
    List<RuleDto> saveRules(Long userId, List<RuleDto> rules);
    /** Atomically add a single rule under user-level lock. */
    List<RuleDto> addRule(Long userId, RuleDto rule);
    /** Atomically remove a single rule by ID under user-level lock. Returns remaining rules, or null if not found. */
    List<RuleDto> removeRule(Long userId, long ruleId);

    /**
     * Atomic read-modify-write of a user's rules under the per-user write lock and one transaction.
     * The mutator receives the current persisted rules and returns the new list to save; any exception
     * it throws rolls back without saving. Use this when a decision (e.g. drift check) must be made on
     * the same snapshot that is written, so a concurrent save cannot interleave between read and write.
     */
    List<RuleDto> updateRules(Long userId, java.util.function.UnaryOperator<List<RuleDto>> mutator);

    /**
     * Atomically save nodes + rules + specs in one transaction under the user write lock.
     * A null collection in the batch is left unchanged. Used for device delete/rename where the three
     * collections must change together to avoid a half-saved board.
     */
    BoardBatchDto saveBoardBatch(Long userId, BoardBatchDto batch);

    BoardLayoutDto getLayout(Long userId);
    BoardLayoutDto saveLayout(Long userId, BoardLayoutDto layout);

    List<DeviceTemplateDto> getDeviceTemplates(Long userId);
    DeviceTemplateDto addDeviceTemplate(Long userId, DeviceTemplateDto templateDto);
    void deleteDeviceTemplate(Long userId, Long templateId);

    /**
     * 重新加载设备模板（从资源文件重新初始化默认模板）
     * @param userId 用户ID
     * @return 重新加载的模板数量
     */
    int reloadDeviceTemplates(Long userId);
}
