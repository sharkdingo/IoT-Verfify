package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.board.BoardActiveDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.DeviceEdgeDto;
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

    List<RuleDto> getRules(Long userId);
    List<RuleDto> saveRules(Long userId, List<RuleDto> rules);

    BoardLayoutDto getLayout(Long userId);
    BoardLayoutDto saveLayout(Long userId, BoardLayoutDto layout);

    BoardActiveDto getActive(Long userId);
    BoardActiveDto saveActive(Long userId, BoardActiveDto active);

    List<DeviceTemplateDto> getDeviceTemplates(Long userId);
    DeviceTemplateDto addDeviceTemplate(Long userId, DeviceTemplateDto templateDto);
    void deleteDeviceTemplate(Long userId, String templateId);

    /**
     * 重新加载设备模板（从资源文件重新初始化默认模板）
     * @param userId 用户ID
     * @return 重新加载的模板数量
     */
    int reloadDeviceTemplates(Long userId);
}
