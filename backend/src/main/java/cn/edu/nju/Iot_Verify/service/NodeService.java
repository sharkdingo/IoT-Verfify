package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.device.DeviceCreationResultDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceRuntimeConfigDto;

import java.util.List;

public interface NodeService {
    List<DeviceNodeDto> searchNodes(Long userId, String keyword);
    DeviceCreationResultDto addNode(Long userId, String templateName, String label,
                                    Double x, Double y, DeviceRuntimeConfigDto runtime,
                                    Integer w, Integer h);
}
