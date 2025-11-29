// src/main/java/cn/edu/nju/Iot_Verify/service/BoardStorageService.java
package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.*;
import java.util.List;

public interface BoardStorageService {
    List<DeviceNodeDto> getNodes();
    void saveNodes(List<DeviceNodeDto> nodes);

    List<DeviceEdgeDto> getEdges();
    void saveEdges(List<DeviceEdgeDto> edges);

    List<SpecificationDto> getSpecs();
    void saveSpecs(List<SpecificationDto> specs);

    BoardLayoutDto getLayout();
    void saveLayout(BoardLayoutDto layout);

    BoardActiveDto getActive();
    void saveActive(BoardActiveDto active);

    List<DeviceTemplateDto> getDeviceTemplates();
    void addDeviceTemplate(DeviceTemplateDto templateDto);
}
