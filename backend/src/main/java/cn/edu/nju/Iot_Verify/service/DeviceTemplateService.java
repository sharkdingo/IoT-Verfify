package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;

import java.util.List;
import java.util.Optional;

public interface DeviceTemplateService {
    List<String> getAllTemplateNames(Long userId);
    Optional<DeviceTemplatePo> findTemplateByName(Long userId, String name);
    boolean checkTemplateExists(Long userId, String name);
}
