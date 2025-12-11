// src/main/java/cn/edu/nju/Iot_Verify/service/DeviceTemplateService.java
package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;

import java.util.List;
import java.util.Optional;

public interface DeviceTemplateService {
    /**
     * 获取所有模板 manifest 中的 name 字段列表
     * (用于模糊匹配等业务)
     */
    List<String> getAllTemplateNames();

    Optional<DeviceTemplatePo> findTemplateByName(String name);
    boolean checkTemplateExists(String name);
}