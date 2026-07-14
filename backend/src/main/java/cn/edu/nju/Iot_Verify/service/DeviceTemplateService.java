package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;

import java.util.List;
import java.util.Optional;

public interface DeviceTemplateService {
    Optional<DeviceTemplatePo> findTemplateByName(Long userId, String name);
    boolean checkTemplateExists(Long userId, String name);

    /**
     * 为新用户初始化默认设备模板（从 resource/deviceTemplate 目录加载）
     *
     * @param userId 用户ID
     * @return 加载的模板数量
     */
    int initDefaultTemplates(Long userId);

    /**
     * 强制导入系统默认模板。调用方应先清理当前用户默认模板或同名覆盖模板。
     *
     * @param userId 用户ID
     * @return 导入的模板数量
     */
    int importDefaultTemplates(Long userId);

    /**
     * Loads and validates every bundled default as unsaved entities for impact previews.
     * Any missing, malformed, or duplicate resource fails the whole load.
     */
    List<DeviceTemplatePo> getDefaultTemplateDefinitions(Long userId);

}
