package cn.edu.nju.Iot_Verify.component.nusmv.data;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import lombok.Data;

/**
 * NuSMV 模板包装器
 * 用于安全地关联设备模板 PO 和 Manifest
 */
@Data
public class TemplateWrapper {
    
    /**
     * 设备模板持久化对象（类型安全）
     */
    public DeviceTemplatePo templatePo;
    
    /**
     * 设备模板 Manifest（强类型解析后的对象）
     */
    public DeviceManifest manifest;
    
    /**
     * 默认构造函数
     */
    public TemplateWrapper() {
    }
    
    /**
     * 带 Manifest 的构造函数
     * @param manifest 解析后的模板 Manifest
     */
    public TemplateWrapper(DeviceManifest manifest) {
        this.manifest = manifest;
    }
    
    /**
     * 带模板 PO 和 Manifest 的构造函数
     * @param templatePo 设备模板持久化对象
     * @param manifest 解析后的模板 Manifest
     */
    public TemplateWrapper(DeviceTemplatePo templatePo, DeviceManifest manifest) {
        this.templatePo = templatePo;
        this.manifest = manifest;
    }
}
