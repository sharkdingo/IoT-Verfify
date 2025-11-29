// src/main/java/cn/edu/nju/Iot_Verify/dto/DeviceTemplateDto.java
package cn.edu.nju.Iot_Verify.dto;

import cn.edu.nju.Iot_Verify.dto.manifest.DeviceManifest;
import lombok.Data;
import java.util.Map;

/**
 * 设备模板 DTO
 * 用于接收前端传入的复杂 JSON 对象
 */
@Data
public class DeviceTemplateDto {
    private String id;
    private String name;

    // [Modified] 使用强类型 Manifest
    private DeviceManifest manifest;
}