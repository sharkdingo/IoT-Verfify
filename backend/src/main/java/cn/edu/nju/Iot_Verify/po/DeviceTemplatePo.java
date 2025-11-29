// src/main/java/cn/edu/nju/Iot_Verify/po/DeviceTemplatePo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

/**
 * 设备模板实体类
 * 对应数据库表: device_templates
 */
@Entity
@Table(name = "device_templates")
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceTemplatePo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    // 模板名称，必须唯一
    @Column(nullable = false, unique = true)
    private String name;

    // 存储 manifest 的 JSON 字符串
    // 使用 @Lob 和 columnDefinition 确保能存储大文本数据 (MySQL中对应 LONGTEXT/TEXT)
    @Lob
    @Column(name = "manifest_json", columnDefinition = "TEXT")
    private String manifestJson;
}