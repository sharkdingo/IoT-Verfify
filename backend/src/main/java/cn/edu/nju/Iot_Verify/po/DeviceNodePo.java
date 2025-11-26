// src/main/java/cn/edu/nju/Iot_Verify/po/DeviceNodePo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "device_node")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class DeviceNodePo {

    @Id
    @Column(length = 100)
    private String id;

    @Column(name = "template_name", nullable = false, length = 100)
    private String templateName;

    @Column(nullable = false, length = 255)
    private String label;

    @Column(name = "pos_x", nullable = false)
    private Double posX;

    @Column(name = "pos_y", nullable = false)
    private Double posY;

    @Column(nullable = false, length = 50)
    private String state;

    @Column(nullable = false)
    private Integer width;

    @Column(nullable = false)
    private Integer height;
}
