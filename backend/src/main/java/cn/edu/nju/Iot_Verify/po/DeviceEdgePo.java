// src/main/java/cn/edu/nju/Iot_Verify/po/DeviceEdgePo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "device_edge")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class DeviceEdgePo {

    @Id
    @Column(length = 100)
    private String id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "`from`", nullable = false, length = 100)
    private String from;

    @Column(name = "`to`", nullable = false, length = 100)
    private String to;

    @Column(name = "from_label", nullable = false, length = 255)
    private String fromLabel;

    @Column(name = "to_label", nullable = false, length = 255)
    private String toLabel;

    @Column(name = "from_api", nullable = false, length = 255)
    private String fromApi;

    @Column(name = "to_api", nullable = false, length = 255)
    private String toApi;

    @Column(name = "from_pos_x", nullable = false)
    private Double fromPosX;

    @Column(name = "from_pos_y", nullable = false)
    private Double fromPosY;

    @Column(name = "to_pos_x", nullable = false)
    private Double toPosX;

    @Column(name = "to_pos_y", nullable = false)
    private Double toPosY;
}
