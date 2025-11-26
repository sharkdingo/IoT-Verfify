// src/main/java/cn/edu/nju/Iot_Verify/po/BoardActivePo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "board_active")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class BoardActivePo {

    @Id
    private Byte id; // 永远1

    @Column(name = "input_tabs", columnDefinition = "JSON", nullable = false)
    private String inputTabsJson;

    @Column(name = "status_tabs", columnDefinition = "JSON", nullable = false)
    private String statusTabsJson;
}
