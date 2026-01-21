// src/main/java/cn/edu/nju/Iot_Verify/po/SpecificationPo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "specification")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class SpecificationPo {

    @Id
    @Column(length = 100)
    private String id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "template_id", nullable = false, length = 10)
    private String templateId;

    @Column(name = "template_label", nullable = false, length = 255)
    private String templateLabel;

    @Column(name = "a_conditions", columnDefinition = "JSON", nullable = false)
    private String aConditionsJson;

    @Column(name = "if_conditions", columnDefinition = "JSON", nullable = false)
    private String ifConditionsJson;

    @Column(name = "then_conditions", columnDefinition = "JSON", nullable = false)
    private String thenConditionsJson;
}
