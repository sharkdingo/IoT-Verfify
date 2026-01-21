package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "device_rule")
@Data
@NoArgsConstructor
@AllArgsConstructor
@Builder
public class RulePo {

    @Id
    @Column(length = 100)
    private String id;

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(name = "sources_json", columnDefinition = "JSON", nullable = false)
    private String sourcesJson;

    @Column(name = "to_id", nullable = false, length = 100)
    private String toId;

    @Column(name = "to_api", nullable = false, length = 255)
    private String toApi;

    @Column(name = "template_label", length = 255)
    private String templateLabel;
}




