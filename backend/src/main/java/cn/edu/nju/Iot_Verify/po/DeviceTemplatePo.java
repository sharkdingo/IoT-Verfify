package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

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

    @Column(name = "user_id", nullable = false)
    private Long userId;

    @Column(nullable = false)
    private String name;

    @Lob
    @Column(name = "manifest_json", columnDefinition = "TEXT")
    private String manifestJson;
}
