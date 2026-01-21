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
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;

    @Column(name = "user_id", nullable = false, unique = true)
    private Long userId;

    @Column(name = "input_tabs", columnDefinition = "JSON", nullable = false)
    private String inputTabsJson;

    @Column(name = "status_tabs", columnDefinition = "JSON", nullable = false)
    private String statusTabsJson;
}
