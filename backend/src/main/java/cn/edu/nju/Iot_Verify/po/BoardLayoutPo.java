package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "board_layout")
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class BoardLayoutPo {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @EqualsAndHashCode.Include
    private Long id;

    @Column(name = "user_id", nullable = false, unique = true)
    private Long userId;

    @Column(name = "canvas_pan_x")
    private Double canvasPanX;

    @Column(name = "canvas_pan_y")
    private Double canvasPanY;

    @Column(name = "canvas_zoom")
    private Double canvasZoom;

    @Column(name = "control_panel_collapsed")
    private Boolean controlPanelCollapsed;

    @Column(name = "control_panel_width")
    private Double controlPanelWidth;

    @Column(name = "control_panel_active_section")
    private String controlPanelActiveSection;

    @Column(name = "inspector_panel_collapsed")
    private Boolean inspectorPanelCollapsed;

    @Column(name = "inspector_panel_width")
    private Double inspectorPanelWidth;

    @Column(name = "inspector_panel_active_section")
    private String inspectorPanelActiveSection;
}
