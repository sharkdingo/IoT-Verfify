// src/main/java/cn/edu/nju/Iot_Verify/po/BoardLayoutPo.java
package cn.edu.nju.Iot_Verify.po;

import jakarta.persistence.*;
import lombok.*;

@Entity
@Table(name = "board_layout")
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class BoardLayoutPo {

    @Id
    @Column(name = "id")
    private Byte id;   // 固定用 1 作为唯一一条记录

    @Column(name = "input_x")
    private Double inputX;

    @Column(name = "input_y")
    private Double inputY;

    @Column(name = "status_x")
    private Double statusX;

    @Column(name = "status_y")
    private Double statusY;

    @Column(name = "canvas_pan_x")
    private Double canvasPanX;

    @Column(name = "canvas_pan_y")
    private Double canvasPanY;

    @Column(name = "canvas_zoom")
    private Double canvasZoom;

    // --- Input Dock State (新增) ---
    @Column(name = "input_is_docked")
    private Boolean inputIsDocked;

    @Column(name = "input_dock_side")
    private String inputDockSide;

    @Column(name = "input_last_pos_x")
    private Double inputLastPosX;

    @Column(name = "input_last_pos_y")
    private Double inputLastPosY;

    // --- Status Dock State (新增) ---
    @Column(name = "status_is_docked")
    private Boolean statusIsDocked;

    @Column(name = "status_dock_side")
    private String statusDockSide;

    @Column(name = "status_last_pos_x")
    private Double statusLastPosX;

    @Column(name = "status_last_pos_y")
    private Double statusLastPosY;
}