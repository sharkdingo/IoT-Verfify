// src/main/java/cn/edu/nju/Iot_Verify/dto/board/BoardLayoutDto.java
package cn.edu.nju.Iot_Verify.dto.board;

import lombok.Data;

@Data
public class BoardLayoutDto {
    private PanelPosition input;
    private PanelPosition status;
    private CanvasPan canvasPan;
    private Double canvasZoom;
    private DockStateWrapper dockState;

    @Data
    public static class PanelPosition {
        private Double x;
        private Double y;
    }

    @Data
    public static class CanvasPan {
        private Double x;
        private Double y;
    }

    @Data
    public static class DockStateWrapper {
        private DockState input;
        private DockState status;
    }

    @Data
    public static class DockState {
        private Boolean isDocked;
        private String side; // "left", "right", "top", "bottom" or null
        private PanelPosition lastPos;
    }
}
