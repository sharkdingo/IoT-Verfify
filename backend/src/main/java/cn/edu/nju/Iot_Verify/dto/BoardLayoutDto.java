// src/main/java/cn/edu/nju/Iot_Verify/dto/BoardLayoutDto.java
package cn.edu.nju.Iot_Verify.dto;

import lombok.Data;

@Data
public class BoardLayoutDto {
    private PanelPosition input;
    private PanelPosition status;
    private CanvasPan canvasPan;
    private Double canvasZoom;

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
}
