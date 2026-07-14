// src/main/java/cn/edu/nju/Iot_Verify/dto/board/BoardLayoutDto.java
package cn.edu.nju.Iot_Verify.dto.board;

import lombok.Data;

@Data
public class BoardLayoutDto {
    private CanvasPan canvasPan;
    private Double canvasZoom;
    private Panels panels;

    @Data
    public static class CanvasPan {
        private Double x;
        private Double y;
    }

    @Data
    public static class Panels {
        private PanelLayout control;
        private PanelLayout inspector;
    }

    @Data
    public static class PanelLayout {
        private Boolean collapsed;
        private Double width;
        private String activeSection;
    }
}
