package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import org.springframework.stereotype.Component;

import java.util.Set;

@Component
public class BoardLayoutMapper {

    private static final double DEFAULT_CONTROL_WIDTH = 320.0;
    private static final double DEFAULT_INSPECTOR_WIDTH = 320.0;
    private static final double DEFAULT_ZOOM = 1.0;
    private static final double MIN_ZOOM = 0.4;
    private static final double MAX_ZOOM = 2.0;
    private static final String DEFAULT_CONTROL_SECTION = "devices";
    private static final String DEFAULT_INSPECTOR_SECTION = "devices";
    private static final Set<String> CONTROL_SECTIONS = Set.of("devices", "templates", "rules", "specs");
    private static final Set<String> INSPECTOR_SECTIONS = Set.of("devices", "rules", "specs");

    private static double d(Double value, double defaultValue) {
        return value != null ? value : defaultValue;
    }

    private static String text(String value, String defaultValue) {
        return value != null && !value.isBlank() ? value : defaultValue;
    }

    public BoardLayoutDto toDto(BoardLayoutPo po) {
        if (po == null) {
            return null;
        }
        BoardLayoutDto dto = new BoardLayoutDto();

        BoardLayoutDto.PanelPosition inputPos = new BoardLayoutDto.PanelPosition();
        inputPos.setX(po.getInputX());
        inputPos.setY(po.getInputY());
        dto.setInput(inputPos);

        BoardLayoutDto.PanelPosition statusPos = new BoardLayoutDto.PanelPosition();
        statusPos.setX(po.getStatusX());
        statusPos.setY(po.getStatusY());
        dto.setStatus(statusPos);

        BoardLayoutDto.DockStateWrapper dockWrapper = new BoardLayoutDto.DockStateWrapper();

        BoardLayoutDto.DockState inputDock = new BoardLayoutDto.DockState();
        inputDock.setIsDocked(po.getInputIsDocked() != null ? po.getInputIsDocked() : false);
        inputDock.setSide(po.getInputDockSide());

        BoardLayoutDto.PanelPosition inputLastPos = new BoardLayoutDto.PanelPosition();
        inputLastPos.setX(po.getInputLastPosX() != null ? po.getInputLastPosX() : 24.0);
        inputLastPos.setY(po.getInputLastPosY() != null ? po.getInputLastPosY() : 24.0);
        inputDock.setLastPos(inputLastPos);

        dockWrapper.setInput(inputDock);

        BoardLayoutDto.DockState statusDock = new BoardLayoutDto.DockState();
        statusDock.setIsDocked(po.getStatusIsDocked() != null ? po.getStatusIsDocked() : false);
        statusDock.setSide(po.getStatusDockSide());

        BoardLayoutDto.PanelPosition statusLastPos = new BoardLayoutDto.PanelPosition();
        statusLastPos.setX(po.getStatusLastPosX() != null ? po.getStatusLastPosX() : 1040.0);
        statusLastPos.setY(po.getStatusLastPosY() != null ? po.getStatusLastPosY() : 80.0);
        statusDock.setLastPos(statusLastPos);

        dockWrapper.setStatus(statusDock);

        dto.setDockState(dockWrapper);

        BoardLayoutDto.CanvasPan pan = new BoardLayoutDto.CanvasPan();
        pan.setX(po.getCanvasPanX());
        pan.setY(po.getCanvasPanY());
        dto.setCanvasPan(pan);

        dto.setCanvasZoom(zoom(po.getCanvasZoom()));

        BoardLayoutDto.Panels panels = new BoardLayoutDto.Panels();
        panels.setControl(panelLayout(
                po.getControlPanelCollapsed(),
                po.getControlPanelWidth(),
                po.getControlPanelActiveSection(),
                DEFAULT_CONTROL_WIDTH,
                DEFAULT_CONTROL_SECTION,
                CONTROL_SECTIONS));
        panels.setInspector(panelLayout(
                po.getInspectorPanelCollapsed(),
                po.getInspectorPanelWidth(),
                po.getInspectorPanelActiveSection(),
                DEFAULT_INSPECTOR_WIDTH,
                DEFAULT_INSPECTOR_SECTION,
                INSPECTOR_SECTIONS));
        dto.setPanels(panels);

        return dto;
    }

    public BoardLayoutPo toEntity(BoardLayoutDto layout, Long id, Long userId) {
        boolean inDocked = false;
        String inSide = null;
        double inLastX = 24.0;
        double inLastY = 24.0;

        if (layout.getDockState() != null && layout.getDockState().getInput() != null) {
            BoardLayoutDto.DockState ds = layout.getDockState().getInput();
            inDocked = Boolean.TRUE.equals(ds.getIsDocked());
            inSide = ds.getSide();
            if (ds.getLastPos() != null) {
                inLastX = ds.getLastPos().getX() != null ? ds.getLastPos().getX() : 24.0;
                inLastY = ds.getLastPos().getY() != null ? ds.getLastPos().getY() : 24.0;
            }
        }

        boolean stDocked = false;
        String stSide = null;
        double stLastX = 1040.0;
        double stLastY = 80.0;

        if (layout.getDockState() != null && layout.getDockState().getStatus() != null) {
            BoardLayoutDto.DockState ds = layout.getDockState().getStatus();
            stDocked = Boolean.TRUE.equals(ds.getIsDocked());
            stSide = ds.getSide();
            if (ds.getLastPos() != null) {
                stLastX = ds.getLastPos().getX() != null ? ds.getLastPos().getX() : 1040.0;
                stLastY = ds.getLastPos().getY() != null ? ds.getLastPos().getY() : 80.0;
            }
        }

        BoardLayoutDto.PanelLayout controlPanel = layout.getPanels() != null
                ? layout.getPanels().getControl()
                : null;
        BoardLayoutDto.PanelLayout inspectorPanel = layout.getPanels() != null
                ? layout.getPanels().getInspector()
                : null;

        return BoardLayoutPo.builder()
                .id(id)
                .userId(userId)
                .inputX(layout.getInput() != null ? d(layout.getInput().getX(), 24.0) : 24.0)
                .inputY(layout.getInput() != null ? d(layout.getInput().getY(), 24.0) : 24.0)
                .statusX(layout.getStatus() != null ? d(layout.getStatus().getX(), 1040.0) : 1040.0)
                .statusY(layout.getStatus() != null ? d(layout.getStatus().getY(), 80.0) : 80.0)
                .canvasPanX(layout.getCanvasPan() != null ? d(layout.getCanvasPan().getX(), 0.0) : 0.0)
                .canvasPanY(layout.getCanvasPan() != null ? d(layout.getCanvasPan().getY(), 0.0) : 0.0)
                .canvasZoom(zoom(layout.getCanvasZoom()))
                .inputIsDocked(inDocked)
                .inputDockSide(inSide)
                .inputLastPosX(inLastX)
                .inputLastPosY(inLastY)
                .statusIsDocked(stDocked)
                .statusDockSide(stSide)
                .statusLastPosX(stLastX)
                .statusLastPosY(stLastY)
                .controlPanelCollapsed(panelCollapsed(controlPanel))
                .controlPanelWidth(panelWidth(controlPanel, DEFAULT_CONTROL_WIDTH))
                .controlPanelActiveSection(panelActiveSection(controlPanel, DEFAULT_CONTROL_SECTION, CONTROL_SECTIONS))
                .inspectorPanelCollapsed(panelCollapsed(inspectorPanel))
                .inspectorPanelWidth(panelWidth(inspectorPanel, DEFAULT_INSPECTOR_WIDTH))
                .inspectorPanelActiveSection(panelActiveSection(inspectorPanel, DEFAULT_INSPECTOR_SECTION, INSPECTOR_SECTIONS))
                .build();
    }

    private BoardLayoutDto.PanelLayout panelLayout(Boolean collapsed,
                                                   Double width,
                                                   String activeSection,
                                                   double defaultWidth,
                                                   String defaultSection,
                                                   Set<String> allowedSections) {
        BoardLayoutDto.PanelLayout panel = new BoardLayoutDto.PanelLayout();
        panel.setCollapsed(Boolean.TRUE.equals(collapsed));
        panel.setWidth(panelWidth(width, defaultWidth));
        panel.setActiveSection(section(activeSection, defaultSection, allowedSections));
        return panel;
    }

    private boolean panelCollapsed(BoardLayoutDto.PanelLayout panel) {
        return panel != null && Boolean.TRUE.equals(panel.getCollapsed());
    }

    private double panelWidth(BoardLayoutDto.PanelLayout panel, double defaultWidth) {
        if (panel == null) {
            return defaultWidth;
        }
        return panelWidth(panel.getWidth(), defaultWidth);
    }

    private double panelWidth(Double width, double defaultWidth) {
        if (width == null || !Double.isFinite(width)) {
            return defaultWidth;
        }
        return Math.min(520.0, Math.max(240.0, width));
    }

    private double zoom(Double value) {
        if (value == null || !Double.isFinite(value)) {
            return DEFAULT_ZOOM;
        }
        return Math.min(MAX_ZOOM, Math.max(MIN_ZOOM, value));
    }

    private String panelActiveSection(BoardLayoutDto.PanelLayout panel, String defaultSection, Set<String> allowedSections) {
        return panel != null ? section(panel.getActiveSection(), defaultSection, allowedSections) : defaultSection;
    }

    private String section(String value, String defaultSection, Set<String> allowedSections) {
        String normalized = text(value, defaultSection);
        return allowedSections.contains(normalized) ? normalized : defaultSection;
    }
}
