package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import org.springframework.stereotype.Component;

@Component
public class BoardLayoutMapper {

    private static double d(Double value, double defaultValue) {
        return value != null ? value : defaultValue;
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

        dto.setCanvasZoom(po.getCanvasZoom());

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

        return BoardLayoutPo.builder()
                .id(id)
                .userId(userId)
                .inputX(layout.getInput() != null ? d(layout.getInput().getX(), 24.0) : 24.0)
                .inputY(layout.getInput() != null ? d(layout.getInput().getY(), 24.0) : 24.0)
                .statusX(layout.getStatus() != null ? d(layout.getStatus().getX(), 1040.0) : 1040.0)
                .statusY(layout.getStatus() != null ? d(layout.getStatus().getY(), 80.0) : 80.0)
                .canvasPanX(layout.getCanvasPan() != null ? d(layout.getCanvasPan().getX(), 0.0) : 0.0)
                .canvasPanY(layout.getCanvasPan() != null ? d(layout.getCanvasPan().getY(), 0.0) : 0.0)
                .canvasZoom(layout.getCanvasZoom() != null ? layout.getCanvasZoom() : 1.0)
                .inputIsDocked(inDocked)
                .inputDockSide(inSide)
                .inputLastPosX(inLastX)
                .inputLastPosY(inLastY)
                .statusIsDocked(stDocked)
                .statusDockSide(stSide)
                .statusLastPosX(stLastX)
                .statusLastPosY(stLastY)
                .build();
    }
}
