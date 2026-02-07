package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.board.BoardLayoutDto;
import cn.edu.nju.Iot_Verify.po.BoardLayoutPo;
import org.springframework.stereotype.Component;

/**
 * BoardLayout PO 与 DTO 之间的转换映射器
 */
@Component
public class BoardLayoutMapper {

    /**
     * BoardLayoutPo -> BoardLayoutDto
     */
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
        inputLastPos.setX(po.getInputLastPosX());
        inputLastPos.setY(po.getInputLastPosY());
        inputDock.setLastPos(inputLastPos);

        dockWrapper.setInput(inputDock);

        BoardLayoutDto.DockState statusDock = new BoardLayoutDto.DockState();
        statusDock.setIsDocked(po.getStatusIsDocked() != null ? po.getStatusIsDocked() : false);
        statusDock.setSide(po.getStatusDockSide());

        BoardLayoutDto.PanelPosition statusLastPos = new BoardLayoutDto.PanelPosition();
        statusLastPos.setX(po.getStatusLastPosX());
        statusLastPos.setY(po.getStatusLastPosY());
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

    /**
     * BoardLayoutDto -> BoardLayoutPo
     */
    public BoardLayoutPo toEntity(BoardLayoutDto dto) {
        if (dto == null) {
            return null;
        }
        BoardLayoutPo po = new BoardLayoutPo();

        if (dto.getInput() != null) {
            po.setInputX(dto.getInput().getX());
            po.setInputY(dto.getInput().getY());
        }

        if (dto.getStatus() != null) {
            po.setStatusX(dto.getStatus().getX());
            po.setStatusY(dto.getStatus().getY());
        }

        if (dto.getCanvasPan() != null) {
            po.setCanvasPanX(dto.getCanvasPan().getX());
            po.setCanvasPanY(dto.getCanvasPan().getY());
        }

        po.setCanvasZoom(dto.getCanvasZoom());

        if (dto.getDockState() != null && dto.getDockState().getInput() != null) {
            BoardLayoutDto.DockState ds = dto.getDockState().getInput();
            po.setInputIsDocked(Boolean.TRUE.equals(ds.getIsDocked()));
            po.setInputDockSide(ds.getSide());
            if (ds.getLastPos() != null) {
                po.setInputLastPosX(ds.getLastPos().getX());
                po.setInputLastPosY(ds.getLastPos().getY());
            }
        }

        if (dto.getDockState() != null && dto.getDockState().getStatus() != null) {
            BoardLayoutDto.DockState ds = dto.getDockState().getStatus();
            po.setStatusIsDocked(Boolean.TRUE.equals(ds.getIsDocked()));
            po.setStatusDockSide(ds.getSide());
            if (ds.getLastPos() != null) {
                po.setStatusLastPosX(ds.getLastPos().getX());
                po.setStatusLastPosY(ds.getLastPos().getY());
            }
        }

        return po;
    }
}
