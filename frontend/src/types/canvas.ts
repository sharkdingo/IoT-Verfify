export interface CanvasPan {
    x: number
    y: number
}

// 整个看板布局的数据结构（对应后端 BoardLayoutDto）
export interface BoardLayoutDto {
    input?: PanelPosition
    status?: PanelPosition
    canvasPan?: CanvasPan
    canvasZoom?: number
    dockState?: DockStateWrapper
}

export interface PanelPosition {
    x?: number
    y?: number
}

export interface DockStateWrapper {
    input?: DockState
    status?: DockState
}

export interface DockState {
    isDocked?: boolean
    side?: string // "left", "right", "top", "bottom" or null
    lastPos?: PanelPosition
}