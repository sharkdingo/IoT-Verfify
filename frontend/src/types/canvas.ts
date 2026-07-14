export interface CanvasPan {
    x: number
    y: number
}

// 整个看板布局的数据结构（对应后端 BoardLayoutDto）
export interface BoardLayoutDto {
    canvasPan?: CanvasPan
    canvasZoom?: number
    panels?: BoardPanels
}

export interface BoardPanels {
    control?: BoardPanelLayout
    inspector?: BoardPanelLayout
}

export interface BoardPanelLayout {
    collapsed?: boolean
    width?: number
    activeSection?: string
}
