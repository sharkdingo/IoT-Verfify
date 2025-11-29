// src/types/panel.ts

// 引用 CanvasPan，假设它定义在 canvas.ts 中
import type { CanvasPan } from './canvas'

/* ================== 基础类型定义 ================== */

export type PanelKey = 'input' | 'status'

export type DockSide = 'left' | 'right' | 'top' | 'bottom' | null

export interface PanelPosition {
    x: number
    y: number
}

/* ================== 停靠状态 ================== */

export interface DockState {
    isDocked: boolean
    side: DockSide
    lastPos: PanelPosition // 记录停靠前的坐标，用于恢复
}

/* ================== DTO (数据传输对象) ================== */

// 整个看板布局的数据结构（对应后端存储的 JSON）
export interface BoardLayoutDto {
    // 面板坐标
    input: PanelPosition
    status: PanelPosition

    // 面板停靠状态 (新增!)
    dockState: {
        input: DockState
        status: DockState
    }

    // 画布状态
    canvasPan: CanvasPan
    canvasZoom: number
}

/* ================== 折叠面板状态 ================== */

export interface PanelActive {
    input: string[]
    status: string[]
}