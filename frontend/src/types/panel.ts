// src/types/panel.ts

/* ================== 基础类型定义 ================== */

// PanelKey type removed as all panels are removed

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
// BoardLayoutDto removed as panel system is removed

/* ================== 折叠面板状态 ================== */

export interface PanelActive {
    status: string[]
}