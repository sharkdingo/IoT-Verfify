// src/types/board.ts

export interface CanvasPan {
    x: number
    y: number
}

export interface DeviceNode {
    id: string
    templateName: string   // AC_Cooler
    label: string          // AC_Cooler 或 AC_Cooler_1
    position: {
        x: number
        y: number
    }
    state: string          // Working / Off ...
    width: number
    height: number
}

export interface DeviceEdge {
    id: string
    from: string           // node.id
    to: string             // node.id
    fromLabel: string
    toLabel: string
    fromApi: string
    toApi: string
    fromPos: { x: number; y: number }
    toPos: { x: number; y: number }
}

export interface RuleForm {
    fromId: string
    fromApi: string
    toId: string
    toApi: string
}

export interface PanelPositions {
    left: { x: number; y: number }
    status: { x: number; y: number }
}

export interface PanelActive {
    input: string[]   // InputPanel: ['devices', 'rules', 'specs']
    status: string[]  // StatusPanel: ['devices', 'edges', 'specs']
}
