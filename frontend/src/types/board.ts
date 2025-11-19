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

/* ==================== 规约相关类型 ==================== */

export type SpecSide = 'a' | 'if' | 'then'
export type SpecTargetType = 'state' | 'variable' | 'api'
export type SpecTemplateId = '1' | '2' | '3' | '4' | '5' | '6' | '7'

export interface SpecCondition {
    id: string
    side: SpecSide
    deviceId: string
    deviceLabel: string
    targetType: SpecTargetType
    key: string
    relation: string
    value: string
}

export interface SpecTemplate {
    id: SpecTemplateId
    label: string
}

export interface SpecForm {
    templateId: SpecTemplateId | ''
    aConditions: SpecCondition[]
    ifConditions: SpecCondition[]
    thenConditions: SpecCondition[]
}

export interface Specification {
    id: string
    templateId: SpecTemplateId
    templateLabel: string
    aConditions: SpecCondition[]
    ifConditions: SpecCondition[]
    thenConditions: SpecCondition[]
}

export interface PanelPositions {
    left: { x: number; y: number }
    status: { x: number; y: number }
}

export interface PanelActive {
    input: string[]   // InputPanel: ['devices', 'rules', 'specs']
    status: string[]  // StatusPanel: ['devices', 'edges', 'specs']
}
