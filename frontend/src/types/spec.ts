/* ==================== 规约相关类型 ==================== */

export type SpecSide = 'a' | 'if' | 'then'
export type SpecTargetType = 'state' | 'variable' | 'api'
export type SpecTemplateId = '1' | '2' | '3' | '4' | '5' | '6' | '7' | 'safety' | 'liveness' | 'fairness'

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
    formula?: string // LTL formula for simple specifications
    deviceId?: string // Associated device ID for device-specific specs (legacy)
    deviceLabel?: string // Associated device label (legacy)
    devices?: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}> // Multi-device support
}