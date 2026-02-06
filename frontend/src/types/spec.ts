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

/**
 * 规约模板详细配置
 */
export type SpecTemplateType = 
    | 'always'      // A holds forever - 只有a条件
    | 'eventually'  // A will happen later - 只有a条件
    | 'never'       // A never happens - 只有a条件
    | 'immediate'   // A → B (at same time) - if + then
    | 'response'    // A → ◇B (eventually) - if + then
    | 'persistence' // A → □B (forever after) - if + then
    | 'safety'      // untrusted → ¬A - if + then

export interface SpecTemplateDetail extends SpecTemplate {
    type: SpecTemplateType
    description: string
    requiredSides: SpecSide[]  // 需要配置的条件位置
    ltlFormula: string         // 对应的LTL公式
}

export interface SpecForm {
    templateId: SpecTemplateId | ''
    templateType: SpecTemplateType | ''
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

/**
 * 关系运算符
 */
export const relationOperators = [
    { value: '=', label: '等于 (=)' },
    { value: '!=', label: '不等于 (≠)' },
    { value: '>', label: '大于 (>)' },
    { value: '>=', label: '大于等于 (≥)' },
    { value: '<', label: '小于 (<)' },
    { value: '<=', label: '小于等于 (≤)' },
    { value: 'contains', label: '包含' },
    { value: 'not_contains', label: '不包含' },
    { value: 'matches', label: '匹配正则' },
    { value: 'in', label: '在列表中 (in)' },
    { value: 'not_in', label: '不在列表中 (not in)' }
] as const

export type RelationOperator = typeof relationOperators[number]['value']

/**
 * 目标类型
 */
export const targetTypes = [
    { value: 'state', label: '设备状态' },
    { value: 'variable', label: '变量值' },
    { value: 'api', label: 'API调用' }
] as const

export type TargetType = typeof targetTypes[number]['value']
