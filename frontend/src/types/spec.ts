/* ==================== 规约相关类型 ==================== */

export type SpecSide = 'a' | 'if' | 'then'
export type SpecTargetType = 'state' | 'variable' | 'api' | 'trust' | 'privacy'
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

/**
 * 规约模板详细配置
 */
export type SpecTemplateType = 
    | 'always'      // A holds forever - 只有a条件
    | 'eventually'  // A will happen later - 只有a条件
    | 'never'       // A never happens - 只有a条件
    | 'immediate'   // A → AX B (next state) - if + then
    | 'response'    // A → ◇B (eventually) - if + then
    | 'persistence' // A → □B (forever after) - if + then
    | 'safety'      // untrusted → ¬A - only a-conditions

export interface SpecTemplateDetail extends SpecTemplate {
    type: SpecTemplateType
    description: string
    requiredSides: SpecSide[]  // 需要配置的条件位置
    ltlFormula: string         // 对应的LTL公式
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

// NOTE: the runtime option lists `relationOperators` and `targetTypes` (and their
// derived types) live in `@/assets/config/specTemplates.ts`, which is what components
// import. Duplicate copies previously here were unused and have been removed to avoid
// two sources drifting apart.
