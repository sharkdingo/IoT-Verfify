/**
 * Fix 功能相关类型定义
 * 对应后端 DTO: FaultRuleDto, FixResultDto, FixSuggestionDto, ParameterAdjustment, ConditionAdjustment
 */

// 故障规则定位结果
export interface FaultRule {
  ruleIndex: number
  ruleId?: number
  ruleString: string
  triggerStep: number
  targetDevice: string
  targetAction: string
  conflicting: boolean
  conflictWithRuleIndex?: number
  reason: string
}

// §5.1 参数调整结果
export interface ParameterAdjustment {
  ruleIndex: number
  conditionIndex: number
  attribute: string
  relation: string
  originalValue: string
  newValue: string
  lowerBound: number
  upperBound: number
}

// §5.2 条件调整结果
export interface ConditionAdjustment {
  ruleIndex: number
  conditionIndex: number
  action: 'remove' | 'keep' | 'add'
  attribute: string
  description: string
  deviceName?: string
  relation?: string
  value?: string
}

// 修复建议
export interface FixSuggestion {
  strategy: 'parameter' | 'condition' | 'disable'
  description: string
  parameterAdjustments?: ParameterAdjustment[]
  conditionAdjustments?: ConditionAdjustment[]
  disabledRuleIndices?: number[]
  verified: boolean
}

// 修复结果
export interface FixResult {
  traceId: number
  violatedSpecId: string
  faultRules: FaultRule[]
  suggestions: FixSuggestion[]
  fixable: boolean
  summary: string
  unusedPreferredRangeKeys?: string[]
}

// 修复请求（可选）
export interface FixRequest {
  strategies?: ('parameter' | 'condition' | 'disable')[]
  preferredRanges?: Record<string, PreferredRange>
}

// 参数化调整的首选范围
export interface PreferredRange {
  lowerBound?: number
  upperBound?: number
  excludeValues?: number[]
}
