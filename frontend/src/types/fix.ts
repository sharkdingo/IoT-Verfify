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

export type FixStrategyName = 'parameter' | 'condition' | 'disable'

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
  strategy: FixStrategyName
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
  strategies?: FixStrategyName[]
  preferredRanges?: Record<string, PreferredRange>
}

// Preferred value range for parameter-adjustment fixes.
// Must match backend PreferredRange DTO: both fields required, inclusive lower ≤ upper.
export interface PreferredRange {
  lower: number
  upper: number
}

// 应用修复请求：客户端回传当前展示的建议，服务端会重算并校验等价后再落库。
export interface FixApplyRequest {
  strategy: FixStrategyName
  suggestion: FixSuggestion
  preferredRanges?: Record<string, PreferredRange>
}

// 应用修复结果：rules 为后端 RuleDto 形状，调用方通常成功后重新拉取画布规则。
export interface FixApplyResult {
  applied: boolean
  strategy: FixStrategyName
  message: string
  rules: Record<string, unknown>[]
}
