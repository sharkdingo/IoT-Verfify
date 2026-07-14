/**
 * Fix 功能相关类型定义
 * 对应后端 DTO: FaultRuleDto, FixResultDto, FixSuggestionDto, ParameterAdjustment, ConditionAdjustment
 */

import type { RuleForm, RuleSourceItemType } from './rule'
import type { ModelGenerationIssue } from './verify'

// 故障规则定位结果
export interface FaultRule {
  ruleString: string
  transitionNumber: number
  targetDeviceLabel: string
  targetActionLabel: string
  conflicting: boolean
  conflictingRuleString?: string
  targetEndState?: string
  conflictingEndState?: string
  reasonCode: 'TRIGGERED' | 'CONFLICTING_END_STATES'
  reason: string
}

export interface FaultLocalizationResult {
  traceId: number
  violatedSpecId: string
  sourceModelComplete: boolean
  sourceDisabledRuleCount: number
  sourceSkippedSpecCount: number
  sourceGenerationIssues: ModelGenerationIssue[]
  faultRules: FaultRule[]
  summary: string
  warnings: string[]
}

export type FixStrategyName = 'parameter' | 'condition' | 'remove'

// §5.1 参数调整结果
export interface ParameterAdjustment {
  targetId: string
  attribute: string
  relation: string
  originalValue: string
  newValue: string
  lowerBound: number
  upperBound: number
  description: string
}

// §5.2 条件调整结果
export interface ConditionAdjustment {
  action: 'remove' | 'keep' | 'add'
  attribute: string
  targetType?: RuleSourceItemType
  description: string
  ruleDescription?: string
  deviceLabel?: string
  relation?: string
  value?: string
}

// 修复建议
export interface FixSuggestion {
  strategy: FixStrategyName
  description: string
  parameterAdjustments?: ParameterAdjustment[]
  conditionAdjustments?: ConditionAdjustment[]
  removedRuleDescriptions?: string[]
  verified: boolean
}

export type FixStrategyAttemptStatus =
  | 'VERIFIED'
  | 'NOT_VERIFIED'
  | 'NO_VERIFIED_SUGGESTION'
  | 'TIMED_OUT'
  | 'SKIPPED_TIMEOUT'
  | 'SKIPPED_NO_SPEC'
  | 'SKIPPED_NO_FAULT_RULES'
  | 'SKIPPED_INCOMPLETE_SOURCE_MODEL'
  | 'SKIPPED_UNSUPPORTED'

export interface FixStrategyAttempt {
  strategy: FixStrategyName
  status: FixStrategyAttemptStatus
  reason: string
}

export type TemplateSnapshotComparison = 'NOT_CHECKED' | 'UNCHANGED' | 'CHANGED' | 'UNAVAILABLE'

// 修复结果
export interface FixResult {
  traceId: number
  violatedSpecId: string
  faultRules: FaultRule[]
  suggestions: FixSuggestion[]
  strategyAttempts: FixStrategyAttempt[]
  fixable: boolean
  sourceModelComplete: boolean
  sourceDisabledRuleCount: number
  sourceSkippedSpecCount: number
  sourceGenerationIssues: ModelGenerationIssue[]
  templateSnapshotComparison: TemplateSnapshotComparison
  summary: string
  warnings: string[]
  unusedPreferredRangeSelections?: PreferredRangeSelection[]
}

// 修复请求（可选）
export interface FixRequest {
  strategies?: FixStrategyName[]
  preferredRangeSelections?: PreferredRangeSelection[]
}

// Preferred value range for parameter-adjustment fixes.
// Must match backend PreferredRange DTO: both fields required, inclusive lower ≤ upper.
export interface PreferredRange {
  lower: number
  upper: number
}

// User/API-facing preferred value range target selected from a parameter adjustment.
export interface PreferredRangeSelection extends PreferredRange {
  targetId: string
}

// Apply a strategy only. The backend recomputes and verifies the concrete proposal from the trace.
export interface FixApplyRequest {
  strategy: FixStrategyName
  preferredRangeSelections?: PreferredRangeSelection[]
}

// Applied-fix result after boardApi maps the authoritative backend RuleDto snapshot.
export interface FixApplyResult {
  applied: boolean
  strategy: FixStrategyName
  verificationRechecked: boolean
  appliedSuggestion: FixSuggestion
  previousRuleCount: number
  currentRuleCount: number
  message: string
  rules: RuleForm[]
}
