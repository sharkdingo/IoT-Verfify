import type { NodePrivacyState, NodeVariableState } from './node'
import type { RuleSourceItemType } from './rule'
import type { Specification } from './spec'
import type { DeviceNode } from './node'

export const RUN_INITIATORS = ['USER', 'AI_ASSISTANT', 'UNKNOWN'] as const
export type RunInitiator = typeof RUN_INITIATORS[number]

export const isRunInitiator = (value: unknown): value is RunInitiator =>
  typeof value === 'string' && (RUN_INITIATORS as readonly string[]).includes(value)

export interface ModelDevice {
  varName: string
  deviceLabel: string
  templateName: string
  state?: string
  currentStateTrust?: string
  currentStatePrivacy?: string
  variables?: NodeVariableState[]
  privacies?: NodePrivacyState[]
}

export interface ModelEnvironmentVariable {
  name: string
  value?: string | null
  trust?: string | null
  privacy?: string | null
}

/** Compare-and-set request used by the public Environment Pool mutation endpoint. */
export interface EnvironmentVariableUpdateRequest {
  name: string
  expected: {
    value: string
    trust: string
    privacy: string
  }
  desired: Partial<{
    value: string
    trust: string
    privacy: string
  }>
}

export interface ModelRuleCondition {
  deviceName: string
  attribute: string
  targetType: RuleSourceItemType
  relation?: string
  value?: string
}

export interface ModelRuleCommand {
  deviceName: string
  action: string
  contentDevice?: string | null
  content?: string | null
}

export interface ModelRule {
  // Persisted board identity used only to map trace rule snapshots back to current canvas rules.
  // Portable scene rules and unsaved UI drafts omit it.
  id?: number
  conditions: ModelRuleCondition[]
  command: ModelRuleCommand
  ruleString?: string
}

/** Immutable visual context for replaying one run independently of the live board. */
export interface ModelPlaybackScene {
  nodes: DeviceNode[]
  rules: ModelRule[]
}

export type ModelSpecification = Specification

export type ValueType = 'NUMERIC' | 'DISCRETE_ENUM' | 'DISCRETE_BOOLEAN'
export type AuthorshipCategory = 'EXOGENOUS' | 'DEVICE_CONTROLLED' | 'COMPOSED'
export type SemanticsTag = 'EXACT' | 'ABSTRACTION'

export const MODEL_TOKEN_SOURCES = ['BUNDLED', 'CUSTOM', 'UNKNOWN'] as const
export type ModelTokenSource = typeof MODEL_TOKEN_SOURCES[number]

export interface DeviceWriter {
  deviceVarName: string
  templateName: string
  templateSource: ModelTokenSource
}

export interface DeviceReader {
  deviceVarName: string
}

/**
 * Per-value semantic provenance for one environment variable in a frozen run.
 * Makes historical counterexamples self-explanatory without consulting the current Board.
 */
export interface EnvironmentValueProvenance {
  name: string
  type: ValueType
  lowerBound?: number | null
  upperBound?: number | null
  naturalChangeRate?: string | null
  values?: string[]
  authorship: AuthorshipCategory
  writers: DeviceWriter[]
  readers: DeviceReader[]
  semantics: SemanticsTag
  evolutionSummary: string
}

export interface ModelRunSnapshot {
  capturedAt: string
  deviceCount: number
  ruleCount: number
  specificationCount: number
  environmentVariableCount: number
  deviceTemplateCount: number
  modelFingerprint?: string | null
  templatesFrozen?: boolean
  environmentProvenance?: EnvironmentValueProvenance[]
}

