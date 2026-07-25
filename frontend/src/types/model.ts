import type { NodePrivacyState, NodeVariableState } from './node'
import type { RuleSourceItemType } from './rule'
import type { Specification } from './spec'

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

export type ModelSpecification = Specification
