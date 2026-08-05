import type { NodePrivacyState, NodeVariableState } from './node'
import type { RuleSourceItemType } from './rule'
import type { Specification } from './spec'
import type { DeviceNode } from './node'
import type { ModelTokenSource } from './modelToken'

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

/**
 * A rule inside a frozen playback scene.
 *
 * This and `BackendRuleDto` in `api/board.ts` both mirror the backend's `RuleDto` — the playback scene carries
 * `List<RuleDto>` too — and they described it differently: `id?: number` versus `id: number | null`, and
 * `ruleString?: string` versus `string | null`. The nullable forms are the accurate ones: `RuleDto.id` is a
 * `Long` and `ruleString` is populated by `optionalText`, which returns null. So this type forbade a value the
 * server can actually send.
 *
 * No live misread came of it — `playbackScene.ts` uses `rule.id ?? ruleIndex` and `rule.id == null`, both of
 * which cover null and undefined — but the type was documenting a contract the server does not honour.
 * `RuleDto.createdAt` is deliberately still absent from both mirrors: it is on the wire and nothing reads it, so
 * declaring it would document an unused field rather than a used one.
 */
export interface ModelRule {
  // Persisted board identity used only to map trace rule snapshots back to current canvas rules.
  // Portable scene rules and unsaved UI drafts omit it, so it is optional *and* nullable.
  id?: number | null
  conditions: ModelRuleCondition[]
  command: ModelRuleCommand
  ruleString?: string | null
}

/** Immutable visual context for replaying one run independently of the live board. */
export interface ModelPlaybackScene {
  nodes: DeviceNode[]
  rules: ModelRule[]
}

export type ModelSpecification = Specification

/** Domain shape of a shared value, mirroring `EnvironmentValueProvenanceDto.ValueType`. */
export type ValueType = 'NUMERIC' | 'DISCRETE_ENUM' | 'DISCRETE_BOOLEAN'

/**
 * Who may change a shared value during a run. See
 * `docs/architecture/shared-value-semantics.md` §7 for the authoritative rules.
 */
export type AuthorshipCategory = 'EXOGENOUS' | 'DEVICE_CONTROLLED' | 'COMPOSED'

/** Whether the evolution rule means exactly what the user declared, or over-approximates it. */
export type SemanticsTag = 'EXACT' | 'ABSTRACTION'

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

// ModelRunSnapshot lives in ./modelSemantics — every consumer imports it from there, and a
// second declaration here would let the two drift apart silently.

