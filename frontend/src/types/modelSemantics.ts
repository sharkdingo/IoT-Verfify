export type AttackPointUnit = 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK'

export type AttackEffect =
  | 'DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
  | 'COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED'
  | 'COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED'

export type AttackSelectionPolicy =
  | 'NOT_MODELED'
  | 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC'

export type TrustPropagationPolicy =
  'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED'

export type PrivacyPropagationPolicy =
  | 'TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'
  | 'NOT_MODELED'

export type LabelPropagationScope = 'AUTOMATION_RULE_COMMANDS_ONLY'

export type EnvironmentEvolutionEffect =
  | 'DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN'
  | 'DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'

export type LocalVariableFallbackPolicy =
  'STUTTER_WHEN_NO_DECLARED_EVOLUTION'

export interface ModelSemantics {
  attackPointUnit: AttackPointUnit
  attackSelectionPolicy: AttackSelectionPolicy
  attackEffects: AttackEffect[]
  modeledDeviceAttackPointCount: number
  modeledFalsifiableReadingDeviceCount: number
  modeledAutomationLinkAttackPointCount: number
  modeledAttackPointCount: number
  trustPropagationPolicy: TrustPropagationPolicy
  privacyPropagationPolicy: PrivacyPropagationPolicy
  labelPropagationScope: LabelPropagationScope
  environmentEvolutionEffects: EnvironmentEvolutionEffect[]
  localVariableFallbackPolicy: LocalVariableFallbackPolicy
}

/** User-facing scope frozen at submission for one verification or simulation run. */
export interface ModelRunSnapshot {
  capturedAt: string
  deviceCount: number
  ruleCount: number
  specificationCount: number
  environmentVariableCount: number
  deviceTemplateCount: number
  templatesFrozen: true
}

/** Local UI comparison between a submitted run input and the board currently open in this tab. */
export type RunBoardComparison = 'UNCHANGED' | 'CHANGED' | 'UNAVAILABLE' | 'NOT_COMPARED'
