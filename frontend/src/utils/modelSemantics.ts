import type { AttackEffect, EnvironmentEvolutionEffect, ModelSemantics } from '@/types/modelSemantics'

const ENVIRONMENT_EVOLUTION_EFFECTS: ReadonlySet<EnvironmentEvolutionEffect> = new Set([
  'DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN',
  'DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
])

export const isModelSemanticsConsistent = (
  semantics: ModelSemantics | null | undefined,
  context: { isAttack?: boolean | null; attackBudget?: number | null; enablePrivacy?: boolean | null }
): boolean => {
  if (!semantics || semantics.attackPointUnit !== 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK') return false
  const counts = [
    semantics.modeledDeviceAttackPointCount,
    semantics.modeledFalsifiableReadingDeviceCount,
    semantics.modeledAutomationLinkAttackPointCount,
    semantics.modeledAttackPointCount
  ]
  if (!counts.every(value => Number.isInteger(value) && value >= 0)) return false
  if (semantics.modeledAttackPointCount
      !== semantics.modeledDeviceAttackPointCount + semantics.modeledAutomationLinkAttackPointCount) return false
  if (semantics.modeledFalsifiableReadingDeviceCount
      > semantics.modeledDeviceAttackPointCount) return false
  if (semantics.trustPropagationPolicy
      !== 'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED') return false
  if (semantics.labelPropagationScope !== 'AUTOMATION_RULE_COMMANDS_ONLY') return false
  if (semantics.localVariableFallbackPolicy !== 'STUTTER_WHEN_NO_DECLARED_EVOLUTION') return false

  const environmentEffects = new Set(semantics.environmentEvolutionEffects || [])
  if (environmentEffects.size !== ENVIRONMENT_EVOLUTION_EFFECTS.size
      || ![...ENVIRONMENT_EVOLUTION_EFFECTS].every(effect => environmentEffects.has(effect))) return false

  const expectedPrivacy = context.enablePrivacy
    ? 'TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'
    : 'NOT_MODELED'
  if (semantics.privacyPropagationPolicy !== expectedPrivacy) return false

  const effects = new Set(semantics.attackEffects || [])
  const selectedPoints = semantics.selectedAttackPoints || []
  if (!context.isAttack) {
    return semantics.attackSelectionPolicy === 'NOT_MODELED'
      && selectedPoints.length === 0
      && effects.size === 0
  }
  if (!['EXACT_ATTACK_POINTS', 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC']
    .includes(semantics.attackSelectionPolicy)) return false
  if (context.attackBudget != null
      && (!Number.isInteger(context.attackBudget)
        || context.attackBudget < 1
        || context.attackBudget > semantics.modeledAttackPointCount)) return false
  if (semantics.attackSelectionPolicy === 'EXACT_ATTACK_POINTS') {
    if (selectedPoints.length < 1 || selectedPoints.length !== context.attackBudget) return false
    const identities = new Set<string>()
    let selectedDeviceCount = 0
    let selectedLinkCount = 0
    for (const point of selectedPoints) {
      if (point.displayLabel != null
          && (typeof point.displayLabel !== 'string' || !point.displayLabel.trim())) return false
      let identity: string
      if (point?.kind === 'DEVICE' && typeof point.deviceId === 'string' && point.deviceId.trim()) {
        identity = `DEVICE:${point.deviceId}`
        selectedDeviceCount += 1
      } else if (point?.kind === 'AUTOMATION_LINK'
          && Number.isInteger(point.ruleId) && point.ruleId > 0) {
        identity = `AUTOMATION_LINK:${point.ruleId}`
        selectedLinkCount += 1
      } else {
        return false
      }
      if (identities.has(identity)) return false
      identities.add(identity)
    }
    if (selectedDeviceCount > semantics.modeledDeviceAttackPointCount
        || selectedLinkCount > semantics.modeledAutomationLinkAttackPointCount) return false
    if (selectedLinkCount > 0
        && !effects.has('COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED')) return false
  } else if (selectedPoints.length !== 0) return false

  const knownEffects = new Set<AttackEffect>([
    'DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN',
    'COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED',
    'COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED'
  ])
  if ([...effects].some(effect => !knownEffects.has(effect))) return false
  if (effects.has('DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN')
      && semantics.modeledFalsifiableReadingDeviceCount < 1) return false
  if (effects.has('COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED')
      && (semantics.modeledDeviceAttackPointCount < 1
        || semantics.modeledAutomationLinkAttackPointCount < 1)) return false
  if (effects.has('COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED')
      && semantics.modeledAutomationLinkAttackPointCount < 1) return false
  return true
}
