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
  const expectedAttackSelection = context.isAttack
    ? 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC'
    : 'NOT_MODELED'
  if (semantics.attackSelectionPolicy !== expectedAttackSelection) return false
  if (context.isAttack && context.attackBudget != null
      && (!Number.isInteger(context.attackBudget)
        || context.attackBudget < 1
        || context.attackBudget > semantics.modeledAttackPointCount)) return false
  if (!context.isAttack) return effects.size === 0
  const expectedEffects = new Set<AttackEffect>()
  if (semantics.modeledFalsifiableReadingDeviceCount > 0) {
    expectedEffects.add('DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN')
  }
  if (semantics.modeledAutomationLinkAttackPointCount > 0) {
    expectedEffects.add('COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED')
    expectedEffects.add('COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED')
  }
  return effects.size === expectedEffects.size
    && [...expectedEffects].every(effect => effects.has(effect))
}
