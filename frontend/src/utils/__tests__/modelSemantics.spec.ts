import { describe, expect, it } from 'vitest'
import type { ModelSemantics } from '@/types/modelSemantics'
import { isModelSemanticsConsistent } from '../modelSemantics'

const semantics = (privacy: ModelSemantics['privacyPropagationPolicy']): ModelSemantics => ({
  attackPointUnit: 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK',
  attackSelectionPolicy: 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC',
  attackEffects: [
    'DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN',
    'COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED',
    'COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED'
  ],
  modeledDeviceAttackPointCount: 2,
  modeledFalsifiableReadingDeviceCount: 1,
  modeledAutomationLinkAttackPointCount: 3,
  modeledAttackPointCount: 5,
  trustPropagationPolicy: 'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED',
  privacyPropagationPolicy: privacy,
  labelPropagationScope: 'AUTOMATION_RULE_COMMANDS_ONLY',
  environmentEvolutionEffects: [
    'DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN',
    'DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
  ],
  localVariableFallbackPolicy: 'STUTTER_WHEN_NO_DECLARED_EVOLUTION'
})

describe('isModelSemanticsConsistent', () => {
  it('accepts the documented attack and privacy policies', () => {
    expect(isModelSemanticsConsistent(
      semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      { isAttack: true, attackBudget: 2, enablePrivacy: true }
    )).toBe(true)
  })

  it('requires no attack effects when attack modeling was disabled', () => {
    expect(isModelSemanticsConsistent({
      ...semantics('NOT_MODELED'),
      attackSelectionPolicy: 'NOT_MODELED',
      attackEffects: []
    }, { isAttack: false, enablePrivacy: false })).toBe(true)
    expect(isModelSemanticsConsistent(
      semantics('NOT_MODELED'),
      { isAttack: false, enablePrivacy: false }
    )).toBe(false)
  })

  it('accepts only the attack effects that this scene can exercise', () => {
    const linkOnly: ModelSemantics = {
      ...semantics('NOT_MODELED'),
      attackEffects: [
        'COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED',
        'COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED'
      ],
      modeledFalsifiableReadingDeviceCount: 0
    }
    expect(isModelSemanticsConsistent(
      linkOnly,
      { isAttack: true, attackBudget: 1, enablePrivacy: false }
    )).toBe(true)
    expect(isModelSemanticsConsistent({
      ...linkOnly,
      attackEffects: [
        ...linkOnly.attackEffects,
        'DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
      ]
    }, { isAttack: true, attackBudget: 1, enablePrivacy: false })).toBe(false)
  })

  it('rejects missing or contradictory model semantics', () => {
    expect(isModelSemanticsConsistent(undefined, { isAttack: true, enablePrivacy: true })).toBe(false)
    expect(isModelSemanticsConsistent(
      semantics('NOT_MODELED'),
      { isAttack: true, enablePrivacy: true }
    )).toBe(false)
    expect(isModelSemanticsConsistent({
      ...semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      modeledAttackPointCount: 4
    }, { isAttack: true, attackBudget: 2, enablePrivacy: true })).toBe(false)
    expect(isModelSemanticsConsistent(
      semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      { isAttack: true, attackBudget: 6, enablePrivacy: true }
    )).toBe(false)
    expect(isModelSemanticsConsistent({
      ...semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      modeledFalsifiableReadingDeviceCount: 3
    }, { isAttack: true, attackBudget: 2, enablePrivacy: true })).toBe(false)
    expect(isModelSemanticsConsistent({
      ...semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      environmentEvolutionEffects: []
    }, { isAttack: true, attackBudget: 2, enablePrivacy: true })).toBe(false)
    expect(isModelSemanticsConsistent({
      ...semantics('TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE'),
      labelPropagationScope: undefined
    } as unknown as ModelSemantics, { isAttack: true, attackBudget: 2, enablePrivacy: true })).toBe(false)
  })
})
