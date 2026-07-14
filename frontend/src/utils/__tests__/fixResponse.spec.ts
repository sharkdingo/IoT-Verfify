import { describe, expect, it } from 'vitest'
import {
  FIX_RESPONSE_INCOMPLETE_CODE,
  validateFaultLocalizationResult,
  validateFixResult,
  validateFixSuggestion
} from '../fixResponse'

const faultRule = {
  ruleString: 'When hall motion is detected, turn on the light',
  transitionNumber: 2,
  targetDeviceLabel: 'Hall light',
  targetActionLabel: 'Turn on',
  conflicting: false,
  reasonCode: 'TRIGGERED',
  reason: 'This automation fired before the violated state.'
}

const parameterSuggestion = {
  strategy: 'parameter',
  description: 'Change the temperature threshold from 30 to 25.',
  parameterAdjustments: [{
    targetId: 'param_abcdefghijklmnopqrstuvwx',
    attribute: 'temperature',
    relation: '>',
    originalValue: '30',
    newValue: '25',
    lowerBound: 10,
    upperBound: 40,
    description: 'Living room temperature threshold in the cooling rule'
  }],
  verified: true
}

const localization = () => ({
  traceId: 12,
  violatedSpecId: 'spec_1',
  sourceModelComplete: true,
  sourceDisabledRuleCount: 0,
  sourceSkippedSpecCount: 0,
  sourceGenerationIssues: [],
  faultRules: [faultRule],
  summary: 'One automation was involved; this does not prove independent causation.',
  warnings: []
})

const fixResult = () => ({
  ...localization(),
  suggestions: [parameterSuggestion],
  strategyAttempts: [{
    strategy: 'parameter',
    status: 'VERIFIED',
    reason: 'The concrete suggestion passed forward verification.'
  }],
  fixable: true,
  templateSnapshotComparison: 'UNCHANGED',
  summary: 'One forward-verified suggestion was found.',
  warnings: []
})

describe('automatic-fix response contracts', () => {
  it('accepts itemized fault localization on a complete source model', () => {
    expect(validateFaultLocalizationResult(localization(), 12)).toEqual(localization())
  })

  it('requires an incomplete source model to explain the limitation', () => {
    expect(() => validateFaultLocalizationResult({
      ...localization(),
      sourceModelComplete: false
    }, 12)).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('accepts a concrete forward-verified parameter suggestion', () => {
    expect(validateFixSuggestion(parameterSuggestion, 'Fix suggestion', 'parameter'))
      .toEqual(parameterSuggestion)
    expect(validateFixResult(fixResult(), 12, ['parameter'])).toEqual(fixResult())
  })

  it('does not trust a fixable flag without a verified suggestion', () => {
    expect(() => validateFixResult({
      ...fixResult(),
      suggestions: [],
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'NO_VERIFIED_SUGGESTION',
        reason: 'No candidate passed forward verification.'
      }]
    }, 12, ['parameter'])).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('rejects suggestions derived from an explicitly incomplete source model', () => {
    expect(() => validateFixResult({
      ...fixResult(),
      sourceModelComplete: false,
      sourceDisabledRuleCount: 1,
      sourceGenerationIssues: [{
        issueType: 'RULE_DISABLED',
        itemLabel: 'Cooling rule',
        reasonCode: 'RULE_UNRESOLVABLE_TRIGGER_CONDITION',
        reason: 'The target action is unavailable.'
      }],
      warnings: ['The source model was incomplete.']
    }, 12, ['parameter'])).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('requires source omission counts to match itemized reasons', () => {
    expect(() => validateFixResult({
      ...fixResult(),
      sourceModelComplete: false,
      sourceSkippedSpecCount: 1,
      suggestions: [],
      fixable: false,
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'SKIPPED_INCOMPLETE_SOURCE_MODEL',
        reason: 'The source model was incomplete.'
      }],
      warnings: ['The source model was incomplete.']
    }, 12, ['parameter'])).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })
})
