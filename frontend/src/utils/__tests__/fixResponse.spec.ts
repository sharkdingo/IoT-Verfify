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
  reason: 'This automation fired before the violated state.',
  modelTokenSource: 'BUNDLED'
}

const parameterSuggestion = {
  suggestionToken: 'signed-parameter-suggestion',
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
    description: 'Living room temperature threshold in the cooling rule',
    modelTokenSource: 'BUNDLED'
  }],
  conditionAdjustments: [],
  removedRuleDescriptions: [],
  verified: true
}

const conditionSuggestion = {
  suggestionToken: 'signed-condition-suggestion',
  strategy: 'condition',
  description: 'Only heat while the room is occupied.',
  parameterAdjustments: [],
  conditionAdjustments: [{
    action: 'add',
    attribute: 'occupied',
    targetType: 'variable',
    description: 'Require an occupied room before heating.',
    ruleDescription: 'When it is cold, heat the room',
    deviceLabel: 'Living-room Occupancy Sensor',
    relation: '=',
    value: 'present',
    modelTokenSource: 'CUSTOM'
  }],
  removedRuleDescriptions: [],
  verified: true
}

const removeSuggestion = {
  suggestionToken: 'signed-remove-suggestion',
  strategy: 'remove',
  description: 'Remove the automation that takes a camera photo.',
  parameterAdjustments: [],
  conditionAdjustments: [],
  removedRuleDescriptions: ['When hall motion is active, take a camera photo'],
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
  warnings: [],
  parameterTargets: [{
    targetId: 'param_abcdefghijklmnopqrstuvwx',
    attribute: 'temperature',
    relation: '>',
    originalValue: '30',
    lowerBound: 10,
    upperBound: 40,
    description: 'Living room temperature threshold in the cooling rule',
    modelTokenSource: 'BUNDLED'
  }],
  unusedPreferredRangeSelections: []
})

const fixResultFor = (suggestion: typeof parameterSuggestion | typeof conditionSuggestion | typeof removeSuggestion) => ({
  ...fixResult(),
  suggestions: [suggestion],
  strategyAttempts: [{
    strategy: suggestion.strategy,
    status: 'VERIFIED',
    reason: 'The concrete suggestion passed forward verification.'
  }],
  parameterTargets: suggestion.strategy === 'parameter' ? fixResult().parameterTargets : []
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

  it('rejects a fix result that omits an array required by the backend contract', () => {
    const { unusedPreferredRangeSelections: _unused, ...incomplete } = fixResult()

    expect(() => validateFixResult(incomplete, 12, ['parameter'])).toThrow(
      expect.objectContaining({ code: FIX_RESPONSE_INCOMPLETE_CODE })
    )
  })

  it('requires explicit model-token provenance for user-visible fix rows', () => {
    const { modelTokenSource: _source, ...targetWithoutSource } = fixResult().parameterTargets[0]
    expect(() => validateFixResult({
      ...fixResult(),
      parameterTargets: [targetWithoutSource]
    }, 12, ['parameter'])).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it.each([
    ['parameter', parameterSuggestion],
    ['condition', conditionSuggestion],
    ['remove', removeSuggestion]
  ] as const)('accepts the concrete %s strategy response shape used by the UI', (strategy, suggestion) => {
    expect(validateFixSuggestion(suggestion, 'Fix suggestion', strategy)).toEqual(suggestion)
    const result = fixResultFor(suggestion)
    expect(validateFixResult(result, 12, [strategy])).toEqual(result)
  })

  it('accepts one default response containing all three verified strategies', () => {
    const result = {
      ...fixResult(),
      suggestions: [parameterSuggestion, conditionSuggestion, removeSuggestion],
      strategyAttempts: ['parameter', 'condition', 'remove'].map(strategy => ({
        strategy,
        status: 'VERIFIED',
        reason: 'The concrete suggestion passed forward verification.'
      }))
    }

    expect(validateFixResult(result, 12, [])).toEqual(result)
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

  it('rejects specification-only trust conditions in a rule adjustment', () => {
    expect(() => validateFixSuggestion({
      suggestionToken: 'signed-condition-suggestion',
      strategy: 'condition',
      description: 'Add a trust condition',
      parameterAdjustments: [],
      conditionAdjustments: [{
        action: 'add',
        attribute: 'temperature',
        targetType: 'trust',
        description: 'Add trust predicate',
        ruleDescription: 'Cooling rule',
        deviceLabel: 'Temperature sensor',
        relation: '=',
        value: 'trusted'
      }],
      removedRuleDescriptions: [],
      verified: true
    }, 'Fix suggestion', 'condition')).toThrow(expect.objectContaining({
      code: FIX_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('accepts a distinct candidate-model generation failure outcome', () => {
    const result = {
      ...fixResult(),
      suggestions: [],
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'FAILED_MODEL_GENERATION',
        reason: 'The counterexample initial state is incomplete.'
      }],
      fixable: false,
      warnings: ['The counterexample initial state is incomplete.']
    }

    expect(validateFixResult(result, 12, ['parameter'])).toEqual(result)
  })

  it('accepts solver failure and budget exhaustion with bounded attempt progress', () => {
    const solverFailure = {
      ...fixResult(),
      suggestions: [],
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'FAILED_SOLVER_EXECUTION',
        reason: 'NuSMV returned incomplete output.',
        attemptsUsed: 3,
        attemptLimit: 7
      }],
      fixable: false
    }
    const budgetExhausted = {
      ...fixResult(),
      suggestions: [],
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'SEARCH_BUDGET_EXHAUSTED',
        reason: 'Unchecked candidates remain.',
        attemptsUsed: 7,
        attemptLimit: 7
      }],
      fixable: false
    }

    expect(validateFixResult(solverFailure, 12, ['parameter'])).toEqual(solverFailure)
    expect(validateFixResult(budgetExhausted, 12, ['parameter'])).toEqual(budgetExhausted)
  })

  it('rejects incomplete or impossible attempt progress', () => {
    const missingLimit = {
      ...fixResult(),
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'SEARCH_BUDGET_EXHAUSTED',
        reason: 'Unchecked candidates remain.',
        attemptsUsed: 3
      }]
    }
    const overLimit = {
      ...fixResult(),
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'SEARCH_BUDGET_EXHAUSTED',
        reason: 'Unchecked candidates remain.',
        attemptsUsed: 8,
        attemptLimit: 7
      }]
    }

    expect(() => validateFixResult(missingLimit, 12, ['parameter'])).toThrow(
      expect.objectContaining({ code: FIX_RESPONSE_INCOMPLETE_CODE })
    )
    expect(() => validateFixResult(overLimit, 12, ['parameter'])).toThrow(
      expect.objectContaining({ code: FIX_RESPONSE_INCOMPLETE_CODE })
    )
  })

  it('accepts parameter targets even when the search found no suggestion', () => {
    const result = {
      ...fixResult(),
      suggestions: [],
      strategyAttempts: [{
        strategy: 'parameter',
        status: 'NO_VERIFIED_SUGGESTION',
        reason: 'No candidate passed forward verification.'
      }],
      fixable: false
    }

    expect(validateFixResult(result, 12, ['parameter'])).toEqual(result)
    expect(result.parameterTargets).toHaveLength(1)
  })
})
