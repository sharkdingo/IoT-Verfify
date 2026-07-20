// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { beforeEach, describe, expect, it, vi } from 'vitest'
import FixResultDialog from '../FixResultDialog.vue'
import type { FixResult } from '@/types/fix'

const elementPlus = vi.hoisted(() => ({
  confirm: vi.fn(),
  success: vi.fn(),
  warning: vi.fn(),
  error: vi.fn()
}))

vi.mock('element-plus', () => ({
  ElMessage: {
    success: elementPlus.success,
    warning: elementPlus.warning,
    error: elementPlus.error
  },
  ElMessageBox: { confirm: elementPlus.confirm }
}))

const boardApi = vi.hoisted(() => ({
  getFaultRules: vi.fn(),
  getFixRequestStatus: vi.fn(),
  fixTrace: vi.fn(),
  cancelFixRequest: vi.fn(),
  applyFix: vi.fn()
}))

vi.mock('@/api/board', () => ({ default: boardApi }))

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: new Proxy({}, {
        get: (_target, key) => String(key)
      })
    }
  },
  missingWarn: false,
  fallbackWarn: false
})

const flush = () => new Promise(resolve => setTimeout(resolve, 0))

const deferred = <T>() => {
  let resolve!: (value: T) => void
  const promise = new Promise<T>(done => { resolve = done })
  return { promise, resolve }
}

const removeResult = (): FixResult => ({
  traceId: 7,
  violatedSpecId: 'spec-1',
  faultRules: [],
  suggestions: [{
    suggestionToken: 'signed-remove-suggestion',
    strategy: 'remove',
    description: 'Permanently remove the unsafe automation',
    parameterAdjustments: [],
    conditionAdjustments: [],
    removedRuleDescriptions: ['Gas leak unlocks exit'],
    verified: true
  }],
  strategyAttempts: [{
    strategy: 'remove',
    status: 'VERIFIED',
    reason: 'Passed forward verification.'
  }],
  fixable: true,
  sourceModelComplete: true,
  sourceDisabledRuleCount: 0,
  sourceSkippedSpecCount: 0,
  sourceGenerationIssues: [],
  templateSnapshotComparison: 'UNCHANGED',
  summary: 'One verified suggestion.',
  warnings: [],
  parameterTargets: [],
  unusedPreferredRangeSelections: []
})

const parameterResult = (): FixResult => ({
  ...removeResult(),
  suggestions: [{
    suggestionToken: 'signed-parameter-suggestion',
    strategy: 'parameter',
    description: 'Adjust the gas threshold',
    parameterAdjustments: [{
      targetId: 'param_abcdefghijklmnopqrstuvwx',
      attribute: 'gas',
      relation: '>',
      originalValue: '70',
      newValue: '85',
      lowerBound: 71,
      upperBound: 100,
      description: 'Gas threshold in the exit-unlock rule'
    }],
    conditionAdjustments: [],
    removedRuleDescriptions: [],
    verified: true
  }],
  strategyAttempts: [{
    strategy: 'parameter',
    status: 'VERIFIED',
    reason: 'Passed forward verification.'
  }],
  parameterTargets: [{
    targetId: 'param_abcdefghijklmnopqrstuvwx',
    attribute: 'gas',
    relation: '>',
    originalValue: '70',
    lowerBound: 0,
    upperBound: 100,
    description: 'Gas threshold in the exit-unlock rule'
  }]
})

const conditionResult = (): FixResult => ({
  ...removeResult(),
  suggestions: [{
    suggestionToken: 'signed-condition-suggestion',
    strategy: 'condition',
    description: 'Only heat while the room is occupied',
    parameterAdjustments: [],
    conditionAdjustments: [{
      action: 'add',
      attribute: 'occupied',
      targetType: 'variable',
      description: 'Require the living room to be occupied',
      ruleDescription: 'When it is cold, heat the room',
      deviceLabel: 'Living-room Occupancy Sensor',
      relation: '=',
      value: 'present'
    }],
    removedRuleDescriptions: [],
    verified: true
  }],
  strategyAttempts: [{
    strategy: 'condition',
    status: 'VERIFIED',
    reason: 'Passed forward verification.'
  }]
})

const jointParameterResult = (): FixResult => {
  const result = parameterResult()
  const suggestion = result.suggestions[0]!
  const first = suggestion.parameterAdjustments[0]!
  const second = {
    ...first,
    targetId: 'param_zyxwvutsrqponmlkjihgfedc',
    originalValue: '72',
    newValue: '86',
    description: 'Backup gas threshold in the exit-unlock rule'
  }
  const { newValue: _newValue, ...secondTarget } = second
  return {
    ...result,
    suggestions: [{ ...suggestion, parameterAdjustments: [first, second] }],
    parameterTargets: [
      ...result.parameterTargets,
      secondTarget
    ]
  }
}

const jointConditionResult = (): FixResult => {
  const result = conditionResult()
  const suggestion = result.suggestions[0]!
  const first = suggestion.conditionAdjustments[0]!
  return {
    ...result,
    suggestions: [{
      ...suggestion,
      conditionAdjustments: [
        first,
        {
          ...first,
          ruleDescription: 'Backup heating rule',
          description: 'Require occupancy on the backup heating rule'
        }
      ]
    }]
  }
}

const jointRemoveResult = (): FixResult => {
  const result = removeResult()
  const suggestion = result.suggestions[0]!
  return {
    ...result,
    suggestions: [{
      ...suggestion,
      removedRuleDescriptions: ['Primary unsafe heating rule', 'Backup unsafe heating rule']
    }]
  }
}

const duplicateNameRemoveResult = (): FixResult => {
  const result = removeResult()
  return {
    ...result,
    suggestions: [{
      ...result.suggestions[0]!,
      removedRuleDescriptions: ['Shared automation name', 'Shared automation name']
    }]
  }
}

const boundaryParameterResult = (relation: '>' | '>='): FixResult => {
  const result = parameterResult()
  const adjustment = result.suggestions[0]!.parameterAdjustments[0]!
  return {
    ...result,
    suggestions: [{
      ...result.suggestions[0]!,
      parameterAdjustments: [{
        ...adjustment,
        relation,
        newValue: '100',
        upperBound: 100
      }]
    }]
  }
}

const conditionWithoutSuggestionResult = (): FixResult => ({
  ...removeResult(),
  suggestions: [],
  strategyAttempts: [{
    strategy: 'condition',
    status: 'NO_VERIFIED_SUGGESTION',
    reason: 'The strategy ran, but no candidate suggestion passed forward checking.'
  }],
  fixable: false
})

const parameterWithoutSuggestionResult = (): FixResult => ({
  ...parameterResult(),
  suggestions: [],
  strategyAttempts: [{
    strategy: 'parameter',
    status: 'NO_VERIFIED_SUGGESTION',
    reason: 'No candidate passed forward verification.'
  }],
  fixable: false
})

const parameterBudgetExhaustedResult = (): FixResult => ({
  ...parameterResult(),
  suggestions: [],
  strategyAttempts: [{
    strategy: 'parameter',
    status: 'SEARCH_BUDGET_EXHAUSTED',
    reason: 'Unchecked candidates remain.',
    attemptsUsed: 5,
    attemptLimit: 5
  }],
  fixable: false
})

const mountDialog = () => mount(FixResultDialog, {
  props: { visible: true, traceId: 7, violatedSpecId: 'spec-1' },
  global: { plugins: [i18n] }
})

describe('FixResultDialog strategy workflow', () => {
  beforeEach(() => {
    vi.useRealTimers()
    vi.clearAllMocks()
    boardApi.getFaultRules.mockResolvedValue({
      traceId: 7,
      violatedSpecId: 'spec-1',
      sourceModelComplete: true,
      sourceDisabledRuleCount: 0,
      sourceSkippedSpecCount: 0,
      sourceGenerationIssues: [],
      faultRules: [],
      summary: 'No user-defined automation rule was localized.',
      warnings: []
    })
    boardApi.getFixRequestStatus.mockResolvedValue({
      requestId: 'request-123',
      state: 'RUNNING',
      stage: 'SEARCHING_AND_VERIFYING',
      elapsedMs: 1000
    })
    boardApi.cancelFixRequest.mockResolvedValue(true)
    elementPlus.confirm.mockResolvedValue('confirm')
  })

  it('opens with fault localization only and does not implicitly run an expensive strategy', async () => {
    const wrapper = mountDialog()
    await flush()

    expect(boardApi.getFaultRules).toHaveBeenCalledWith(7)
    expect(boardApi.fixTrace).not.toHaveBeenCalled()
    expect(wrapper.get('[data-testid="fix-result-header"]').classes()).toContain('flex-shrink-0')
    expect(wrapper.get('[data-testid="fix-result-scroll"]').classes()).toContain('min-h-0')
    expect(wrapper.text()).toContain('faultLocalizationNoRuleCaveat')
    expect(wrapper.text()).not.toContain('No user-defined automation rule was localized.')
    expect(wrapper.get('[data-testid="fix-result-dialog"]').classes()).toContain('z-[2500]')
    expect(wrapper.find('[data-testid="fix-strategy-remove"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-try-current"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)
  })

  it('runs only the selected strategy and keeps apply hidden until a verified response arrives', async () => {
    const pending = deferred<FixResult>()
    boardApi.fixTrace.mockReturnValueOnce(pending.promise)
    const wrapper = mountDialog()
    await flush()

    await wrapper.get('[data-testid="fix-strategy-remove"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')

    expect(boardApi.fixTrace).toHaveBeenCalledWith(7, {
      strategies: ['remove'],
      preferredRangeSelections: undefined
    }, expect.objectContaining({
      requestId: expect.any(String),
      signal: expect.anything()
    }))
    expect(wrapper.find('[data-testid="fix-strategy-loading"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)

    pending.resolve(removeResult())
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.find('[data-testid="fix-strategy-loading"]').exists()).toBe(false)
    expect(wrapper.get('[data-testid="fix-apply-current"]').attributes('disabled')).toBeUndefined()
  })

  it('cancels an active search when the parent hides the dialog', async () => {
    const pending = deferred<FixResult>()
    boardApi.fixTrace.mockReturnValueOnce(pending.promise)
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')

    const options = boardApi.fixTrace.mock.calls[0]![2]
    expect(options.signal.aborted).toBe(false)
    await wrapper.setProps({ visible: false })
    await wrapper.vm.$nextTick()

    expect(options.signal.aborted).toBe(true)
    expect(boardApi.cancelFixRequest).toHaveBeenCalledWith(options.requestId)
    expect(wrapper.find('[data-testid="fix-result-dialog"]').exists()).toBe(false)
  })

  it('contains a failed server cancellation after aborting the local search', async () => {
    const pending = deferred<FixResult>()
    const cancellationError = new Error('network unavailable')
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {})
    boardApi.fixTrace.mockReturnValueOnce(pending.promise)
    boardApi.cancelFixRequest.mockRejectedValueOnce(cancellationError)
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')

    const options = boardApi.fixTrace.mock.calls[0]![2]
    await wrapper.setProps({ visible: false })
    await flush()

    expect(options.signal.aborted).toBe(true)
    expect(warn).toHaveBeenCalledWith(
      expect.stringContaining(`[Fix] Failed to cancel automatic-fix request ${options.requestId}`),
      cancellationError
    )
    warn.mockRestore()
  })

  it('shows the server-observed automatic-fix phase while the strategy is running', async () => {
    const pending = deferred<FixResult>()
    boardApi.fixTrace.mockReturnValueOnce(pending.promise)
    const wrapper = mountDialog()
    await flush()

    vi.useFakeTimers()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await vi.advanceTimersByTimeAsync(1000)
    await wrapper.vm.$nextTick()

    expect(boardApi.getFixRequestStatus).toHaveBeenCalledWith(expect.any(String))
    expect(wrapper.text()).toContain('fixProgressStage_SEARCHING_AND_VERIFYING')

    vi.useRealTimers()
    pending.resolve(parameterResult())
    await flush()
  })

  it('invalidates an old verified suggestion before retrying that strategy', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(true)

    const retry = deferred<FixResult>()
    boardApi.fixTrace.mockReturnValueOnce(retry.promise)
    await wrapper.get('[data-testid="fix-run-with-preferences"]').trigger('click')

    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)
    expect(wrapper.find('[data-testid="fix-strategy-loading"]').exists()).toBe(true)
  })

  it('retains independently verified suggestions while trying all three strategies', async () => {
    boardApi.fixTrace
      .mockResolvedValueOnce(parameterResult())
      .mockResolvedValueOnce(conditionResult())
      .mockResolvedValueOnce(removeResult())
    const wrapper = mountDialog()
    await flush()

    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.get('[data-testid="fix-strategy-condition"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.get('[data-testid="fix-strategy-remove"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    expect(boardApi.fixTrace).toHaveBeenNthCalledWith(1, 7, {
      strategies: ['parameter'],
      preferredRangeSelections: undefined
    }, expect.any(Object))
    expect(boardApi.fixTrace).toHaveBeenNthCalledWith(2, 7, {
      strategies: ['condition'],
      preferredRangeSelections: undefined
    }, expect.any(Object))
    expect(boardApi.fixTrace).toHaveBeenNthCalledWith(3, 7, {
      strategies: ['remove'],
      preferredRangeSelections: undefined
    }, expect.any(Object))

    await wrapper.get('[data-testid="fix-strategy-parameter"]').trigger('click')
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(true)
    expect(wrapper.text()).toContain('85')
    await wrapper.get('[data-testid="fix-strategy-condition"]').trigger('click')
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(true)
    expect(wrapper.text()).toContain('addConditionAdjustment')
    await wrapper.get('[data-testid="fix-strategy-remove"]').trigger('click')
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(true)
    expect(wrapper.text()).toContain('Gas leak unlocks exit')
  })

  it.each([
    ['parameter', jointParameterResult, 'parameterAdjustments (2)'],
    ['condition', jointConditionResult, 'conditionAdjustments (2)'],
    ['remove', jointRemoveResult, 'rulesToRemove (2)']
  ] as const)('renders and submits every item in a coordinated %s suggestion', async (
    strategy,
    resultFactory,
    countText
  ) => {
    const result = resultFactory()
    boardApi.fixTrace.mockResolvedValueOnce(result)
    boardApi.applyFix.mockResolvedValueOnce({
      applied: true,
      strategy,
      verificationRechecked: false,
      verificationEvidenceReused: true,
      appliedSuggestion: result.suggestions[0],
      previousRuleCount: 3,
      currentRuleCount: strategy === 'remove' ? 1 : 3,
      message: 'Applied coordinated suggestion.',
      rules: []
    })
    const wrapper = mountDialog()
    await flush()
    if (strategy !== 'parameter') {
      await wrapper.get(`[data-testid="fix-strategy-${strategy}"]`).trigger('click')
    }
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.text()).toContain(countText)
    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()
    expect(boardApi.applyFix).toHaveBeenCalledWith(7, result.suggestions[0], undefined)
  })

  it('renders two distinct removal operations even when their display names match', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(duplicateNameRemoveResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-strategy-remove"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    const removals = wrapper.findAll('[data-testid="fix-removed-rule"]')
    expect(removals).toHaveLength(2)
    expect(removals.map(item => item.text())).toEqual([
      'Shared automation name',
      'Shared automation name'
    ])
  })

  it.each([
    ['>', true],
    ['>=', false]
  ] as const)('shows an unreachable-rule warning only for a strict %s upper boundary', async (
    relation,
    expectedWarning
  ) => {
    boardApi.fixTrace.mockResolvedValueOnce(boundaryParameterResult(relation))
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.find('[data-testid="fix-parameter-unreachable-warning"]').exists())
      .toBe(expectedWarning)
  })

  it('invalidates a parameter suggestion as soon as a preference is edited', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-use-current-preferences"]').trigger('click')
    await wrapper.vm.$nextTick()

    expect(wrapper.find('[data-testid="fix-parameter-preferences-stale"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)
    expect(wrapper.find('select').exists()).toBe(true)
  })

  it('offers preferred ranges from parameter targets when no suggestion was found', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterWithoutSuggestionResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)
    const seedButton = wrapper.get('[data-testid="fix-use-current-preferences"]')
    expect(seedButton.attributes('disabled')).toBeUndefined()
    await seedButton.trigger('click')
    await wrapper.vm.$nextTick()
    expect(wrapper.find('select').exists()).toBe(true)
  })

  it('does not present an exhausted search budget as a complete no-result conclusion', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterBudgetExhaustedResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.text()).toContain('fixStrategyBudgetExhaustedTitle')
    expect(wrapper.text()).toContain('fixAttemptProgress')
    expect(wrapper.text()).not.toContain('noVerifiedFixSuggestion')
  })

  it('locks a parameter at its original value for the next search', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-lock-original"]').trigger('click')
    await wrapper.vm.$nextTick()

    const bounds = wrapper.findAll('input[type="number"]')
    expect(bounds).toHaveLength(2)
    expect((bounds[0].element as HTMLInputElement).value).toBe('70')
    expect((bounds[1].element as HTMLInputElement).value).toBe('70')
    expect(wrapper.find('[data-testid="fix-parameter-preferences-stale"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-apply-current"]').exists()).toBe(false)
  })

  it('explains that condition adjustment was tried without a verified proposal', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(conditionWithoutSuggestionResult())
    const wrapper = mountDialog()
    await flush()

    await wrapper.get('[data-testid="fix-strategy-condition"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.text()).toContain('conditionFixNoVerifiedSuggestion')
    expect(wrapper.text()).toContain('conditionFixNoVerifiedSuggestionDetail')
    expect(wrapper.text()).not.toContain('noFixSuggestionsForStrategy')
  })

  it('shows and applies a verified condition adjustment without destructive confirmation', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(conditionResult())
    boardApi.applyFix.mockResolvedValueOnce({
      applied: true,
      strategy: 'condition',
      verificationRechecked: true,
      verificationEvidenceReused: false,
      appliedSuggestion: conditionResult().suggestions[0],
      previousRuleCount: 1,
      currentRuleCount: 1,
      message: 'Added one guard.',
      rules: [{
        id: '21',
        name: 'When it is cold, heat the room',
        sources: [
          { fromId: 'temperature_1', fromApi: 'temperature', itemType: 'variable', relation: '<=', value: '18' },
          { fromId: 'occupancy_1', fromApi: 'occupied', itemType: 'variable', relation: '=', value: 'present' }
        ],
        toId: 'ac_1',
        toApi: 'heat'
      }]
    })
    const wrapper = mountDialog()
    await flush()

    await wrapper.get('[data-testid="fix-strategy-condition"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.vm.$nextTick()

    expect(wrapper.text()).toContain('addConditionAdjustment')
    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(elementPlus.confirm).not.toHaveBeenCalled()
    expect(boardApi.applyFix).toHaveBeenCalledWith(
      7,
      conditionResult().suggestions[0],
      undefined
    )
    expect(elementPlus.success).toHaveBeenCalledWith('fixAppliedWithRecheck')
    expect(wrapper.emitted('applied')?.[0]?.[0]).toMatchObject({
      strategy: 'condition',
      currentRuleCount: 1
    })
  })

  it('applies the exact verified parameter adjustment and authoritative rule snapshot', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    boardApi.applyFix.mockResolvedValueOnce({
      applied: true,
      strategy: 'parameter',
      verificationRechecked: false,
      verificationEvidenceReused: true,
      appliedSuggestion: parameterResult().suggestions[0],
      previousRuleCount: 1,
      currentRuleCount: 1,
      message: 'Changed one threshold.',
      rules: [{
        id: '31',
        name: 'Adjust the gas threshold',
        sources: [{ fromId: 'gas_1', fromApi: 'gas', itemType: 'variable', relation: '>', value: '85' }],
        toId: 'exit_1',
        toApi: 'unlock'
      }]
    })
    const wrapper = mountDialog()
    await flush()

    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()
    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(elementPlus.confirm).not.toHaveBeenCalled()
    expect(boardApi.applyFix).toHaveBeenCalledWith(
      7,
      parameterResult().suggestions[0],
      undefined
    )
    expect(elementPlus.success).toHaveBeenCalledWith('fixAppliedWithSignedEvidence')
    expect(wrapper.emitted('applied')?.[0]?.[0]).toMatchObject({
      strategy: 'parameter',
      currentRuleCount: 1
    })
  })

  it('requires confirmation before permanently removing rules', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(removeResult())
    boardApi.applyFix.mockResolvedValueOnce({
      applied: true,
      strategy: 'remove',
      verificationRechecked: false,
      verificationEvidenceReused: true,
      appliedSuggestion: removeResult().suggestions[0],
      previousRuleCount: 1,
      currentRuleCount: 0,
      message: 'Removed one rule.',
      rules: []
    })
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-strategy-remove"]').trigger('click')
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(elementPlus.confirm).toHaveBeenCalledOnce()
    expect(boardApi.applyFix).toHaveBeenCalledWith(
      7,
      removeResult().suggestions[0],
      undefined
    )
    expect(elementPlus.success).toHaveBeenCalledWith('fixAppliedWithSignedEvidence')
    expect(elementPlus.success).not.toHaveBeenCalledWith('Removed one rule.')
    expect(wrapper.emitted('applied')?.[0]?.[0]).toMatchObject({
      applied: true,
      strategy: 'remove',
      currentRuleCount: 0,
      rules: []
    })
  })

  it('does not expose an internal device reference when fix apply is rejected', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    boardApi.applyFix.mockRejectedValueOnce({
      response: {
        status: 400,
        data: {
          message: 'rules[0].conditions[0].deviceName: Unknown condition device: device_78da526b_8cb4'
        }
      }
    })
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(elementPlus.error).toHaveBeenCalledWith('fixDeviceReferenceUnavailable')
    expect(elementPlus.error).not.toHaveBeenCalledWith(expect.stringContaining('device_78da526b'))
    expect(wrapper.emitted('outcome-uncertain')).toBeUndefined()
    expect(wrapper.emitted('update:visible')).toBeUndefined()
  })

  it('keeps the dialog open for a definitive 503 preflight rejection', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    boardApi.applyFix.mockRejectedValueOnce({
      response: {
        status: 503,
        data: {
          message: 'Current template comparison is unavailable.',
          data: { reasonCode: 'FIX_APPLY_PREFLIGHT_UNAVAILABLE' }
        }
      }
    })
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(elementPlus.error).toHaveBeenCalledWith('Current template comparison is unavailable.')
    expect(wrapper.emitted('outcome-uncertain')).toBeUndefined()
    expect(wrapper.emitted('update:visible')).toBeUndefined()
  })

  it('treats an unclassified 503 as an uncertain mutation outcome', async () => {
    boardApi.fixTrace.mockResolvedValueOnce(parameterResult())
    boardApi.applyFix.mockRejectedValueOnce({
      response: { status: 503, data: { message: 'Upstream unavailable.' } }
    })
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    await wrapper.get('[data-testid="fix-apply-current"]').trigger('click')
    await flush()

    expect(wrapper.emitted('outcome-uncertain')).toHaveLength(1)
    expect(wrapper.emitted('update:visible')?.at(-1)).toEqual([false])
    expect(elementPlus.error).not.toHaveBeenCalled()
  })

  it('disables apply when the template snapshot has changed', async () => {
    boardApi.fixTrace.mockResolvedValueOnce({
      ...parameterResult(),
      templateSnapshotComparison: 'CHANGED'
    })
    const wrapper = mountDialog()
    await flush()
    await wrapper.get('[data-testid="fix-try-current"]').trigger('click')
    await flush()

    expect(wrapper.get('[data-testid="fix-apply-current"]').attributes('disabled')).toBeDefined()
    expect(wrapper.text()).toContain('fixTemplateSnapshotChangedLimitation')
  })
})
