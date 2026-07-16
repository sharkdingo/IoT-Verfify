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
  warnings: []
})

const parameterResult = (): FixResult => ({
  ...removeResult(),
  suggestions: [{
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
    verified: true
  }],
  strategyAttempts: [{
    strategy: 'parameter',
    status: 'VERIFIED',
    reason: 'Passed forward verification.'
  }]
})

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
    expect(elementPlus.success).toHaveBeenCalledWith('fixAppliedSuccessfully')
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
})
