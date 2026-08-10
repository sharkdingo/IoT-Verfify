// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, describe, expect, it, vi } from 'vitest'
import ControlCenter from '../ControlCenter.vue'

vi.mock('element-plus', () => ({
  /*
   * `HintTooltip` imports `ElTooltip`, and a whole-module mock hides it — every case in the file then fails at
   * import time with "No 'ElTooltip' export is defined", a message that names the mock rather than the component
   * needing it. A render-slot stub suffices: nothing here asserts tooltip behaviour, only the control it wraps.
   */
  ElTooltip: { name: 'ElTooltip', template: '<slot />' },
  ElMessage: { success: vi.fn(), warning: vi.fn(), error: vi.fn() }
}))

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: { en: { app: {} } },
  missingWarn: false,
  fallbackWarn: false
})

// One shared value the device only affects (Reads=false), one it reads. The generator emits a
// `device.name := a_name` mirror only for the second, so only the second is a value this device
// can be said to observe.
const template = {
  id: 1,
  name: 'Light',
  manifest: {
    Name: 'Light',
    Modes: ['Power'],
    InitState: 'on',
    ImpactedVariables: ['illuminance'],
    InternalVariables: [
      {
        Name: 'illuminance',
        IsInside: false,
        Reads: false,
        FalsifiableWhenCompromised: false,
        LowerBound: 0,
        UpperBound: 100,
        NaturalChangeRate: '0',
        Trust: 'trusted',
        Privacy: 'public'
      },
      {
        Name: 'lux',
        IsInside: false,
        Reads: true,
        FalsifiableWhenCompromised: true,
        LowerBound: 0,
        UpperBound: 100,
        NaturalChangeRate: '0',
        Trust: 'trusted',
        Privacy: 'public'
      },
      {
        Name: 'bulbHours',
        IsInside: true,
        FalsifiableWhenCompromised: false,
        LowerBound: 0,
        UpperBound: 9,
        Trust: 'trusted',
        Privacy: 'public'
      }
    ],
    WorkingStates: [{ Name: 'on', Trust: 'trusted', Privacy: 'public', Dynamics: [] }]
  }
} as any

afterEach(() => {
  document.body.innerHTML = ''
  vi.clearAllMocks()
})

describe('specification condition sources honour read capability', () => {
  const mountControlCenter = () => mount(ControlCenter, {
    attachTo: document.body,
    props: {
      activeSection: 'specs',
      nodes: [{ id: 'light_1', label: 'Light 1', templateName: 'Light' }] as any,
      deviceTemplates: [template]
    },
    global: { plugins: [i18n] }
  })

  it('does not offer an affect-only shared value as a condition source', () => {
    const vm = mountControlCenter().vm as any
    const offered = vm.getAvailableKeys('light_1', 'variable').map((key: any) => key.value)

    // A condition on an affect-only value would compare something this device never observes, and
    // the backend refuses it at persist time and again before generation. Offering it here would
    // only let the user build a specification that gets rejected later.
    expect(offered).not.toContain('illuminance')
    expect(offered).toContain('lux')
    expect(offered).toContain('bulbHours')
  })
})

describe('specification variable conditions must say which value they mean', () => {
  const mountControlCenter = () => mount(ControlCenter, {
    attachTo: document.body,
    props: {
      activeSection: 'specs',
      nodes: [{ id: 'light_1', label: 'Light 1', templateName: 'Light' }] as any,
      deviceTemplates: [template]
    },
    global: { plugins: [i18n] }
  })

  const draftVariableCondition = (key: string) => {
    const vm = mountControlCenter().vm as any
    Object.assign(vm.editingConditionData, {
      deviceId: 'light_1',
      targetType: 'variable',
      key,
      relation: '=',
      value: '5'
    })
    return vm
  }

  it('offers both questions for a shared value, with neither preselected', async () => {
    const vm = draftVariableCondition('lux')
    await vm.$nextTick()

    // Presenting either as the author's intent is the defect being fixed: the two answers differ
    // exactly when the device is compromised, which is the case the specification exists to catch.
    expect(vm.editingConditionVariableSourceOptions.map((option: any) => option.value))
      .toEqual(['environment', 'reported'])
    expect(vm.editingConditionData.variableSource).toBeUndefined()
    expect(vm.specConditionBlockedReason).toBe('app.specVariableSourceRequired')

    vm.editingConditionData.variableSource = 'reported'
    await vm.$nextTick()
    expect(vm.specConditionBlockedReason).toBeNull()
  })

  it('offers only the device reading for a device-local value, and chooses it', async () => {
    const vm = draftVariableCondition('bulbHours')
    await vm.$nextTick()

    // A device-local value has no counterpart in the home, so there is nothing to choose between
    // and the backend refuses the environment reading outright.
    expect(vm.editingConditionVariableSourceOptions.map((option: any) => option.value))
      .toEqual(['reported'])
    expect(vm.editingConditionData.variableSource).toBe('reported')
    expect(vm.specConditionBlockedReason).toBeNull()
  })

  it('clears a stale choice when no reading can answer it any more', async () => {
    /*
     * Driven through a transition that leaves NO options, because that is the only one that reaches the
     * clear branch. Switching to a device-local key instead returns at the auto-fill arm one line earlier,
     * so an earlier version of this test passed with the clear branch deleted entirely — it was asserting
     * the auto-fill its neighbour above already covers.
     */
    const vm = draftVariableCondition('lux')
    await vm.$nextTick()
    vm.editingConditionData.variableSource = 'environment'
    await vm.$nextTick()
    expect(vm.editingConditionVariableSourceOptions.length).toBeGreaterThan(1)

    vm.editingConditionData.targetType = 'state'
    await vm.$nextTick()

    // A non-variable condition has no reading to choose, so a carried-over `environment` would be sent
    // as a field the backend rejects on that target type.
    expect(vm.editingConditionVariableSourceOptions).toEqual([])
    expect(vm.editingConditionData.variableSource).toBeUndefined()
  })

  it('labels which question a saved condition asks, and marks one that never chose', () => {
    const vm = mountControlCenter().vm as any
    const condition = (variableSource?: string) => ({
      deviceId: 'light_1', targetType: 'variable', key: 'lux', variableSource
    })

    expect(vm.formatConditionVariableSourceLabel(condition('environment')))
      .toBe('app.specVariableSourceEnvironmentShort')
    expect(vm.formatConditionVariableSourceLabel(condition('reported')))
      .toBe('app.specVariableSourceReportedShort')
    expect(vm.formatConditionVariableSourceLabel(condition()))
      .toBe('app.specVariableSourceUnresolvedShort')
    // No badge on a condition type the question does not apply to.
    expect(vm.formatConditionVariableSourceLabel({
      deviceId: 'light_1', targetType: 'state', key: 'state'
    })).toBeNull()
  })
})
