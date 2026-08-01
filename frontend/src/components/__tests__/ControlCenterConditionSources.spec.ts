// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, describe, expect, it, vi } from 'vitest'
import ControlCenter from '../ControlCenter.vue'

vi.mock('element-plus', () => ({
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
