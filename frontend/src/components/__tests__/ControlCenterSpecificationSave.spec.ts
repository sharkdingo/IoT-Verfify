// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, describe, expect, it, vi } from 'vitest'
import ControlCenter from '../ControlCenter.vue'

const messageMocks = vi.hoisted(() => ({
  success: vi.fn(),
  warning: vi.fn(),
  error: vi.fn()
}))

// A render-slot `ElTooltip` stub: `HintTooltip` imports it, and a whole-module mock otherwise
// hides it, failing every case at import time with a message that names the mock rather than
// the component needing it.
vi.mock('element-plus', () => ({
  ElMessage: messageMocks,
  ElTooltip: { name: 'ElTooltip', template: '<slot />' }
}))

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: { en: { app: {} } },
  missingWarn: false,
  fallbackWarn: false
})

afterEach(() => {
  document.body.innerHTML = ''
  vi.clearAllMocks()
})

describe('ControlCenter specification save', () => {
  it('locks the editor and detaches the submitted draft until completion', async () => {
    const wrapper = mount(ControlCenter, {
      attachTo: document.body,
      // The condition below references `device-1`, so the board must actually contain it: a
      // condition pointing at a device that is not on the canvas is legitimately refused.
      props: {
        activeSection: 'specs',
        nodes: [{ id: 'device-1', label: 'Device 1', templateName: 'Light' }] as any
      },
      global: { plugins: [i18n] }
    })
    const vm = wrapper.vm as any
    await wrapper.get('[data-testid="spec-template-select"]').setValue('1')
    vm.specForm.aConditions.push({
      id: 'condition-1',
      side: 'a',
      deviceId: 'device-1',
      deviceLabel: 'Device 1',
      targetType: 'state',
      key: 'state',
      relation: '=',
      value: 'on'
    })
    // The create button's disabled state is derived from the draft, so let it re-evaluate
    // before clicking.
    await wrapper.vm.$nextTick()
    await wrapper.get('[data-testid="spec-create"]').trigger('click')

    const emission = wrapper.emitted('add-spec')?.[0]?.[0] as any
    expect(emission).toBeTruthy()
    expect(wrapper.get('[data-testid="spec-editor-fieldset"]').attributes('disabled')).toBeDefined()
    expect(wrapper.get('[data-testid="spec-template-select"]').element.matches(':disabled')).toBe(true)

    vm.specForm.aConditions[0].value = 'off'
    expect(emission.aConditions[0].value).toBe('on')
    expect(emission.aConditions).not.toBe(vm.specForm.aConditions)

    emission.complete(true)
    await flushPromises()

    expect(wrapper.get('[data-testid="spec-editor-fieldset"]').attributes('disabled')).toBeUndefined()
    expect(wrapper.get<HTMLSelectElement>('[data-testid="spec-template-select"]').element.value).toBe('')
    wrapper.unmount()
  })

  it('refuses a draft whose condition names a device that is no longer on the board', async () => {
    // The device is deleted after the condition was saved. Without an inline block the button
    // stayed enabled, the backend refused the request, and the toast named no row.
    const wrapper = mount(ControlCenter, {
      attachTo: document.body,
      props: {
        activeSection: 'specs',
        nodes: [{ id: 'device-1', label: 'Device 1', templateName: 'Light' }] as any
      },
      global: { plugins: [i18n] }
    })
    const vm = wrapper.vm as any
    await wrapper.get('[data-testid="spec-template-select"]').setValue('1')
    vm.specForm.aConditions.push({
      id: 'condition-1',
      side: 'a',
      deviceId: 'device-1',
      deviceLabel: 'Device 1',
      targetType: 'state',
      key: 'state',
      relation: '=',
      value: 'on'
    })
    await wrapper.vm.$nextTick()
    expect(wrapper.get('[data-testid="spec-create"]').attributes('disabled')).toBeUndefined()

    // The device disappears (canvas delete, another tab, the assistant, or an undo).
    await wrapper.setProps({ nodes: [] as any })

    expect(wrapper.get('[data-testid="spec-create"]').attributes('disabled')).toBeDefined()
    expect(vm.specificationBlockedReason).toBe('app.specConditionDeviceMissing')
    // The offending row is marked, not silently rendered as an unnamed device.
    expect(vm.isSpecConditionDeviceMissing('device-1')).toBe(true)
    expect(vm.getDeviceLabel('device-1')).toBe('app.deletedModelItem')

    await wrapper.get('[data-testid="spec-create"]').trigger('click')
    expect(wrapper.emitted('add-spec')).toBeUndefined()
    wrapper.unmount()
  })

  /**
   * The chip beside the formula preview named the temporal logic, and it read "Model" for every
   * template: it looked for a `CTLSPEC`/`LTLSPEC` prefix that `buildSpecFormula` never writes, so it
   * contradicted the formula rendered immediately next to it in the one surface teaching that
   * distinction. Rendered rather than source-read, because the defect was in what reached the screen.
   */
  it('names the temporal logic of the selected template beside its formula', async () => {
    const wrapper = mount(ControlCenter, {
      attachTo: document.body,
      props: {
        activeSection: 'specs',
        nodes: [{ id: 'device-1', label: 'Device 1', templateName: 'Light' }] as any
      },
      global: { plugins: [i18n] }
    })

    // Template 1 (always, `AG(A)`) is CTL; template 6 (persistence, `G(IF -> F G(THEN))`) is the
    // only LTL one. Both are asserted so a constant would fail rather than half-pass.
    await wrapper.get('[data-testid="spec-template-select"]').setValue('1')
    await wrapper.vm.$nextTick()
    const chip = () => wrapper.get('[data-testid="spec-formula-kind"]').text()
    expect(chip()).toBe('CTL')
    // The formula printed next to it must agree — that contradiction was the visible symptom.
    expect((wrapper.vm as any).specForm.formula.startsWith('CTL ')).toBe(true)

    await wrapper.get('[data-testid="spec-template-select"]').setValue('6')
    await wrapper.vm.$nextTick()
    expect(chip()).toBe('LTL')
    expect((wrapper.vm as any).specForm.formula.startsWith('LTL ')).toBe(true)

    wrapper.unmount()
  })
})
