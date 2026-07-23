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

vi.mock('element-plus', () => ({ ElMessage: messageMocks }))

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
      props: { activeSection: 'specs' },
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
})
