// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import ControlCenter from '../ControlCenter.vue'
import SystemInspector from '../SystemInspector.vue'

vi.mock('element-plus', async () => {
  const actual = await vi.importActual<typeof import('element-plus')>('element-plus')
  return {
    ...actual,
    ElMessage: Object.assign(vi.fn(), { success: vi.fn(), warning: vi.fn(), error: vi.fn() })
  }
})

beforeEach(() => {
  i18n.global.locale.value = 'en'
})

afterEach(() => {
  document.body.innerHTML = ''
})

const SECTIONS = ['templates', 'devices', 'rules', 'specs'] as const

describe('board side panel tab semantics', () => {
  it('exposes the control center sections as a single-selection tablist', () => {
    const wrapper = mount(ControlCenter, {
      attachTo: document.body,
      props: { activeSection: 'templates' },
      global: { plugins: [i18n] }
    })

    const tablist = wrapper.get('[role="tablist"]')
    const tabs = tablist.findAll('[role="tab"]')
    expect(tabs).toHaveLength(SECTIONS.length)
    expect(tabs.filter(tab => tab.attributes('aria-selected') === 'true')).toHaveLength(1)

    const selected = tabs.find(tab => tab.attributes('aria-selected') === 'true')!
    expect(selected.attributes('id')).toBe('control-tab-templates')
    // Roving tabindex: only the selected tab is reachable with Tab.
    expect(tabs.filter(tab => tab.attributes('tabindex') === '0')).toHaveLength(1)

    const panel = wrapper.get(`#${selected.attributes('aria-controls')}`)
    expect(panel.attributes('role')).toBe('tabpanel')
    expect(panel.attributes('aria-labelledby')).toBe('control-tab-templates')

    wrapper.unmount()
  })

  it('moves control center selection with the arrow keys', async () => {
    const wrapper = mount(ControlCenter, {
      attachTo: document.body,
      global: { plugins: [i18n] }
    })

    await wrapper.get('#control-tab-templates').trigger('keydown', { key: 'ArrowRight' })
    expect(wrapper.get('#control-tab-devices').attributes('aria-selected')).toBe('true')
    expect(wrapper.emitted('update:active-section')?.at(-1)).toEqual(['devices'])

    await wrapper.get('#control-tab-devices').trigger('keydown', { key: 'End' })
    expect(wrapper.get('#control-tab-specs').attributes('aria-selected')).toBe('true')

    await wrapper.get('#control-tab-specs').trigger('keydown', { key: 'ArrowRight' })
    expect(wrapper.get('#control-tab-templates').attributes('aria-selected')).toBe('true')

    wrapper.unmount()
  })

  it('gives the system inspector the same tablist contract', async () => {
    const wrapper = mount(SystemInspector, {
      attachTo: document.body,
      global: { plugins: [i18n] }
    })

    const tabs = wrapper.get('[role="tablist"]').findAll('[role="tab"]')
    expect(tabs.filter(tab => tab.attributes('aria-selected') === 'true')).toHaveLength(1)
    expect(tabs.filter(tab => tab.attributes('tabindex') === '0')).toHaveLength(1)

    await wrapper.get('#inspector-tab-devices').trigger('keydown', { key: 'ArrowRight' })
    expect(wrapper.get('#inspector-tab-rules').attributes('aria-selected')).toBe('true')

    wrapper.unmount()
  })
})
