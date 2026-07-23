// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { afterEach, describe, expect, it } from 'vitest'

import { i18n } from '@/assets/i18n'
import ControlCenter from '../ControlCenter.vue'
import RuleBuilderDialog from '../RuleBuilderDialog.vue'

afterEach(() => {
  i18n.global.locale.value = 'en'
  document.body.innerHTML = ''
})

describe('board modal surfaces', () => {
  it('keeps the rule builder above the fixed board navigation', () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes: [], deviceTemplates: [] },
      global: { plugins: [i18n] }
    })

    expect(wrapper.classes()).toContain('z-[2400]')
    expect(wrapper.get('[role="dialog"]').attributes('aria-modal')).toBe('true')
    wrapper.unmount()
  })

  it('keeps the specification condition actions reachable in short viewports', async () => {
    const wrapper = mount(ControlCenter, {
      props: { activeSection: 'specs', nodes: [], deviceTemplates: [] },
      global: { plugins: [i18n] }
    })

    const templateSelect = wrapper.get('[data-testid="spec-template-select"]')
    const templateOption = templateSelect.findAll('option')
      .find(option => Boolean(option.attributes('value')))
    expect(templateOption).toBeDefined()
    await templateSelect.setValue(templateOption!.attributes('value'))
    await wrapper.get('[data-testid="spec-add-condition-a"]').trigger('click')

    const overlay = wrapper.get('[data-testid="spec-condition-dialog"]')
    const dialog = overlay.get('[role="dialog"]')
    expect(overlay.classes()).toContain('z-[2400]')
    expect(dialog.classes()).toContain('control-center-dialog-surface')
    expect(dialog.classes()).toContain('control-center-spec-dialog')
    expect(dialog.get('.control-center-dialog-body').classes()).toContain('overflow-y-auto')
    expect(dialog.get('.control-center-dialog-footer').classes()).toContain('shrink-0')
    wrapper.unmount()
  })
})
