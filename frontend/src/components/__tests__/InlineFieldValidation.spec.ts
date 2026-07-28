// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { i18n } from '@/assets/i18n'
import ControlCenter from '../ControlCenter.vue'
import * as feedback from '@/utils/feedback'

/**
 * Field-level validation belongs next to the field, never in a toast — a toast fades before
 * the user has finished fixing the input, and it duplicates what the form already shows.
 * Rule: docs/guides/frontend-ui-conventions.md
 */

beforeEach(() => {
  i18n.global.locale.value = 'en'
  vi.restoreAllMocks()
})

afterEach(() => {
  document.body.innerHTML = ''
})

const mountControlCenter = (props: Record<string, unknown> = {}) => mount(ControlCenter, {
  attachTo: document.body,
  props,
  global: { plugins: [i18n] }
})

describe('device creation validation', () => {
  it('reports a duplicate name inline and keeps submit disabled instead of toasting', async () => {
    const blocked = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
    const wrapper = mountControlCenter({
      activeSection: 'devices',
      nodes: [{ id: 'n1', label: 'Lamp', templateName: 'Light', x: 0, y: 0 }]
    })

    const name = wrapper.get('[data-testid="single-device-name"]')
    await name.setValue('Lamp')

    const inlineError = wrapper.get('[data-testid="single-device-name-conflict"]')
    expect(inlineError.attributes('role')).toBe('alert')
    // The input points at its own error, so assistive tech reads them together.
    expect(name.attributes('aria-invalid')).toBe('true')
    expect(name.attributes('aria-describedby')).toBe(inlineError.attributes('id'))

    const submit = wrapper.get('[data-testid="single-device-create"]')
    expect(submit.attributes('disabled')).toBeDefined()

    await submit.trigger('click')
    expect(blocked).not.toHaveBeenCalled()

    wrapper.unmount()
  })

  it('keeps submit disabled for an empty name without announcing anything', async () => {
    const blocked = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
    const wrapper = mountControlCenter({ activeSection: 'devices' })

    const submit = wrapper.get('[data-testid="single-device-create"]')
    expect(submit.attributes('disabled')).toBeDefined()
    await submit.trigger('click')
    expect(blocked).not.toHaveBeenCalled()

    wrapper.unmount()
  })
})

describe('specification condition validation', () => {
  it('names the blocking reason inline and never enables submit without one', async () => {
    const blocked = vi.spyOn(feedback, 'notifyBlocked').mockImplementation(() => undefined)
    const wrapper = mountControlCenter({
      activeSection: 'specs',
      nodes: [],
      deviceTemplates: []
    })

    const templateSelect = wrapper.get('[data-testid="spec-template-select"]')
    const option = templateSelect.findAll('option').find(o => Boolean(o.attributes('value')))
    expect(option).toBeDefined()
    await templateSelect.setValue(option!.attributes('value'))
    await wrapper.get('[data-testid="spec-add-condition-a"]').trigger('click')

    const reason = wrapper.get('[data-testid="spec-condition-blocked-reason"]')
    expect(reason.text().length).toBeGreaterThan(0)

    const save = wrapper.get('[data-testid="spec-condition-save"]')
    expect(save.attributes('disabled')).toBeDefined()
    // The button explains itself rather than relying on a toast the user must catch.
    expect(save.attributes('aria-describedby')).toBe(reason.attributes('id'))

    await save.trigger('click')
    expect(blocked).not.toHaveBeenCalled()

    wrapper.unmount()
  })
})
