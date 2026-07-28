// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { describe, expect, it } from 'vitest'

import { i18n } from '@/assets/i18n'
import AccountDeleteDialog from '../AccountDeleteDialog.vue'

const mountDialog = () => mount(AccountDeleteDialog, {
  props: {
    visible: true,
    username: 'alice',
    phone: '13800138000',
    loading: false
  },
  global: {
    plugins: [i18n],
    stubs: { Teleport: true }
  }
})

const confirmationField = 'input[name="delete-account-confirmation"]'

/**
 * Edits the field the way a real user does: an `InputEvent` carrying an `inputType`. Programmatic
 * autofill assigns `.value` and fires a plain `Event` with no `inputType`, which `setValue`
 * reproduces — so the two cases stay distinguishable here rather than assumed equivalent.
 */
const typeInto = async (element: Element, value: string) => {
  (element as HTMLInputElement).value = value
  element.dispatchEvent(new InputEvent('input', { inputType: 'insertText', bubbles: true }))
  await Promise.resolve()
}

describe('AccountDeleteDialog confirmation gate', () => {
  it('refuses a confirmation the user did not enter', async () => {
    const wrapper = mountDialog()
    // `setValue` fires a plain `input` Event with no `inputType`, as autofill does.
    await wrapper.get(confirmationField).setValue('alice')
    await wrapper.get('input[type="password"]').setValue('Password123')

    expect(wrapper.get('button.danger').attributes('disabled')).toBe('')
    wrapper.unmount()
  })

  it('accepts text the user typed, including on keyboards that report no printable key', async () => {
    const wrapper = mountDialog()
    // Android soft keyboards report `key` as `Unidentified`, and dropped text fires no keydown at
    // all; both still produce an InputEvent. Gating on printable keys disabled the button forever.
    await typeInto(wrapper.get(confirmationField).element, 'alice')
    await wrapper.get('input[type="password"]').setValue('Password123')

    expect(wrapper.get('button.danger').attributes('disabled')).toBeUndefined()
    wrapper.unmount()
  })

  it('normalizes the confirmation it emits', async () => {
    const wrapper = mountDialog()
    await typeInto(wrapper.get(confirmationField).element, '  alice  ')
    await wrapper.get('input[type="password"]').setValue('Password123')

    await wrapper.get('form').trigger('submit')

    expect(wrapper.emitted('confirm')).toEqual([[
      { password: 'Password123', confirmation: 'alice' }
    ]])
    wrapper.unmount()
  })
})
