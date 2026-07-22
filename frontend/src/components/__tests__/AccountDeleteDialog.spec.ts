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

describe('AccountDeleteDialog', () => {
  it('does not enable permanent deletion from autofilled values or navigation keys', async () => {
    const wrapper = mountDialog()
    const confirmation = wrapper.get('input[name="delete-account-confirmation"]')
    const password = wrapper.get('input[type="password"]')

    await confirmation.setValue('alice')
    await password.setValue('Password123')

    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeDefined()

    await confirmation.trigger('keydown', { key: 'Tab' })
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeDefined()

    await confirmation.trigger('keydown', { key: 'e' })
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeDefined()

    await confirmation.setValue('alice')
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeUndefined()
  })

  it('treats deletion and IME composition as deliberate text editing', async () => {
    const wrapper = mountDialog()
    const confirmation = wrapper.get('input[name="delete-account-confirmation"]')
    const password = wrapper.get('input[type="password"]')

    await confirmation.setValue('alice')
    await password.setValue('Password123')
    await confirmation.trigger('keydown', { key: 'ArrowLeft' })
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeDefined()

    await confirmation.trigger('compositionstart')
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeDefined()

    await confirmation.setValue('alice')
    expect(wrapper.get('button[type="submit"]').attributes('disabled')).toBeUndefined()
  })

  it('emits the normalized confirmation after deliberate editing', async () => {
    const wrapper = mountDialog()
    const confirmation = wrapper.get('input[name="delete-account-confirmation"]')
    await confirmation.trigger('paste')
    await confirmation.setValue('  alice  ')
    await wrapper.get('input[type="password"]').setValue('Password123')

    await wrapper.get('form').trigger('submit')

    expect(wrapper.emitted('confirm')).toEqual([[
      { password: 'Password123', confirmation: 'alice' }
    ]])
  })
})
