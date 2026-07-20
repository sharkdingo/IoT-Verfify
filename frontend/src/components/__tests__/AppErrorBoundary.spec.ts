// @vitest-environment jsdom
import { defineComponent, h, nextTick, ref } from 'vue'
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, describe, expect, it, vi } from 'vitest'
import AppErrorBoundary from '../AppErrorBoundary.vue'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        viewErrorTitle: 'View failed',
        viewErrorDescription: 'The view could not be rendered.',
        retry: 'Retry',
        reloadPage: 'Reload page'
      }
    }
  },
  missingWarn: false,
  fallbackWarn: false
})

describe('AppErrorBoundary', () => {
  afterEach(() => vi.restoreAllMocks())

  it('contains a descendant render error and can recover after retry', async () => {
    const shouldThrow = ref(true)
    const BrokenView = defineComponent({
      setup: () => () => shouldThrow.value
        ? (() => { throw new Error('render failure') })()
        : h('p', { 'data-testid': 'recovered' }, 'Recovered')
    })
    vi.spyOn(console, 'error').mockImplementation(() => undefined)

    const wrapper = mount(AppErrorBoundary, {
      global: { plugins: [i18n] },
      slots: { default: () => h(BrokenView) }
    })

    await nextTick()
    expect(wrapper.get('[role="alert"]').text()).toContain('View failed')

    shouldThrow.value = false
    await wrapper.get('button').trigger('click')
    await nextTick()

    expect(wrapper.get('[data-testid="recovered"]').text()).toBe('Recovered')
  })
})
