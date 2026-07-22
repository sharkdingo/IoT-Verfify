import { flushPromises, mount } from '@vue/test-utils'
import { beforeAll, describe, expect, it } from 'vitest'

import ChatMarkdown from '@/components/ChatMarkdown.vue'

describe('ChatMarkdown security', () => {
  beforeAll(() => {
    Object.defineProperty(window, 'matchMedia', {
      configurable: true,
      value: () => ({
        matches: false,
        addEventListener: () => undefined,
        removeEventListener: () => undefined
      })
    })
  })

  it('does not render executable links or raw HTML', async () => {
    const wrapper = mount(ChatMarkdown, {
      props: {
        source: '[unsafe](javascript:alert(document.domain))\n\n<img src=x onerror=alert(1)>'
      }
    })
    await flushPromises()

    const link = wrapper.get('a')
    expect(link.attributes('href')).toBeUndefined()
    expect(wrapper.find('img').exists()).toBe(false)
    expect(wrapper.html()).not.toContain('onerror')
  })

  it('blocks automatic remote images and hardens external links', async () => {
    const wrapper = mount(ChatMarkdown, {
      props: {
        source: '[docs](https://example.com/docs)\n\n![diagram](https://tracker.example/pixel)'
      }
    })
    await flushPromises()

    expect(wrapper.get('a').attributes()).toMatchObject({
      href: 'https://example.com/docs',
      target: '_blank',
      referrerpolicy: 'no-referrer'
    })
    expect(wrapper.find('img').exists()).toBe(false)
    expect(wrapper.text()).toContain('diagram')
  })
})
