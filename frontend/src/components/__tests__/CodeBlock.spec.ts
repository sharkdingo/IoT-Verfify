// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { h } from 'vue'
import { beforeEach, describe, expect, it, vi } from 'vitest'
import CodeBlock from '../CodeBlock.vue'
import { i18n } from '@/assets/i18n'

describe('CodeBlock copy control', () => {
  beforeEach(() => {
    i18n.global.locale.value = 'en'
  })

  it('announces a successful copy', async () => {
    const writeText = vi.fn().mockResolvedValue(undefined)
    Object.defineProperty(navigator, 'clipboard', {
      configurable: true,
      value: { writeText }
    })
    const wrapper = mount(CodeBlock, {
      props: { highlightVnode: h('pre', 'const answer = 42'), language: 'ts' },
      global: { plugins: [i18n] }
    })

    await wrapper.get('button[aria-label="Copy"]').trigger('click')
    await flushPromises()

    expect(writeText).toHaveBeenCalledWith('const answer = 42')
    expect(wrapper.text()).toContain('Copied')
  })

  it('shows a recoverable state when clipboard access fails', async () => {
    Object.defineProperty(navigator, 'clipboard', {
      configurable: true,
      value: { writeText: vi.fn().mockRejectedValue(new Error('denied')) }
    })
    const wrapper = mount(CodeBlock, {
      props: { highlightVnode: h('pre', 'example'), language: 'text' },
      global: { plugins: [i18n] }
    })

    await wrapper.get('button[aria-label="Copy"]').trigger('click')
    await flushPromises()

    expect(wrapper.text()).toContain('Copy failed')
  })
})
