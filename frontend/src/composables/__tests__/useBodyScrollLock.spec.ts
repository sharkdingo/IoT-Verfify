// @vitest-environment jsdom
import { defineComponent, h, ref } from 'vue'
import { mount } from '@vue/test-utils'
import { afterEach, describe, expect, it } from 'vitest'

import { openModalDepth, useBodyScrollLock } from '../useBodyScrollLock'

const wrappers: Array<ReturnType<typeof mount>> = []

const mountLock = (initial: boolean) => {
  const locked = ref(initial)
  const wrapper = mount(defineComponent({
    setup() {
      useBodyScrollLock(locked)
      return () => h('div')
    }
  }))
  wrappers.push(wrapper)
  return { locked, wrapper }
}

afterEach(() => {
  wrappers.splice(0).forEach(wrapper => wrapper.unmount())
  document.body.style.overflow = ''
})

describe('useBodyScrollLock', () => {
  it('locks the page while open and restores the previous value on close', () => {
    document.body.style.overflow = 'auto'
    const { locked } = mountLock(true)
    expect(document.body.style.overflow).toBe('hidden')

    locked.value = false
    expect(document.body.style.overflow).toBe('auto')
  })

  it('keeps the lock until the last nested owner closes', async () => {
    const outer = mountLock(true)
    const inner = mountLock(true)
    expect(document.body.style.overflow).toBe('hidden')

    inner.locked.value = false
    expect(document.body.style.overflow).toBe('hidden')

    outer.locked.value = false
    expect(document.body.style.overflow).toBe('')
  })

  it('releases the lock when an open owner unmounts', () => {
    const { wrapper } = mountLock(true)
    expect(document.body.style.overflow).toBe('hidden')

    wrapper.unmount()
    expect(document.body.style.overflow).toBe('')
  })

  it('does not lock while closed', () => {
    mountLock(false)
    expect(document.body.style.overflow).toBe('')
  })

  it('reports how many modal surfaces are open', () => {
    // Board.vue's Ctrl+Z accelerator is on `window` and a modal's own buttons own no native undo, so
    // this count is what stops the keystroke mutating the board behind an open dialog.
    expect(openModalDepth.value).toBe(0)

    const outer = mountLock(true)
    expect(openModalDepth.value).toBe(1)

    const inner = mountLock(true)
    expect(openModalDepth.value).toBe(2)

    inner.locked.value = false
    expect(openModalDepth.value).toBe(1)

    outer.wrapper.unmount()
    expect(openModalDepth.value).toBe(0)
  })
})
