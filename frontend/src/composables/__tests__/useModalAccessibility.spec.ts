import { defineComponent, h, nextTick, ref, type VNode } from 'vue'
import { mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import { useModalAccessibility } from '../useModalAccessibility'

const mountedWrappers: Array<ReturnType<typeof mount>> = []

afterEach(() => {
  mountedWrappers.splice(0).forEach(wrapper => wrapper.unmount())
  document.body.innerHTML = ''
  vi.restoreAllMocks()
})

beforeEach(() => {
  vi.spyOn(HTMLElement.prototype, 'getClientRects').mockImplementation(function (this: HTMLElement) {
    return [this.getBoundingClientRect()] as unknown as DOMRectList
  })
})

const mountPanel = (
  trapFocus: boolean,
  shouldRestoreFocus?: () => boolean,
  renderControls?: () => VNode[],
  fallbackTarget?: HTMLElement
) => {
  const opener = document.createElement('button')
  opener.textContent = 'Open'
  document.body.append(opener)
  opener.focus()

  const Panel = defineComponent({
    setup() {
      const open = ref(true)
      const close = () => { open.value = false }
      const { setDialogRef, handleModalKeydown } = useModalAccessibility(
        open,
        close,
        () => fallbackTarget ?? opener,
        { trapFocus, shouldRestoreFocus }
      )
      return () => open.value
        ? h('section', {
            ref: setDialogRef,
            tabindex: -1,
            onKeydown: handleModalKeydown
          }, renderControls?.() ?? [
            h('button', { 'data-testid': 'first' }, 'First'),
            h('button', { 'data-testid': 'last' }, 'Last')
          ])
        : null
    }
  })

  const wrapper = mount(Panel, { attachTo: document.body })
  mountedWrappers.push(wrapper)
  return { opener, wrapper }
}

describe('useModalAccessibility', () => {
  it('focuses and restores a non-modal panel without trapping Tab', async () => {
    const { opener, wrapper } = mountPanel(false)
    await nextTick()
    expect(document.activeElement).toBe(wrapper.get('[data-testid="first"]').element)

    ;(wrapper.get('[data-testid="last"]').element as HTMLElement).focus()
    const tab = new KeyboardEvent('keydown', { key: 'Tab', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(tab)
    expect(tab.defaultPrevented).toBe(false)

    const escape = new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(escape)
    await nextTick()
    expect(wrapper.find('section').exists()).toBe(false)
    expect(document.activeElement).toBe(opener)
  })

  it('keeps the existing modal focus trap enabled by default behavior', async () => {
    const { wrapper } = mountPanel(true)
    await nextTick()
    const last = wrapper.get('[data-testid="last"]')
    ;(last.element as HTMLElement).focus()
    const tab = new KeyboardEvent('keydown', { key: 'Tab', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(tab)
    expect(tab.defaultPrevented).toBe(true)
    expect(document.activeElement).toBe(wrapper.get('[data-testid="first"]').element)
  })

  it('skips hidden, inert, and closed-details controls for initial focus', async () => {
    const { wrapper } = mountPanel(true, undefined, () => [
      h('button', { hidden: true, 'data-testid': 'hidden-first' }, 'Hidden'),
      h('div', { inert: '', 'data-testid': 'inert-region' }, [
        h('button', { 'data-testid': 'inert-button' }, 'Inert')
      ]),
      h('details', {}, [
        h('summary', { tabindex: -1 }, 'Closed'),
        h('button', { 'data-testid': 'closed-details-button' }, 'Closed content')
      ]),
      h('button', { 'data-testid': 'visible-first' }, 'Visible')
    ])

    await nextTick()

    expect(document.activeElement).toBe(wrapper.get('[data-testid="visible-first"]').element)
  })

  it('wraps from the last visible control when later controls are hidden', async () => {
    const { wrapper } = mountPanel(true, undefined, () => [
      h('button', { 'data-testid': 'visible-first' }, 'First'),
      h('button', { 'data-testid': 'visible-last' }, 'Last'),
      h('button', { style: 'display: none', 'data-testid': 'hidden-last' }, 'Hidden'),
      h('div', { inert: '' }, [h('button', { 'data-testid': 'inert-last' }, 'Inert')])
    ])
    await nextTick()
    const visibleLast = wrapper.get('[data-testid="visible-last"]')
    ;(visibleLast.element as HTMLElement).focus()

    const tab = new KeyboardEvent('keydown', { key: 'Tab', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(tab)

    expect(tab.defaultPrevented).toBe(true)
    expect(document.activeElement).toBe(wrapper.get('[data-testid="visible-first"]').element)
  })

  it('does not steal focus back while another related panel is taking over', async () => {
    const { opener, wrapper } = mountPanel(false, () => false)
    await nextTick()
    const escape = new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(escape)
    await nextTick()

    expect(wrapper.find('section').exists()).toBe(false)
    expect(document.activeElement).not.toBe(opener)
  })

  it('falls back when the original opener becomes hidden while the panel is open', async () => {
    const fallback = document.createElement('button')
    fallback.textContent = 'Fallback'
    document.body.append(fallback)
    const { opener, wrapper } = mountPanel(false, undefined, undefined, fallback)
    await nextTick()
    opener.hidden = true

    const escape = new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true })
    wrapper.get('section').element.dispatchEvent(escape)
    await nextTick()

    expect(document.activeElement).toBe(fallback)
  })

  it('closes a trapping modal on Escape even before focus has reached it', async () => {
    // The element-bound handler only sees the key once focus is inside the dialog, and focus moves
    // there in a nextTick after a post-flush watcher. A deep link that opens the surface on load —
    // or a fast user — presses Escape inside that window, and the keystroke used to be dropped
    // silently, leaving the dialog open with no indication why.
    const { wrapper } = mountPanel(true)
    // Deliberately no `await nextTick()`: focus is still outside the dialog here.
    document.body.focus()

    document.dispatchEvent(
      new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true }))
    await nextTick()

    expect(wrapper.find('section').exists()).toBe(false)
  })

  it('leaves Escape to a non-modal panel rather than closing it from the document', async () => {
    // The board's floating tool panels are non-modal on purpose and own their own Escape behaviour;
    // one keypress must not close all of them.
    const { wrapper } = mountPanel(false)
    document.body.focus()

    document.dispatchEvent(
      new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true }))
    await nextTick()

    expect(wrapper.find('section').exists()).toBe(true)
  })
})
