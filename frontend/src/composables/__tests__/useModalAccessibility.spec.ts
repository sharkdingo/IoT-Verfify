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
})
