import { describe, expect, it } from 'vitest'
import { mount } from '@vue/test-utils'
import { nextTick } from 'vue'
import HintTooltip from '../HintTooltip.vue'

/**
 * A hint on a disabled control must still appear, because "why can't I press this?" is exactly when
 * the hint carries the most information.
 *
 * This is not hypothetical. The board's action dock used to reveal a hand-rolled `<span>` hint via
 * `.board-tool-wrapper:hover` -- the wrapper, which is never disabled -- so the hint worked in every
 * state. Moving the dock onto `HintTooltip` moves the trigger onto the button itself, and a native
 * `disabled` button dispatches no pointer events at all: `mouseenter` never fires, so a popper bound
 * to that element would stay closed in precisely the state that needs explaining. Several dock
 * buttons are disabled during playback, during a run, and while a recommendation is in flight.
 *
 * The test drives the DOM event rather than `trigger('mouseenter')` on the wrapper so it observes
 * what a real pointer would produce.
 */
describe('HintTooltip on a disabled trigger', () => {
  const mountWithButton = (disabled: boolean) => mount(HintTooltip, {
    props: { content: 'Close playback first', placement: 'left' },
    slots: { default: `<button type="button" ${disabled ? 'disabled' : ''}>Run history</button>` },
    attachTo: document.body
  })

  /**
   * Asserting on `document.body.textContent` is not enough: Element Plus renders the popper's text
   * into the DOM even while it is closed, so a `textContent` match passes with the tooltip hard
   * disabled. Read the popper element's visibility instead -- that is what distinguishes "shown"
   * from "present but never opened".
   */
  const openAndReadVisible = async (wrapper: ReturnType<typeof mountWithButton>) => {
    const button = wrapper.find('button').element
    // ElTooltip listens on its trigger; dispatch the real event a pointer would deliver.
    button.dispatchEvent(new MouseEvent('mouseenter', { bubbles: false }))
    button.dispatchEvent(new MouseEvent('mouseover', { bubbles: true }))
    await nextTick()
    await new Promise(resolve => setTimeout(resolve, 250))
    await nextTick()
    const popper = document.querySelector('.iot-info-tooltip-popper')
    if (!popper) return { open: false, text: '' }
    const hidden = popper.getAttribute('aria-hidden') === 'true'
      || (popper as HTMLElement).style.display === 'none'
    return { open: !hidden, text: popper.textContent ?? '' }
  }

  it('shows the hint when the trigger is enabled', async () => {
    const wrapper = mountWithButton(false)
    const shown = await openAndReadVisible(wrapper)
    wrapper.unmount()
    expect(shown.open, 'an enabled trigger must open its hint').toBe(true)
    expect(shown.text).toContain('Close playback first')
  })

  it('shows the hint when the trigger is disabled', async () => {
    const wrapper = mountWithButton(true)
    const shown = await openAndReadVisible(wrapper)
    wrapper.unmount()
    // If this reddens, a disabled dock button has no reachable explanation and the trigger must move
    // back onto an enabled wrapper around the button rather than the button itself.
    expect(shown.open, 'a disabled trigger must still open its hint').toBe(true)
    expect(shown.text).toContain('Close playback first')
  })
})
