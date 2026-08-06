import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Every enabled button on the board shows a pointer cursor, from one rule.
 *
 * Tailwind's preflight resets `button { cursor: default }`, so only components that explicitly opt in get a pointer.
 * Measured on a real board: **77 of 182 enabled buttons rendered `cursor: default`** — including the entire Control
 * Center tab strip and the panel collapse toggles.
 *
 * Every one of them had hover feedback, so none was undiscoverable. What was wrong is subtler and still worth fixing:
 * the cursor contradicted the appearance. For a pointer user the cursor is the fastest signal that something is
 * clickable, and on a canvas tool that matters more than on a page — a reader assumes most of the surface is inert, so
 * the affordance has to be unambiguous.
 *
 * The fix is one rule in `board.css` rather than 77 component edits, because per-component opt-in is exactly what
 * missed 77 buttons. `:not(:disabled)` is the load-bearing part: a disabled control must keep `default`, or the cursor
 * promises an interaction that will not happen.
 *
 * Also verified in the same pass, and left alone: **zero** inert elements carry `cursor: pointer`. A click that does
 * nothing is indistinguishable from a failed operation, and nothing in the board makes that promise.
 */

const boardCss = () => readFileSync(join(__dirname, '../board.css'), 'utf8')

describe('button cursor affordance', () => {
  it('sets a pointer cursor for enabled board buttons in one place', () => {
    const css = boardCss()
    // The rule must exist and must be scoped to the board, not global — the landing page has its own styling.
    expect(css, 'a board-wide button cursor rule should exist')
      .toMatch(/\.iot-board button:not\(:disabled\)/)
    const at = css.indexOf('.iot-board button:not(:disabled)')
    const block = css.slice(at, at + 220)
    expect(block, 'the rule should set a pointer cursor').toMatch(/cursor:\s*pointer/)
  })

  it('excludes disabled controls, so the cursor never promises a dead interaction', () => {
    const css = boardCss()
    const at = css.indexOf('.iot-board button:not(:disabled)')
    expect(at, 'the rule should exist before checking its selector').toBeGreaterThan(-1)
    const selector = css.slice(at, css.indexOf('{', at))
    // Dropping `:not(:disabled)` is the tempting simplification, and it would give every greyed-out control a pointer.
    expect(selector, 'the selector must exclude disabled buttons').toMatch(/:not\(:disabled\)/)
    // The same care for ARIA-disabled role buttons, which have no `:disabled` state to match.
    expect(selector, 'role=button elements should exclude the aria-disabled case')
      .toMatch(/aria-disabled/)
  })

  it('does not hand a pointer cursor to non-interactive text', () => {
    // The inverse failure. A `cursor: pointer` on a bare span or paragraph invites a click that does nothing — and in
    // a verification tool a silent no-op is indistinguishable from a failed operation. Measured live: 0 such elements.
    // This rule keeps a blanket `* { cursor: pointer }`-style shortcut from ever being introduced.
    const css = boardCss()
    const offenders: string[] = []
    /*
     * The element selector may be scoped, and here it always is.
     *
     * The first version anchored on a bare element at the start of a line. `board.css` is board-scoped, so every
     * selector begins `.iot-board …` and that pattern could not match by construction — the check was
     * structurally incapable of failing, and the comment above recording "0 such elements" was measuring its own
     * blind spot. Verified by injecting `.iot-board p { cursor: pointer }`: the old form passed it, this one
     * reports it.
     *
     * Matching the selector's *last* simple component catches both `p {` and `.iot-board p {` while still
     * ignoring `.iot-board .some-button {`, which is a control and may legitimately have the cursor.
     */
    for (const rule of css.matchAll(/([^{}]+)\{([^}]*)\}/g)) {
      const [, selector, body] = rule
      if (!/cursor:\s*pointer/.test(body)) continue
      const hitsBareElement = selector
        .split(',')
        .map(part => part.trim().split(/[\s>+~]+/).pop() ?? '')
        .some(last => /^(\*|span|p|div|h[1-6]|li|td)$/.test(last))
      if (hitsBareElement) offenders.push(`board.css: ${selector.trim().slice(0, 70)}`)
    }
    expect(offenders, 'a pointer cursor on a bare text element promises an interaction that does not exist')
      .toEqual([])
  })
})
