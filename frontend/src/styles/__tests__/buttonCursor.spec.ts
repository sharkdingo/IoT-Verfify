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
    css.split('\n').forEach((line, index) => {
      // A pointer cursor applied through a universal or bare-element selector, rather than to a control.
      if (/^\s*(\*|span|p|div|h[1-6])\s*\{/.test(line)) {
        const block = css.slice(css.indexOf(line), css.indexOf(line) + 200)
        if (/cursor:\s*pointer/.test(block)) offenders.push(`board.css:${index + 1}`)
      }
    })
    expect(offenders, 'a pointer cursor on a bare text element promises an interaction that does not exist')
      .toEqual([])
  })
})
