import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The playback overlay's height ceilings must bracket its content, in both directions.
 *
 * There are two caps: a base `max-height: min(44dvh, 26rem)` and a narrow/short override
 * `min(40dvh, 22rem)`. Both have been wrong, in opposite ways, and each time the symptom was a scrollbar or a
 * takeover rather than anything a type checker or a unit test would notice:
 *
 * - **Too large.** The narrow ceiling was once `22rem` against a wide `20rem`, so a tablet rendered a *taller*
 *   overlay than a desktop — the smaller screen giving the apparatus more of itself, which inverts the priority
 *   the whole rule exists to express.
 * - **Too small.** It was then lowered to `18rem` (288px) on the premise that a full-width overlay "holds more
 *   per row and needs less height". That premise inverted when the base width went from 39rem to 72rem: the wide
 *   panel became 1152px and the narrow full-width one 991px, so the narrow case is now the *narrower* of the two.
 *   Measured content is a constant **317px** at every width from 900 to 1600 — it does not re-fold — so the 288px
 *   ceiling clipped 31px and the overlay scrolled at exactly `< 1024px`, a discontinuous step with identical
 *   `scrollHeight` either side of it.
 *
 * So the invariant has a floor and a lid, and this file pins both. The floor is the measured content height, held
 * as a constant here rather than remeasured, because the point is to fail when a *ceiling* moves below it — a
 * change in content is a separate question that the E2E measurement answers.
 */

const BOARD_CSS = readFileSync(join(__dirname, '../board.css'), 'utf8')

/**
 * The tallest the overlay's content has been measured at, across every viewport from 900x1400 to 2556x1413.
 *
 * Deliberately a literal. Deriving it from the markup would make this test agree with whatever the markup
 * currently is, which is exactly the failure mode it exists to catch.
 */
const MEASURED_CONTENT_PX = 317

/** `min(<fraction>dvh, <n>rem)` → the rem term in pixels, which is what binds on a tall screen. */
const remCeiling = (declaration: string): number => {
  const match = /min\(\s*[\d.]+dvh\s*,\s*([\d.]+)rem\s*\)/.exec(declaration)
  expect(match, `expected a min(dvh, rem) ceiling, got: ${declaration}`).not.toBeNull()
  return Number(match![1]) * 16
}

/**
 * The `max-height` declared for `.board-timeline` inside a given rule block.
 *
 * Anchors on a `.board-timeline {` rule that actually carries a `max-height`, not on the first one it finds.
 * There are three `.board-timeline` rules in this stylesheet and the earliest — `.iot-board .board-timeline` at
 * line 733 — declares no height at all, so a naive `indexOf` matched it, found no `max-height`, and threw during
 * collection. The whole file then reported "no tests", which is the vacuous-guard shape in its purest form: a
 * green-looking run that executed nothing.
 */
const timelineMaxHeight = (block: string): string => {
  for (const rule of block.matchAll(/\.board-timeline \{([^}]*)\}/g)) {
    const match = /max-height:\s*([^;]+);/.exec(rule[1])
    if (match) return match[1].trim()
  }
  throw new Error('no .board-timeline rule in this block declares a max-height')
}

/**
 * The narrow/short override of the timeline cap.
 *
 * Anchored on the rule's own comment, not on the media query. **Six** blocks in this stylesheet open with
 * `@media (max-width: 1023.98px), (max-height: 599.98px)`, and an `indexOf` on that string found the first —
 * a 169-character block with no `.board-timeline` in it at all. The guard then read the *base* cap for both
 * values and passed every mutation of the narrow one.
 */
const narrowCapDeclaration = (): string => {
  const at = BOARD_CSS.indexOf('The ceiling then went to `18rem`')
  if (at === -1) throw new Error('the narrow timeline cap and its rationale are missing')
  return timelineMaxHeight(BOARD_CSS.slice(at))
}

/** The base rule, found from the comment that owns it. */
const baseBlock = (): string => {
  const at = BOARD_CSS.indexOf('/* The playback overlay is apparatus')
  if (at === -1) throw new Error('the base playback overlay rule is missing')
  return BOARD_CSS.slice(at)
}

describe('playback overlay height ceilings', () => {
  it('gives both caps room for the content the overlay actually holds', () => {
    for (const [name, cap] of [
      ['base', timelineMaxHeight(baseBlock())],
      ['narrow/short', narrowCapDeclaration()]
    ] as const) {
      expect(remCeiling(cap), `the ${name} ceiling must clear the measured ${MEASURED_CONTENT_PX}px of content`)
        .toBeGreaterThanOrEqual(MEASURED_CONTENT_PX)
    }
  })

  it('never lets the narrow ceiling exceed the base one', () => {
    // The other direction: a smaller screen must not hand the apparatus more of itself than a large screen does.
    expect(remCeiling(narrowCapDeclaration()), 'the narrow ceiling should not exceed the base')
      .toBeLessThanOrEqual(remCeiling(timelineMaxHeight(baseBlock())))
  })

  it('keeps a viewport fraction on both, so a short screen still clamps below the ceiling', () => {
    /*
     * The `dvh` term protects a short viewport, where a rem ceiling alone would take most of the screen. A
     * 667px-tall phone gets 40dvh = 267px rather than the 352px ceiling, which is the intended trade.
     */
    for (const [name, cap] of [
      ['base', timelineMaxHeight(baseBlock())],
      ['narrow/short', narrowCapDeclaration()]
    ] as const) {
      expect(cap, `the ${name} cap should clamp by viewport height as well as by rem`).toMatch(/[\d.]+dvh/)
    }
  })
})
