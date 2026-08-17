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

/** `min(<fraction>dvh, <n>rem)` → the dvh term, which is what binds on a short screen. */
const dvhFraction = (declaration: string): number => {
  const match = /min\(\s*([\d.]+)dvh\s*,/.exec(declaration)
  expect(match, `expected a min(dvh, rem) ceiling, got: ${declaration}`).not.toBeNull()
  return Number(match![1])
}

/**
 * The change popover's `max-height`, from the rule block a given comment anchors.
 *
 * Its own comment states the *combined* budget in prose — "34dvh + the timeline's 44dvh = 78dvh, leaving the
 * canvas a visible corridor" — which is the one property here that no single-cap assertion can see. It was
 * `46dvh` against `66dvh` once: **112dvh**, more than the whole screen, so the two overlays could meet before
 * either reached its rem ceiling.
 */
/**
 * The base change-popover rule, anchored on the comment that owns *its* cap.
 *
 * Not reachable from `baseBlock()`: that anchor sits at the timeline's comment, which is ~130 lines *after*
 * the base popover rule, so slicing from it skips the popover's base cap entirely and the first
 * `.board-playback-change-popover` it then finds is the narrow override. That made this guard read 36+44
 * for the "base" pair and stay green under a 50dvh mutation of the value it claimed to check — caught by
 * mutation, not by review.
 */
const basePopoverBlock = (): string => {
  const at = BOARD_CSS.indexOf('/* Capped so the two playback overlays cannot claim the viewport between them.')
  if (at === -1) {
    throw new Error(
      'the base change-popover cap and its combined-budget rationale are missing; update the anchor '
      + 'rather than deleting the case')
  }
  // Back up to the rule's opening brace: the comment sits *inside* the block, after `max-height`'s siblings
  // but before the declaration itself, so slicing forward from it still contains the `max-height`.
  return BOARD_CSS.slice(BOARD_CSS.lastIndexOf('.board-playback-change-popover {', at))
}

/**
 * The narrow/short block that overrides *both* overlays.
 *
 * Anchored on the popover's own override, because `narrowCapDeclaration()` above anchors on a comment that
 * sits ~30 lines further down: the two narrow overrides live in the same `@media` block but are found from
 * different landmarks, and reusing either anchor for both would read one overlay's cap twice.
 */
const narrowBlock = (): string => {
  const at = BOARD_CSS.indexOf('@media (max-width: 1023.98px), (max-height: 599.98px) {\n    .iot-board .board-playback-change-popover {')
  if (at === -1) {
    throw new Error(
      'the narrow/short override of the change popover is missing, or no longer opens its media block; '
      + 'update the anchor rather than deleting the case')
  }
  return BOARD_CSS.slice(at)
}

const popoverMaxHeight = (block: string): string => {
  const rule = /\.board-playback-change-popover \{([^}]*)\}/.exec(block)
  if (!rule) throw new Error('no .board-playback-change-popover rule in this block')
  const match = /max-height:\s*([^;]+);/.exec(rule[1])
  if (!match) throw new Error('the .board-playback-change-popover rule declares no max-height')
  return match[1].trim()
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

  it('leaves the canvas a corridor when both playback overlays are open at once', () => {
    /*
     * The two overlays are capped independently but share one screen, and each cap is honest on its own —
     * the pair is what can go wrong. `board.css` states this budget in prose beside the popover cap; prose
     * does not fail, so a later pass raising one term would keep reading as correct.
     *
     * The popover is top-anchored under the nav and the timeline is bottom-anchored, so they approach each
     * other as their `dvh` terms grow. The rem terms bind on a tall screen and cannot collide there; the
     * `dvh` terms are the ones that scale with the viewport, which makes their sum the real constraint.
     *
     * 85% rather than 100%: at exactly 100 the two boxes touch, and "the canvas is the subject, the overlays
     * are apparatus" is the rule the caps exist to express — a 15dvh corridor is the weakest form of that
     * still worth calling a corridor. Both current pairs pass with room (78 and 76).
     */
    const CORRIDOR_BUDGET_DVH = 85
    for (const [name, popover, timeline] of [
      ['base', popoverMaxHeight(basePopoverBlock()), timelineMaxHeight(baseBlock())],
      ['narrow/short', popoverMaxHeight(narrowBlock()), narrowCapDeclaration()]
    ] as const) {
      const combined = dvhFraction(popover) + dvhFraction(timeline)
      expect(
        combined,
        `the ${name} playback overlays claim ${combined}dvh between them (popover ${popover}, timeline `
        + `${timeline}); the canvas needs a corridor at a short viewport, where the dvh terms bind`
      ).toBeLessThanOrEqual(CORRIDOR_BUDGET_DVH)
    }
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
