import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Reduced motion stops decoration. It must not stop the one animation that carries information.
 *
 * `.animate-spin` sat in the same `animation: none !important` list as the ping halos and shimmer, so a user
 * with `prefers-reduced-motion: reduce` saw every spinner frozen mid-rotation. A stopped spinner does not read
 * as "motion is disabled" — it reads as **stalled**, and NuSMV runs take real seconds, so the one thing a user
 * needs during a verification is confidence that it is still alive. Freezing that signal turns a healthy run
 * into an apparent hang, which is the repo's "never present an unknown as a settled outcome" rule pointing the
 * other way.
 *
 * Measured in a browser during a live verification: `1s linear` normally, `2.4s steps(8)` under reduce — still
 * infinite. A slow stepped rotation of a 16px glyph is not the fast, large-area, parallax motion the
 * preference exists to suppress.
 *
 * The probe that confirmed this was wrong twice first, and both failures produced a *zero* that looked like
 * success: an idle board animates nothing, and a fixed 1.5s wait let a small model finish before the
 * measurement. It now waits for a spinner to exist and says so when the run outpaces it.
 */

const boardCss = () => readFileSync(join(__dirname, '../board.css'), 'utf8')

describe('reduced motion', () => {
  /** The `@media (prefers-reduced-motion: reduce)` block that owns the animation overrides. */
  const motionBlock = () => {
    const css = boardCss()
    // The block containing the animate-* list, not merely the first reduced-motion block in the file.
    const marker = css.indexOf('.iot-board .animate-ping')
    expect(marker, 'the reduced-motion animation list should exist').toBeGreaterThan(-1)
    const start = css.lastIndexOf('@media (prefers-reduced-motion: reduce)', marker)
    expect(start, 'the animate-* list should sit inside a reduced-motion block').toBeGreaterThan(-1)
    /*
     * The block's own extent, by balancing braces — not "everything up to the next `@media`".
     *
     * That earlier heuristic ran **17,904 characters past** the block it meant to read (20,026 against a real
     * 2,122), so every assertion below was free to match a rule outside reduced-motion entirely. It passed only
     * because one `animation-duration` happened to fall inside the window; a rule deleted from the block and a
     * rule added anywhere in those 17.9k characters would look identical to it.
     */
    let depth = 0
    let cursor = css.indexOf('{', start)
    while (cursor < css.length) {
      if (css[cursor] === '{') depth += 1
      else if (css[cursor] === '}') {
        depth -= 1
        if (depth === 0) break
      }
      cursor += 1
    }
    expect(depth, 'the reduced-motion block should be closed').toBe(0)
    return css.slice(start, cursor + 1)
  }

  it('keeps a progress spinner turning, because a frozen one reports a stall that is not happening', () => {
    const block = motionBlock()

    // The spinner must not be in the kill list.
    const killList = block.slice(0, block.indexOf('animation: none'))
    expect(killList, '.animate-spin must not be silenced with the decorative animations')
      .not.toMatch(/\.animate-spin\b/)

    // And it must be given an explicit slowed duration, not merely left alone: leaving it untouched would keep
    // the full-speed 1s rotation, which is the thing the preference is asking to soften.
    const spinRule = block.slice(block.indexOf('.iot-board .animate-spin'))
    expect(spinRule, 'the spinner should be slowed rather than stopped').toMatch(/animation-duration:\s*[\d.]+s/)
    const duration = /animation-duration:\s*([\d.]+)s/.exec(spinRule)
    expect(Number(duration?.[1]), 'a slowed spinner should take longer than the default 1s')
      .toBeGreaterThanOrEqual(2)
  })

  it('still stops the animations that carry no information', () => {
    const block = motionBlock()
    // These exist to draw the eye and nothing else, so reduced motion removes them outright.
    for (const decorative of ['.animate-ping', '.animate-pulse', '.animate-pulse-glow', '.fade-in']) {
      expect(block, `${decorative} should be stopped under reduced motion`).toContain(decorative)
    }
    expect(block, 'the decorative list should be silenced').toMatch(/animation:\s*none\s*!important/)
  })
})
