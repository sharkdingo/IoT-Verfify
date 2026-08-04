import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A device node must be able to show its own values.
 *
 * The counterexample replay surface was reported five times, by independent vision reviews, as one where "the
 * causal story lives almost entirely in the panels" — and measurement found why. On a default 184×135 node:
 *
 * | Element | Shown / needed | Lost |
 * | :--- | :--- | ---: |
 * | `device-state-value` "No state machine" | 2px / 85px | **98%** |
 * | The changed value `26` | 6px / 15px | 60% |
 * | Neighbouring node's `0` | 2px / 16px | 88% |
 *
 * The value a counterexample exists to show rendered in **six pixels**. The overlay was not stealing
 * attention; it was the only place the information existed.
 *
 * Two inverted `clamp()` bounds caused it, and both are the sort of defect that no rendering test and no
 * screenshot review catches directly — the text is *present*, just 2px wide. These checks pin the shape of the
 * fix instead.
 */

const boardCss = () => readFileSync(join(__dirname, '../board.css'), 'utf8')

describe('canvas node legibility', () => {
  it('never lets the icon column outgrow the text beside it', () => {
    // The icon column's upper bound was `clamp(4.5rem, 42cqmin, 52rem)`. A `clamp()` *lower* bound on a
    // maximum guarantees the decoration its size while the content absorbs every shortfall: 4.5rem (72px)
    // beat the 42cqmin term on any node up to ~171px, so the icon took 72px of a 132px content row and the
    // column holding label, state and chips resolved to 26px.
    const columns = boardCss().match(/grid-template-columns:\s*minmax\(clamp\([^)]*\),\s*clamp\(([\d.]+)rem[^)]*\)\)/)
    expect(columns, 'the node grid should declare an icon column with a clamped maximum').not.toBeNull()

    // The icon's guaranteed floor must stay small enough that a default node keeps most of its row for text.
    // 132px content row minus a 2rem (32px) icon leaves 100px; at 4.5rem it left 60px before gaps.
    expect(Number(columns![1])).toBeLessThanOrEqual(2)
  })

  it('shrinks a runtime chip\'s label before its value', () => {
    // Both were equally shrinkable, so a 65px chip holding "Temperature" (58px) and "26" (15px) split the
    // shortfall and printed the value in 6px. The label names the variable; the value is the fact.
    const css = boardCss()
    // The rules are `.iot-board`-scoped, so match the full selector rather than the bare class — my first
    // version sliced on the unprefixed name, found nothing, and failed against correct CSS.
    const ruleBody = (selector: string) => {
      const at = css.indexOf(`${selector} {`)
      expect(at, `${selector} should exist`).toBeGreaterThan(-1)
      return css.slice(at, at + css.slice(at).indexOf('}'))
    }
    const label = ruleBody('.iot-board .device-runtime-chip__label')
    const value = ruleBody('.iot-board .device-runtime-chip__value')

    // The label may shrink; the value may not.
    expect(label).toMatch(/flex:\s*0\s+1\s+auto/)
    expect(value).toMatch(/flex:\s*0\s+0\s+auto/)
    // And the label keeps a floor, so it still identifies itself by prefix rather than vanishing.
    expect(label).toMatch(/min-width:\s*[\d.]+rem/)
  })

  it('lets the runtime chips wrap into the node\'s spare height', () => {
    // The strip was a single non-wrapping row while the node had 29–32px of unused vertical space, so its
    // chips compressed each other instead of using it.
    const css = boardCss()
    const strip = css.slice(css.indexOf('.iot-board .device-runtime-strip {'))
    expect(strip.slice(0, strip.indexOf('}'))).toMatch(/flex-wrap:\s*wrap/)
  })

  // No rule here for the third defect of this pass — three node sizes declared as
  // `clamp(<sub-floor>, N cqmin, <huge ceiling>)`, where `cqmin` is a percentage of a 110-137px node and so
  // evaluated to 4.7-6.9px: always below the floor, which therefore *was* the rendered size (a flat 9.28px and
  // 10px at every viewport). That belongs to `typographyFloor.spec.ts`, whose container-relative exemption was
  // the hole that let it through and is now removed.
  //
  // I first wrote the check here as "an unreachable ceiling is misleading", and it immediately failed on
  // `clamp(0.72rem, 8cqmin, 8rem)` — whose ceiling is equally unreachable but whose floor is 11.52px, so the
  // text is legible whichever bound wins. The ceiling was never the harm; a *sub-floor floor that renders* is,
  // and one rule in one place already says that.

  it('gives a node provenance pill room for its own label', () => {
    // The pill states whether the shown sources are trusted. It printed the full sentence ("Shown sources
    // trusted") inside a 54px box, so it was ellipsized to a fragment — at any font size. The node now prints
    // the category and keeps the sentence in `title` plus an `sr-only` span, which is how the same node already
    // handles `noStateMachineShort`; that only works while the cap is wide enough for the short word, and the
    // previous `46cqmin` (63px on a 137px node) cut 28% off "Trusted".
    const css = boardCss()
    const at = css.indexOf('.iot-board .device-node-trust {')
    expect(at, '.device-node-trust should exist').toBeGreaterThan(-1)
    const rule = css.slice(at, at + css.slice(at).indexOf('}'))
    expect(rule).not.toMatch(/max-width:\s*[\d.]+cq/)
    expect(rule).toMatch(/max-width:\s*min\(100%,\s*[\d.]+rem\)/)
  })
})
