import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Opening a replay must give the canvas back to the animation.
 *
 * Replay is the one moment where attention belongs on the canvas: the user is watching devices change state,
 * step by step, to understand why a property failed. Measured during a real counterexample replay, **five
 * surfaces held the canvas at once** — Control Center 320px left, System Inspector 320px right, trace timeline
 * below, change popover above, and the floating action dock over the middle:
 *
 * | | before | after |
 * | :--- | ---: | ---: |
 * | Clear canvas width | 800px (55.6% of viewport) | **1328px (92.2%)** |
 * | Panels cover, 1440x900 | 67.7% | **33.9%** |
 * | Panels cover, 1440x700 | **73.6%** | **40.6%** |
 *
 * Every panel was reasonable on its own, which is exactly how this accumulated — nobody added a fifth panel,
 * five features each added one. The fix is not decoration or removal: the two *authoring* panels collapse to
 * their rails, because during replay the Control Center creates devices and rules that are not in the frozen
 * scene, and the Inspector inspects the live board rather than the trace. What a replay reader needs is already
 * in the timeline (`trace-timeline-devices`, `trace-timeline-env`, `trace-step-values`).
 *
 * The timeline, popover and dock are deliberately untouched: the timeline *is* the replay control, the popover
 * explains the step being watched, and the dock is how the user leaves. Trading meaning for space would swap one
 * honesty problem for another.
 *
 * Pinned because the regression is silent. Adding a sixth panel, or a new replay entry point that forgets the
 * call, costs nothing at build time and shows up only as a slowly shrinking canvas.
 */

const boardVue = () => readFileSync(join(__dirname, '../Board.vue'), 'utf8')

describe('replay canvas focus', () => {
  const withoutComments = (text: string) =>
    text.replace(/<!--[\s\S]*?-->/g, '').replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '')

  it('collapses both authoring panels through one named owner', () => {
    const source = withoutComments(boardVue())
    // One function, so "what happens when a replay opens" has a single answer rather than two copies that can
    // drift apart.
    expect(source, 'a named owner for replay focus should exist')
      .toMatch(/const focusCanvasForReplay = \(\) => \{/)
    const body = source.slice(source.indexOf('const focusCanvasForReplay'))
      .slice(0, source.slice(source.indexOf('const focusCanvasForReplay')).indexOf('}') + 1)
    expect(body, 'the Control Center collapses').toMatch(/boardPanels\.control\.collapsed = true/)
    expect(body, 'the System Inspector collapses').toMatch(/boardPanels\.inspector\.collapsed = true/)
  })

  it('is called from every replay entry point, not just the one that prompted it', () => {
    const source = withoutComments(boardVue())
    // Counterexample replay and simulation playback are the same task — watch the canvas — so a focus rule that
    // holds for one and not the other is worse than none: the user would learn a behaviour that then betrays them.
    const calls = (source.match(/focusCanvasForReplay\(\)/g) || []).length
    // Two call sites: counterexample replay and simulation playback. The declaration is
    // `const focusCanvasForReplay = () => {`, which this pattern does not match.
    expect(calls, 'expected both replay entry points to call it').toBeGreaterThanOrEqual(2)

    const traceEntry = source.slice(source.indexOf('const openTraceAnimationAt'))
    expect(traceEntry.slice(0, 1400), 'counterexample replay focuses the canvas')
      .toMatch(/focusCanvasForReplay\(\)/)

    const simEntry = source.slice(source.indexOf('const openSimulationAnimationFromSavedStates'))
    expect(simEntry.slice(0, 1400), 'simulation playback focuses the canvas')
      .toMatch(/focusCanvasForReplay\(\)/)
  })

  it('collapses rather than unmounts, so nothing is hidden from the user or a screen reader', () => {
    const source = withoutComments(boardVue())
    const body = source.slice(source.indexOf('const focusCanvasForReplay'))
      .slice(0, source.slice(source.indexOf('const focusCanvasForReplay')).indexOf('}') + 1)
    // A `v-if`-style removal would take the panels out of the DOM and the accessibility tree, and would need a
    // second layout path. Collapsing reuses the mechanism narrow viewports already have: the rails stay on
    // screen at 64px/48px and reopen on one click.
    expect(body, 'replay focus must not unmount panels').not.toMatch(/= false\b/)
    expect(body, 'replay focus changes only the collapsed flags')
      .not.toMatch(/showControlCenter|showSystemInspector|\.visible\s*=/)
  })
})
