import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * The action dock has two groups with different consequences: run actions drive the verifier,
 * suggestions only propose edits. Every button used to be an opaque saturated fill in its own hue,
 * so eight of them read as eight primary actions and an empty Board offered no focal point --
 * measured in a browser as 8 of 8 dock buttons carrying primary weight.
 *
 * These tests pin the resulting hierarchy at the source. They are text assertions over the
 * component and stylesheet rather than a mounted render, because Board.vue is far too large to
 * mount cheaply and the property in question is which visual treatment each button is given.
 */
describe('board action dock hierarchy', () => {
  const root = join(process.cwd(), 'src')
  const board = readFileSync(join(root, 'views/Board.vue'), 'utf8')
  const css = readFileSync(join(root, 'styles/board.css'), 'utf8')

  const SUGGESTION_TOOLS = [
    'open-scenario-recommendations',
    'open-rule-recommendations',
    'open-device-recommendations',
    'open-spec-recommendations'
  ]

  // Run History is deliberately not here: it reads a stored result rather than running one, so it
  // has its own group. It keeps the filled treatment because reading a verdict is a primary task.
  const RUN_TOOLS = [
    'open-simulation-panel',
    'open-verification-panel',
    'open-fuzzing-panel',
    'open-history-panel'
  ]

  /**
   * The complete opening tag of one dock button.
   *
   * Scans forward for the tag-closing `>` while ignoring any `>` inside an attribute value, since
   * these bindings contain expressions like `count > 0`. Attribute order varies between buttons, so
   * nothing here assumes the test id comes before the class.
   */
  const buttonMarkup = (testId: string): string => {
    // Search inside the template only. The script block references these same test ids in
    // focus-restoration selectors, and matching one of those would read the wrong region entirely.
    const templateAt = board.indexOf('<template>')
    expect(templateAt, 'Board.vue should have a template block').toBeGreaterThan(-1)
    const at = board.indexOf(`data-testid="${testId}"`, templateAt)
    expect(at, `${testId} should exist in the dock markup`).toBeGreaterThan(-1)
    const start = board.lastIndexOf('<button', at)
    expect(start, `${testId} should sit inside a <button>`).toBeGreaterThan(-1)
    let quote: string | null = null
    for (let i = start; i < board.length; i++) {
      const ch = board[i]
      if (quote) {
        if (ch === quote) quote = null
      } else if (ch === '"' || ch === "'") {
        quote = ch
      } else if (ch === '>') {
        return board.slice(start, i + 1)
      }
    }
    throw new Error(`unterminated <button> for ${testId}`)
  }

  it('gives every suggestion tool the quieter secondary treatment', () => {
    for (const id of SUGGESTION_TOOLS) {
      expect(buttonMarkup(id), `${id} should use the shared secondary treatment`)
        .toContain('board-tool-button--suggestion')
    }
  })

  it('keeps run actions above the suggestion tier', () => {
    // If a run action were demoted to a suggestion, the dock would have no primary action at all, which is
    // the opposite failure: a user could not tell what the Board is for.
    for (const id of RUN_TOOLS) {
      expect(buttonMarkup(id), `${id} must not be demoted to a suggestion`)
        .not.toContain('board-tool-button--suggestion')
    }
  })

  it('separates a formal proof from candidate evidence and from a view', () => {
    // The sharper version of the rule above, and it was needed: the four run-group buttons rendered
    // **byte-identical** — same `rgb(37, 99, 235)` fill, 400 weight, 124x44 box, 10.4px radius, same shadow —
    // while doing three different things. "Keep run actions primary" was satisfied by that, because it only
    // forbade demotion to the suggestion tier and said nothing about the differences *inside* the group.
    //
    // Verification is the only control whose output is a formal conclusion. Simulation produces one concrete
    // trace and Explore produces bounded candidate evidence, which `CLAUDE.md` requires never be dressed as a
    // verdict — painting them exactly like the verifier is that overclaim in the visual layer. Run History
    // writes nothing at all.
    expect(buttonMarkup('open-verification-panel'), 'verification returns a proof and stays the filled primary')
      .toContain('board-tool-button--primary')

    for (const id of ['open-simulation-panel', 'open-fuzzing-panel']) {
      const markup = buttonMarkup(id)
      expect(markup, `${id} produces candidate evidence, not a verdict, so it is the evidence tier`)
        .toContain('board-tool-button--evidence')
      expect(markup, `${id} must not carry the verifier's filled treatment`)
        .not.toContain('board-tool-button--primary')
    }

    expect(buttonMarkup('open-history-panel'), 'run history opens a view and writes nothing')
      .toContain('board-tool-button--view')

    // Each tier must actually be defined, or a typo silently yields an unstyled button.
    for (const tier of ['--primary', '--evidence', '--view']) {
      expect(css, `board-tool-button${tier} should be defined`).toContain(`.board-tool-button${tier}`)
    }
  })

  it('gives every quiet tier a visible boundary', () => {
    // A demoted tier is still a control, and its edge has to be findable. Both quiet tiers have a surface
    // barely distinguishable from the panel behind the dock — 1.22:1 for `--evidence`, 1.10 for `--view` — so
    // the border alone carries the boundary and has to clear the 3:1 minimum by itself.
    //
    // Two independent design reviews, one per theme, both called Run History "too quiet" and "easy to miss".
    // That reads like taste until it is measured: its border was **1.48:1**. The reviews were describing a
    // real boundary failure, so the fix is a value rather than an opinion — and a later edit that softens
    // either border back toward the panel would reintroduce it invisibly.
    for (const tier of ['--evidence', '--view']) {
      const at = css.indexOf(`.iot-board .board-tool-button${tier} {`)
      expect(at, `board-tool-button${tier} should exist`).toBeGreaterThan(-1)
      const rule = css.slice(at, at + css.slice(at).indexOf('}'))
      expect(rule, `${tier} needs an explicit border to carry its boundary`).toMatch(/border:\s*1px solid/)
      // A low percentage blends into the panel: 42% measured 1.87:1. 80% is the floor that clears 3:1.
      const mix = /border:\s*1px solid color-mix\(in srgb, var\(--accent\) (\d+)%/.exec(rule)
      if (mix) {
        expect(Number(mix[1]), `${tier} border at ${mix[1]}% accent is too close to the panel`)
          .toBeGreaterThanOrEqual(80)
      }
    }
  })

  it('marks an open panel with more than colour in every tier', () => {
    // A tinted tier is a weaker signal than a fill, so its pressed state has to work harder — and the
    // pressed state is how a user knows which panel is currently covering the canvas.
    for (const tier of ['--evidence', '--view']) {
      const rule = css.slice(css.indexOf(`.iot-board .board-tool-button${tier}[aria-pressed='true']`))
      expect(rule.slice(0, rule.indexOf('}')), `${tier} pressed state needs a non-colour cue`)
        .toMatch(/box-shadow:\s*inset/)
    }
  })

  it('does not give a suggestion tool a saturated fill', () => {
    // A saturated fill is what made all eight compete. Catching the utility class directly means a
    // future edit cannot reintroduce the competition one button at a time.
    for (const id of SUGGESTION_TOOLS) {
      expect(buttonMarkup(id), `${id} should not carry a saturated background`)
        .not.toMatch(/bg-(teal|amber|purple|red|indigo|green|cyan|blue)-[5-9]00/)
    }
  })

  it('states each suggestion category with its own accent so colour coding survives', () => {
    // Demoting the fill must not erase the category cue: the icon keeps the hue the fill used to
    // carry, otherwise four identical grey buttons become harder to tell apart, not easier.
    const accents = ['--iot-tool-scenario', '--iot-tool-rule', '--iot-tool-device', '--iot-tool-spec']
    for (const accent of accents) {
      expect(board, `${accent} should be applied to a dock button`).toContain(accent)
      expect(css, `${accent} should be defined for the light theme`).toContain(`${accent}:`)
    }
    // And a dark-theme override, since the light-theme hues lose contrast on a dark surface.
    const darkBlock = css.slice(css.indexOf('.dark .iot-board {'))
    for (const accent of accents) {
      expect(darkBlock, `${accent} needs a dark-theme value`).toContain(`${accent}:`)
    }
  })

  it('signals the active suggestion panel without relying on colour alone', () => {
    // Someone who cannot distinguish the accent hue still needs to see which panel is open.
    const rule = css.slice(css.indexOf(".board-tool-button--suggestion[aria-pressed='true']"))
      .slice(0, 400)
    expect(rule).toContain('box-shadow')
  })

  it('keeps the suggestion fill neutral so the accent border stays identifiable', () => {
    // Reviewing the rendered screenshot -- not the CSS -- showed the first version of this treatment
    // nearly vanished in the light theme: a hairline border measured 1.23:1 against the fill, below
    // the 3:1 minimum for identifying a UI component. Tinting the fill with the same accent did not
    // fix it, because darkening the border darkened the fill in step (purple measured *down*, from
    // 2.99:1 to 2.39:1). A neutral fill decouples the two and measures 5.02-8.72:1 in light and
    // 9.38-12.30:1 in dark. So the fill must not be mixed with the accent.
    const block = css.slice(
      css.indexOf('.iot-board .board-tool-button--suggestion {'),
      css.indexOf('.iot-board .board-tool-button--suggestion:hover')
    )
    expect(block, 'the suggestion button needs a background').toMatch(/background-color:/)
    expect(block, 'tinting the fill with the accent dilutes the border contrast')
      .not.toMatch(/background-color:[^;]*--board-tool-accent/)
    expect(block, 'the border carries the button shape, so it uses the full accent')
      .toMatch(/border:[^;]*--board-tool-accent/)
  })

  it('keeps every suggestion tool a real focusable button with a name', () => {
    // This is a demotion in emphasis, not disclosure: the tools stay keyboard reachable and named.
    for (const id of SUGGESTION_TOOLS) {
      const markup = buttonMarkup(id)
      expect(markup, `${id} should be a <button>`).toContain('<button')
      expect(markup, `${id} needs an accessible name`).toContain('aria-label')
      expect(markup, `${id} should report its panel state`).toContain('aria-pressed')
    }
  })

  it('groups Run History apart from the actions that start a run', () => {
    // Two independent visual reviews raised the same point unprompted: Run History reads a stored
    // result rather than producing one, so grouping it under "Run" mislabels what it does.
    const template = board.slice(board.indexOf('<template>'))
    const runGroupAt = template.indexOf('data-testid="run-tool-group"')
    const reviewGroupAt = template.indexOf('data-testid="review-tool-group"')
    const historyAt = template.indexOf('data-testid="open-history-panel"')
    expect(reviewGroupAt, 'Run History needs its own group').toBeGreaterThan(-1)
    expect(historyAt, 'the history button should live after the review group opens')
      .toBeGreaterThan(reviewGroupAt)
    expect(reviewGroupAt, 'the review group should come after the run group')
      .toBeGreaterThan(runGroupAt)
  })

  it('uses a rail label short enough not to truncate', () => {
    // "Counterexample Search" rendered as "Counterex..." in a rail that allows about 70px. A
    // truncated *action name* is the one label a user cannot recover from surrounding context, so
    // the rail uses a short form while the full name stays on the panel and the accessible name.
    expect(buttonMarkup('open-fuzzing-panel'), 'the rail should not print the long name')
      .not.toContain("t('app.fuzzSearch')")
    expect(board, 'the rail needs a dedicated short label').toContain("t('app.fuzzSearchShort')")
  })

  it('shows the values for the selected counterexample step without an extra click', () => {
    // The device states, triggered rules and environment values answer "what changed and why".
    // Collapsed, a 14-state trace showed a step number and a violated property but no values -- for
    // a counterexample whose whole point is a value climbing to the forbidden number.
    // Renamed from `trace-timeline-state-details`, which shared a prefix with the per-step buttons
    // (`trace-timeline-state-{i}`) and so was matched by selectors meant to find steps.
    for (const testId of ['trace-step-values']) {
      const at = board.indexOf(`data-testid="${testId}"`)
      expect(at, `${testId} should exist`).toBeGreaterThan(-1)
      const tagStart = board.lastIndexOf('<details', at)
      expect(board.slice(tagStart, at), `${testId} should be open by default`).toContain(' open')
    }
  })

  it('derives every dock mode decision from one list of available modes', () => {
    // Which modes a viewport allows was written four times in four shapes: two hardcoded cycle arrays
    // selected by `>= 1280`, a clamp restating the same threshold, a restore handler re-deriving the
    // same answer, and a `>= 1280` ternary inline in the launcher's `aria-label`. They agreed only by
    // coincidence, so a new width rule had to be remembered in three other places.
    expect(board).toContain('const availableActionDockModes = computed<ActionDockMode[]>')

    // The threshold appears once, in that list. The 720px fallback is a separate documented rule and
    // lives in `actionDockMode`, which is why it is excluded rather than counted here.
    const railWidthThresholds = board.match(/actionDockViewportWidth\.value\s*[<>]=?\s*1280/g) ?? []
    expect(railWidthThresholds, 'the 1280px rail threshold should have one owner').toHaveLength(1)

    // The launcher names the mode it restores instead of re-deriving it from a width.
    expect(board).toContain(':aria-label="actionDockRestoreLabel"')
    expect(board).not.toMatch(/:aria-label="actionDockViewportWidth >= 1280/)
  })

  it('names the set of workflow panels once', () => {
    // `showCanvasEmptyState` spelled out the five members and also re-listed the four recommendation flags
    // that `isAnyRecommendationPanelVisible()` owns, so a sixth panel meant remembering two lists. Only the
    // E2E suite covers the empty state, so a unit-level mutation of that predicate was silent; this is not.
    expect(board).toContain('const isWorkflowPanelOpen = computed(')
    const listings = board.match(/showVerificationPanel\.value \|\|\s*\n\s*showSimulationPanel\.value/g) ?? []
    expect(listings, 'the workflow-panel set should be enumerated once').toHaveLength(1)

    const at = board.indexOf('const showCanvasEmptyState = computed(')
    expect(at, 'showCanvasEmptyState should exist').toBeGreaterThan(-1)
    const body = board.slice(at, at + board.slice(at).indexOf('\n)'))
    expect(body, 'it should read the shared predicate').toContain('isWorkflowPanelOpen.value')
    expect(body, 'it should not re-list the recommendation panels').not.toContain('showDeviceRecommendationPanel')
  })

  it('keeps the canvas map and its viewport controls visible together', () => {
    /*
     * The map card had a `v-show` hiding it whenever any of eleven surfaces was open, which also removed the
     * zoom field, the zoom buttons and fit-to-content — the board's only pointer viewport controls.
     *
     * Narrowing that to hide only the map rectangle (and renaming the card's heading while it was hidden) was
     * treating a symptom. Measured, the collision it guarded against cannot occur: the floating panels carry a
     * `right` inset clearing the inspector and the action rail, so at 1440x900 a panel spans x=660..948
     * against an inspector at 1120..1440, and at 1100x800 it is 336..692 against 780..1100. The map lives
     * inside that inspector. At narrow widths the inspector is a 56px rail and the map is not rendered.
     */
    /*
     * The slice must span the WHOLE tag, not `<div` up to the testid.
     *
     * The first version ended the slice at the testid, so it only ever examined `'<div\n          '` — pure
     * whitespace — and a `v-show` written after the testid (the natural place, and where the original one was)
     * was invisible to it. Mutation-verified blind: re-adding `v-show="!isWorkflowPanelOpen"` right after either
     * testid left the spec green. Both halves of the check were fiction.
     */
    const openingTag = (testId: string): string => {
      const at = board.indexOf(`data-testid="${testId}"`)
      expect(at, `${testId} should exist`).toBeGreaterThan(-1)
      const start = board.lastIndexOf('<div', at)
      const end = board.indexOf('>', at)
      expect(end, `${testId}'s tag should be closed`).toBeGreaterThan(start)
      return board.slice(start, end)
    }

    expect(openingTag('canvas-map'), 'the map card should not be conditionally hidden')
      .not.toMatch(/v-(show|if)=/)
    expect(openingTag('canvas-map-viewport'), 'the map viewport should not be conditionally hidden')
      .not.toMatch(/v-(show|if)=/)

    // One heading, and it must name the map unconditionally. Asserting the *absence* of the removed
    // `app.canvasView` key was vacuous — that key no longer exists in `assets/`, so nothing could reintroduce
    // the literal. What can regress is the heading becoming state-dependent again, so assert the shape instead.
    const headingAt = board.indexOf('canvas-map__title')
    expect(headingAt, 'the map heading should exist').toBeGreaterThan(-1)
    const heading = board.slice(headingAt, board.indexOf('</span>', headingAt))
    expect(heading, 'the map heading should not branch on state').not.toMatch(/\?[^:]*:/)
    expect(heading, 'the map heading should name the map').toContain("t('app.canvasMap')")
  })

  it('keeps the dock heading a tier above the group labels it introduces', () => {
    // The heading was `0.72rem`/800 against `--iot-font-min` (11px)/700 group labels *beneath* it —
    // 0.52px of difference at a heavier weight, i.e. two heading levels rendering as one. It cleared
    // `typographyFloor` (11.52px over an 11px floor), which is why nothing flagged it; a floor is a
    // minimum for body text, not a target for a heading. Uppercase also cost apparent x-height and
    // word shape, which is most of why four characters read as smaller than they measured.
    const title = css.slice(css.indexOf('.iot-board .board-action-dock__title {'))
      .slice(0, css.slice(css.indexOf('.iot-board .board-action-dock__title {')).indexOf('}'))
    const titlePx = Number(/font-size:\s*([\d.]+)rem/.exec(title)?.[1]) * 16
    expect(titlePx, 'the dock heading should use the panel-title tier').toBeGreaterThanOrEqual(14)
    expect(title, 'the heading should not be uppercased').not.toMatch(/text-transform:\s*uppercase/)

    const groupLabel = css.slice(css.indexOf('.iot-board .board-tool-group-label {'))
    const groupPx = /font-size:\s*var\(--iot-font-min\)/.test(groupLabel.slice(0, groupLabel.indexOf('}')))
      ? 11
      : Number.NaN
    expect(groupPx, 'group labels should stay on the minimum tier').toBe(11)
    expect(titlePx - groupPx, 'the two tiers should be distinguishable').toBeGreaterThanOrEqual(2)
  })
})
