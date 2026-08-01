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

  it('keeps run actions visually primary', () => {
    // If a run action were demoted too, the dock would have no primary action at all, which is the
    // opposite failure: a user could not tell what the Board is for.
    for (const id of RUN_TOOLS) {
      expect(buttonMarkup(id), `${id} must stay a primary action`)
        .not.toContain('board-tool-button--suggestion')
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
    for (const testId of ['trace-timeline-state-details']) {
      const at = board.indexOf(`data-testid="${testId}"`)
      expect(at, `${testId} should exist`).toBeGreaterThan(-1)
      const tagStart = board.lastIndexOf('<details', at)
      expect(board.slice(tagStart, at), `${testId} should be open by default`).toContain(' open')
    }
  })
})
