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

  it('keeps every suggestion tool a real focusable button with a name', () => {
    // This is a demotion in emphasis, not disclosure: the tools stay keyboard reachable and named.
    for (const id of SUGGESTION_TOOLS) {
      const markup = buttonMarkup(id)
      expect(markup, `${id} should be a <button>`).toContain('<button')
      expect(markup, `${id} needs an accessible name`).toContain('aria-label')
      expect(markup, `${id} should report its panel state`).toContain('aria-pressed')
    }
  })
})
