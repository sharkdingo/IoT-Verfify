import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Interactive controls are 44px targets, declared as a floor rather than left to padding.
 *
 * This defect has now been found in three separate places, each time by measuring rather than reading:
 *
 * | surface | was | controls |
 * | :--- | :--- | ---: |
 * | board nav strip | 37-40px, five different sizes | 7 of 10 |
 * | System Inspector | 24-36px | 9 |
 * | action dock | 40px, uniformly | 8 of 8 |
 *
 * The pattern in every case: the height came from `padding` plus a glyph's line-height, so it was whatever the
 * content happened to produce. A control sized by its contents has no target size — it has a coincidence. The dock
 * is the clearest example, because all eight buttons agreed on 40px and nothing in the code said 40.
 *
 * These are the surfaces a user crosses before every task — undo, the workflow entry points, the panel that lists
 * their devices — so a near-miss here costs more than the 4px suggests. `--iot-tap-min` names the value once so a
 * call site states the constraint instead of restating a number.
 */

const STYLE_DIR = join(__dirname, '..')

const css = (file: string) => readFileSync(join(STYLE_DIR, file), 'utf8')

/** The declaration block of a selector, up to its closing brace. */
const ruleBody = (file: string, selector: string): string => {
  const source = css(file)
  const at = source.indexOf(`${selector} {`)
  expect(at, `${selector} should exist in ${file}`).toBeGreaterThan(-1)
  return source.slice(at, at + source.slice(at).indexOf('}'))
}

/** 2.75rem at a 16px root. */
const MINIMUM_REM = 2.75

/** Every `min-height`/`height`/`min-width`/`width` in a block, as pixels. */
const declaredSizes = (block: string) => {
  const sizes: Array<{ raw: string, px: number }> = []
  for (const match of block.matchAll(/(?:min-)?(?:width|height):\s*([\d.]+)(rem|px)\b/g)) {
    sizes.push({ raw: match[0], px: match[2] === 'rem' ? Number(match[1]) * 16 : Number(match[1]) })
  }
  return sizes
}

describe('interactive target size floor', () => {
  it('sizes every action-dock button at the minimum', () => {
    // All eight measured 124x40 — the entry points to simulation, verification, exploration, run history and the
    // four recommendation panels, i.e. every primary workflow on the board.
    const block = ruleBody('board.css', '.iot-board .board-tool-button')
    expect(block).toMatch(new RegExp(`min-height:\\s*${MINIMUM_REM}rem`))
    expect(block).not.toMatch(/min-height:\s*2\.5rem/)
  })

  it('sizes the canvas map tools at the minimum', () => {
    // Zoom in, zoom out and fit-to-screen measured 32px — among the most repeatedly pressed controls, and the
    // ones a user reaches for while already struggling to see something.
    const block = ruleBody('board.css', '.iot-board .canvas-map__tool')
    for (const size of declaredSizes(block)) {
      expect(size.px, `${size.raw} should be at least ${MINIMUM_REM}rem`).toBeGreaterThanOrEqual(MINIMUM_REM * 16)
    }
  })

  it('sizes the nav strip controls at the minimum in the base rule', () => {
    // Not only inside a narrow-viewport media query. The nav had exactly that inversion: mobile was correct and
    // desktop was 4px short, because the rule lived in `max-width: 1023.98px` instead of the base declaration.
    for (const selector of [
      '.board-nav-bar .board-edit-history-btn',
      '.board-nav-bar .nav-logout-btn'
    ]) {
      const block = ruleBody('board.css', selector)
      for (const size of declaredSizes(block)) {
        expect(size.px, `${selector}: ${size.raw}`).toBeGreaterThanOrEqual(MINIMUM_REM * 16)
      }
    }
  })

  it('never grants a narrow viewport a larger target than the base', () => {
    // A media query for a *smaller* screen handing out a *larger* size means the wide case is the unnoticed
    // exception. Found twice in this audit — here and in the playback overlay caps.
    const source = css('board.css')
    const offenders: string[] = []
    for (const block of source.match(/@media \(max-width: 1023\.98px\)[^{]*\{[\s\S]*?\n\}/g) || []) {
      for (const rule of block.matchAll(/(\.board-nav-bar [^{]+|\.iot-board \.board-tool-button[^{]*)\{([^}]*)\}/g)) {
        for (const size of declaredSizes(rule[2])) {
          if (size.px < MINIMUM_REM * 16) offenders.push(`${rule[1].trim()} -> ${size.raw}`)
        }
      }
    }
    expect(offenders).toEqual([])
  })

  it('gives the help trigger a full target without inflating its badge', () => {
    // The trigger measured 24x24 — the smallest control in the inspector, and a help affordance is exactly what a
    // confused user reaches for. The badge stays 1.5rem so it does not compete with the content it annotates;
    // `content-box` padding grows the target instead.
    const tooltip = readFileSync(join(__dirname, '../../components/common/InfoTooltip.vue'), 'utf8')
    const at = tooltip.indexOf('.iot-info-tooltip-trigger {')
    expect(at).toBeGreaterThan(-1)
    const block = tooltip.slice(at, at + tooltip.slice(at).indexOf('}'))

    expect(block).toContain('box-sizing: content-box')
    expect(block).toMatch(/padding:\s*0\.625rem/)
    // 1.5rem badge + 2 x 0.625rem padding = 2.75rem of target.
    expect(block).toMatch(/width:\s*1\.5rem/)
    expect(block).toContain('background-clip: content-box')
  })

  it('sizes the inspector tabs and add-device control at the minimum', () => {
    const inspector = readFileSync(join(__dirname, '../../components/SystemInspector.vue'), 'utf8')

    // The tab strip measured 33px; a tab is a primary navigation target.
    expect(inspector).toMatch(/min-w-0 min-h-11 rounded-lg px-2 py-2/)
    // `inspector-add-device` measured 26x36 and is the primary way to add a device to the board.
    const addAt = inspector.indexOf('data-testid="inspector-add-device"')
    expect(addAt).toBeGreaterThan(-1)
    const addButton = inspector.slice(addAt, addAt + 400)
    expect(addButton).toMatch(/h-11 w-11/)
  })
})
