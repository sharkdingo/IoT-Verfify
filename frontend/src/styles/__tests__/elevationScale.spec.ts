import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Depth comes from the elevation scale, never from a literal offset/blur/alpha.
 *
 * `shadowRoleOwnership.spec.ts` owns the *hue* rule and deliberately exempts neutral shade as "elevation, not
 * meaning". That left elevation itself unchecked, and it drifted exactly the way the radius scale had:
 * `--shadow-elevated` was the only token, so anything wanting a different depth wrote its own value. Eight
 * distinct neutral elevations, no two agreeing, each plausible in isolation.
 *
 * Two defects came out of that, both visible on screen rather than theoretical:
 *
 * - **A hand-written shadow does not follow the theme.** Every literal carried a light-theme wash
 *   (`rgba(15, 23, 42, …)`) in a property whose token the dark theme overrides, so on a near-black ground the
 *   shadow was doing nothing while its neighbours' tokens deepened. Reviewed as "the shadow is still those
 *   same few colours".
 * - **The wrong step misdescribes the thing.** The dock's hover tooltip used `--shadow-elevated`, an 18px/42px
 *   panel lift, on a two-line hover chip — so hovering a dock button dropped a panel-sized shadow across the
 *   canvas. Depth says what kind of thing something is; a chip claiming a panel's depth is a lie about it.
 *
 * Three steps, matching the three depths the product actually has: `--shadow-raised` (a control lifting off
 * its own surface), `--shadow-floating` (a transient chip or node above content), `--shadow-elevated` (a panel
 * above the page).
 *
 * `inset` shadows are exempt: an inset ring is an edge or a pressed-state marker, not elevation. `none` and
 * `0 0 0 …` spread-only rings are exempt for the same reason — a focus ring or hairline is a boundary, and
 * `focusIndicator.spec.ts` already measures those against WCAG 1.4.11.
 */

const SRC = join(__dirname, '../..')
const STEPS = ['--shadow-raised', '--shadow-floating', '--shadow-elevated']

/**
 * The board's own stylesheets, which is where this migration happened.
 *
 * Twenty more hand-written neutral elevations remain in nine components outside the board — `ChatView`,
 * `Landing`, `PublicHeader`, `ThemeToggle`, `LanguageToggle`, `ToggleSwitch`, `AccountDeleteDialog`,
 * `ControlCenter`'s scoped block, and `CanvasBoard`'s. They are the same defect and should move onto the
 * scale, but each needs its depth *chosen* and then measured on the surface it sits on, and several of them
 * (chat, landing, the auth dialog) are outside the review this change came from. Scoping the file list is
 * deliberate: a `.skip` or a hardcoded allow-list of twenty paths would go stale silently, whereas this
 * states plainly what is covered and leaves the rest visibly unconverted.
 */
const FILES = ['styles/base.css', 'styles/board.css']

const sources = () => FILES.map(name => ({ name, text: readFileSync(join(SRC, name), 'utf8') }))

/** Comments quote the defects they explain, so counting them inflates every measurement. */
const withoutComments = (text: string) =>
  text.replace(/\/\*[\s\S]*?\*\//g, '').replace(/<!--[\s\S]*?-->/g, '')

describe('elevation scale', () => {
  it('declares each step once per theme, and deepens them for the dark ground', () => {
    const base = readFileSync(join(SRC, 'styles/base.css'), 'utf8')
    for (const step of STEPS) {
      // `:root` (light values), the dark block, and the explicit light block — the dark block is the default
      // theme, so an explicit light theme must reset every step rather than inherit.
      const declared = base.match(new RegExp(`${step}:`, 'g')) ?? []
      expect(declared, `${step} should be declared for both themes`).toHaveLength(3)
    }

    // A shadow darkens its ground, and a near-black ground has little headroom left, so the light theme's
    // alphas disappear on it. Each dark step must be at least as opaque as its light counterpart.
    const alphas = (block: string) => STEPS.map(step => {
      const value = new RegExp(`${step}:\\s*[^;]*rgba\\([^)]*?([\\d.]+)\\)`).exec(block)
      return Number(value?.[1])
    })
    const darkAt = base.indexOf(":root[data-theme='dark'],")
    const lightAt = base.indexOf(":root[data-theme='light'] {")
    const dark = alphas(base.slice(darkAt, lightAt))
    const light = alphas(base.slice(lightAt))
    dark.forEach((a, index) => {
      expect(a, `dark step ${STEPS[index]} should parse`).toBeGreaterThan(0)
      expect(a, `${STEPS[index]} should be at least as opaque in dark theme`)
        .toBeGreaterThanOrEqual(light[index])
    })
  })

  it('has no elevation token outside the scale', () => {
    /*
     * Two more existed and both had the same dark-theme bug, which is what a fourth owner buys you:
     * `--iot-node-shadow` and `--iot-color-card-shadow` were declared as `rgba(15, 23, 42, 0.9)` in dark
     * theme — the *light* palette's navy at 90% opacity, where every dark shadow is `rgba(2, 6, 23, …)`. The
     * node one was worse than a wrong colour: the node's resting rule used the scale while its four state
     * rules (focus, focused, trace-active, trace-changed) used that token, so highlighting a node silently
     * changed its base depth as well as adding a ring.
     *
     * `--iot-color-resize-shadow` is exempt and stays: it is a *colour* for a 1px handle ring, not an
     * offset/blur elevation, and the ring is a boundary.
     */
    const base = readFileSync(join(SRC, 'styles/base.css'), 'utf8')
    const tokens = new Set<string>()
    for (const match of base.matchAll(/^\s*(--[a-z0-9-]*shadow[a-z0-9-]*):\s*[^;]*\d+(?:px|rem)\s+[\d.]+(?:px|rem)/gmi)) {
      tokens.add(match[1])
    }
    expect([...tokens].sort()).toEqual([...STEPS].sort())
  })

  it('never hand-writes a neutral elevation', () => {
    const offenders: string[] = []
    for (const { name, text } of sources()) {
      withoutComments(text).split(/\r?\n/).forEach((line, index) => {
        const match = /box-shadow:\s*([^;}]+)/.exec(line)
        if (!match) return
        for (const layer of match[1].split(/,(?![^(]*\))/)) {
          const value = layer.trim()
          if (!value || value === 'none' || value.includes('inset')) continue
          if (value.startsWith('var(')) continue
          // A spread-only ring (`0 0 0 <n>`) is a boundary, not a lift.
          if (/^0\s+0\s+0\s/.test(value)) continue
          // Only neutral shade is this spec's business; hue belongs to shadowRoleOwnership.
          if (!/rgba\(\s*(15,\s*23,\s*42|2,\s*6,\s*23|0,\s*0,\s*0)/.test(value)) continue
          offenders.push(`${name}:${index + 1}  ${value}`)
        }
      })
    }
    expect(offenders, `use a --shadow-* step:\n${offenders.join('\n')}`).toEqual([])
  })

  it('gives the dock tooltip a chip depth, not a panel depth', () => {
    // The specific defect: an 18px/42px panel lift on a hover label, which is what made hovering a dock
    // button drop a panel-sized shadow across the canvas.
    const css = readFileSync(join(SRC, 'styles/board.css'), 'utf8')
    const at = css.indexOf('.iot-board .board-tool-tooltip {')
    expect(at, 'the tooltip rule should exist').toBeGreaterThan(-1)
    const body = css.slice(at, at + css.slice(at).indexOf('}'))
    expect(body).toMatch(/box-shadow:\s*var\(--shadow-floating\)/)
  })

  it('keeps every dock button flat, so the tiers differ by fill rather than by depth', () => {
    // `open-verification-panel` carried Tailwind's `shadow-lg` while its seven siblings declared
    // `box-shadow: none` — one of eight floating above a strip they all belong to, inside a panel that is
    // itself elevated. It read as a depth difference where the product means an emphasis difference.
    const board = readFileSync(join(SRC, 'views/Board.vue'), 'utf8')
    const tags = board.match(/class="board-tool-button[^"]*"/g) ?? []
    expect(tags.length, 'the dock buttons should be found').toBeGreaterThanOrEqual(8)
    for (const tag of tags) {
      expect(tag, `a dock button must not carry its own elevation: ${tag}`).not.toMatch(/\bshadow-(sm|md|lg|xl|2xl)\b/)
    }
  })

  it('keeps the two quiet dock tiers on one ground', () => {
    // Run History sat on `--board-control-bg` (#f1f5f9) while the four suggestions sat on `--board-card-bg`
    // (#ffffff) — two tiers that both mean "not the primary action", on two different neutrals, four rows
    // apart in one strip. A background change down a vertical list implies a *category* change, so it read as
    // an unexplained grey band among white buttons. What separates them is the border hue and the label.
    //
    // Border contrast was re-measured in a browser after the move, because changing the ground changes what
    // the border is measured against: 4.76 (vs fill) / 3.02 (vs panel) light, 3.73 / 3.90 dark — the 3:1
    // component minimum still holds on the new ground.
    const css = readFileSync(join(SRC, 'styles/board.css'), 'utf8')
    const groundOf = (selector: string) => {
      const at = css.indexOf(`${selector} {`)
      expect(at, `${selector} should exist`).toBeGreaterThan(-1)
      const body = css.slice(at, at + css.slice(at).indexOf('}'))
      return /background-color:\s*([^;]+)/.exec(body)?.[1].trim()
    }
    const quiet = groundOf('.iot-board .board-tool-button--view')
    expect(quiet).toBeTruthy()
    expect(quiet).toBe(groundOf('.iot-board .board-tool-button--suggestion'))

    // Hover and pressed must mix against that same ground, or hover changes ground rather than deepening it.
    // They still named `--board-control-bg` after the rest state moved, which would have made hover *lighter*
    // than rest in light theme.
    for (const state of [':hover:not(:disabled)', "[aria-pressed='true']"]) {
      const at = css.indexOf(`.iot-board .board-tool-button--view${state} {`)
      expect(at, `the --view${state} rule should exist`).toBeGreaterThan(-1)
      const body = css.slice(at, at + css.slice(at).indexOf('}'))
      expect(body, `--view${state} should mix against the tier's resting ground`)
        .not.toContain('--board-control-bg')
    }
  })
})
