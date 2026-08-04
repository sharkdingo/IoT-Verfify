import { readFileSync, readdirSync, statSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A filled button must not be disabled by opacity alone — the fade takes its label with it.
 *
 * `opacity` multiplies the whole control, so a white label on a role fill moves toward the fill as the fill
 * moves toward the page. Measured on the two that did this: the template-reset primary went from **5.02:1 to
 * 2.49:1** at `opacity: 0.6`, and the protected-action confirm from **4.83:1 to 2.51:1** at `0.55`. A disabled
 * control is exempt from AA, but a user still has to read *which* button they cannot press — and on a
 * confirmation, which one they are being asked about.
 *
 * Desaturating says "inactive" through the fill instead: mixed toward a neutral, both keep their ink above
 * 5:1 while plainly reading as drained. `AccountDeleteDialog` already did this, and its comment records why —
 * a faded-but-still-saturated danger button read as *armed*, on the product's one irreversible action.
 *
 * Scope, deliberately narrow, because opacity is the right answer nearly everywhere else:
 *   - only `:disabled` rules on a selector whose base class is painted with a role **fill**;
 *   - `cursor: wait` is excluded — that is a loading state, where fading is the honest signal;
 *   - controls with no text (`ToggleSwitch`'s thumb is `aria-hidden`) have no label to lose;
 *   - a parent that already desaturates (`.board-panel--interaction-read-only` uses
 *     `filter: saturate(0.72)`) makes the opacity beneath it a softener, not the signal.
 */

const SRC = join(__dirname, '../..')
const SKIP = new Set(['assets', 'testing', '__tests__'])

const sources = () => {
  const files: Array<{ name: string, text: string }> = []
  const walk = (dir: string, prefix: string) => {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const full = join(dir, entry.name)
      if (statSync(full).isDirectory()) {
        if (!SKIP.has(entry.name)) walk(full, `${prefix}${entry.name}/`)
      } else if (/\.(css|vue)$/.test(entry.name)) {
        files.push({ name: `${prefix}${entry.name}`, text: readFileSync(full, 'utf8') })
      }
    }
  }
  walk(SRC, '')
  return files
}

const stripComments = (text: string) =>
  text.replace(/\/\*[\s\S]*?\*\//g, match => match.replace(/[^\n]/g, ' '))

/** Anything that carries the disabled state other than a global fade. */
const STATE_SIGNAL = /color-mix|saturate|grayscale|background\s*:|box-shadow\s*:\s*none|border-color\s*:/

describe('disabled fill legibility', () => {
  it('never disables a role-filled control by opacity alone', () => {
    const offenders: string[] = []

    for (const { name, text } of sources()) {
      const clean = stripComments(text)

      // Base classes painted with a role fill under light ink — the combination opacity ruins.
      const filled = new Set<string>()
      for (const rule of clean.matchAll(/([^{}]+)\{([^{}]*)\}/g)) {
        const body = rule[2]
        if (!/background[^;]*var\(--(?:danger|warning|success|info|accent)-fill\)/.test(body)) continue
        if (!/color\s*:\s*(#fff(fff)?|white)/i.test(body)) continue
        for (const cls of rule[1].matchAll(/\.([a-zA-Z][a-zA-Z0-9_-]*)/g)) filled.add(cls[1])
      }
      if (!filled.size) continue

      for (const rule of clean.matchAll(/([^{}]*:disabled[^{}]*)\{([^{}]*)\}/g)) {
        const selector = rule[1].trim().replace(/\s+/g, ' ')
        const body = rule[2]
        if (!/opacity:\s*0?\.\d/.test(body)) continue
        if (/cursor:\s*wait/.test(body)) continue
        if (STATE_SIGNAL.test(body)) continue

        // Does this `:disabled` rule reach one of the filled classes?
        const reaches = [...filled].filter(c => selector.includes(`.${c}`))
        if (!reaches.length) continue

        // A more specific sibling may supply the desaturation for the filled variant.
        const covered = reaches.some(c =>
          [...clean.matchAll(new RegExp(`\\.${c}[^{}]*:disabled[^{}]*\\{([^{}]*)\\}`, 'g'))]
            .some(m => STATE_SIGNAL.test(m[1])))
        if (covered) continue

        const line = clean.slice(0, rule.index).split('\n').length
        offenders.push(`${name}:${line}  ${selector} fades a role-filled control; desaturate the fill instead`)
      }
    }

    expect(offenders).toEqual([])
  })
})
