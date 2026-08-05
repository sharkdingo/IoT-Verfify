import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A `hover:`/`focus:`/`disabled:`/`dark:` prefix on a hand-written class only works if this repo defines it.
 *
 * Tailwind generates variants for utilities *it* owns. `board-*` and `iot-*` are hand-written in `board.css`, so
 * `hover:board-chip-danger` in a template emitted **nothing** — the class sat in the DOM and no rule matched it.
 * Verified against the built bundle: grepping all 14 emitted CSS files for any `<variant>\:board-*` selector
 * returned zero matches, while the unprefixed base classes were present.
 *
 * That silently disabled **90 declarations** across the components, with nothing detecting it. The ones that
 * mattered, all confirmed in a browser:
 *
 *   - The device delete button asked for `hover:board-chip-danger hover:board-text-danger`. Colour and background
 *     were **identical** on hover (`rgb(97,113,135)`, transparent) — a destructive action with no danger cue.
 *   - Cancel/delete on running verification tasks (5 sites) — same.
 *   - `disabled:board-chip-info` on the runtime save button: the only `disabled:` utility Tailwind could emit
 *     there is `cursor-not-allowed`, so a *disabled* primary kept its accent fill and read as enabled.
 *   - `group-focus-within:board-text-info` on 13 rule-builder select icons — the keyboard-focus cue was absent.
 *
 * There is a second trap this does not catch, recorded here because it cost three attempts: defining the rule is
 * not sufficient if it loses the cascade. The ink variants had to be placed *after* the neutral-text normaliser
 * (`.iot-board .board-side-panel .text-slate-500`), because at equal specificity source order decides. Only CDP
 * matched-styles showed which rule won; the symptom was a danger-tinted background under a grey glyph.
 */

const DIRS = ['components', 'components/common', 'views']
const STYLE_FILES = ['styles/board.css', 'styles/base.css', 'style.css']

/** Every variant-prefixed hand-written class used in a template, with where it came from. */
const usedVariants = () => {
  const found = new Map<string, string[]>()
  const src = join(__dirname, '../..')
  for (const dir of DIRS) {
    for (const entry of readdirSync(join(src, dir), { withFileTypes: true })) {
      if (!entry.isFile() || !entry.name.endsWith('.vue')) continue
      const text = readFileSync(join(src, dir, entry.name), 'utf8')
      text.split(/\r?\n/).forEach((line, index) => {
        // `class="…"` and `:class="[…]"` alike — the whole line is scanned, since a binding may span it.
        for (const match of line.matchAll(
          /\b((?:hover|focus|focus-visible|active|disabled|dark|group-hover|group-focus|group-focus-within):(?:board|iot)-[A-Za-z0-9_-]+)/g)) {
          const site = `${dir}/${entry.name}:${index + 1}`
          found.set(match[1], [...(found.get(match[1]) ?? []), site])
        }
      })
    }
  }
  return found
}

const declaredSelectors = () => {
  const src = join(__dirname, '../..')
  return STYLE_FILES.map(file => readFileSync(join(src, file), 'utf8')).join('\n')
}

describe('role class variants', () => {
  it('defines every variant-prefixed role class that a template uses', () => {
    const css = declaredSelectors()
    const offenders: string[] = []

    for (const [variantClass, sites] of usedVariants()) {
      // In CSS the colon is escaped: `hover:board-chip-danger` is written `.hover\:board-chip-danger`.
      // One backslash in the file, so one backslash in the needle — `'\\\\:'` was two and matched nothing,
      // which made this check report all 15 as undefined even after they were defined.
      const escaped = variantClass.replace(':', '\\:')
      if (!css.includes(escaped)) {
        offenders.push(`${variantClass} — used at ${sites.slice(0, 3).join(', ')}${sites.length > 3 ? ` (+${sites.length - 3} more)` : ''}`)
      }
    }

    expect(offenders, `these classes render nothing; define them in board.css:\n${offenders.join('\n')}`)
      .toEqual([])
  })

  it('never puts an opacity modifier on a hand-written class', () => {
    /*
     * `board-chip-warning/70` is not a Tailwind utility, so **no rule at all** is generated — not even the
     * un-suffixed strength. That is worse than the `primary/20` case `tailwind.config.js` warns about, where the
     * base utility still renders: here a danger chip and its text both come out as unstyled neutral.
     *
     * Eleven of these existed. Use `color-mix()` in a real rule if a softened role is genuinely wanted.
     */
    const offenders: string[] = []
    const src = join(__dirname, '../..')
    for (const dir of DIRS) {
      for (const entry of readdirSync(join(src, dir), { withFileTypes: true })) {
        if (!entry.isFile() || !entry.name.endsWith('.vue')) continue
        const text = readFileSync(join(src, dir, entry.name), 'utf8')
        text.split(/\r?\n/).forEach((line, index) => {
          for (const match of line.matchAll(/\b((?:board|iot)-[a-z]+(?:-[a-z]+)*(?:--[a-z-]+)?\/\d+)/g)) {
            offenders.push(`${dir}/${entry.name}:${index + 1}  ${match[1]}`)
          }
        })
      }
    }

    expect(offenders, `an opacity modifier on a hand-written class renders nothing:\n${offenders.join('\n')}`)
      .toEqual([])
  })
})
