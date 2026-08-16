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

  it('never asks a borderless chip role for a border', () => {
    /*
     * `board-chip-*` declares `border: 0` deliberately — the roles are badges, where a border would add a
     * second edge inside a dense row. So `board-chip-warning border board-border-subtle` is a markup
     * contradiction, and the cascade resolves it the way the reader does not expect: `board.css` is
     * **unlayered** while Tailwind's `.border` lives in `@layer utilities`, and unlayered wins regardless
     * of order or specificity. Measured in the real host chain: that markup renders
     * `border-top-width: 0px`, while `board-surface-warning` renders 0.667px from the role's own border
     * token.
     *
     * Five sites read this way, all of them callouts rather than badges — including the verification
     * result dialog's error notice and its generation-warning notice. An edgeless tint reads as a
     * background wash rather than a bounded notice, so a warning strip stopped looking like one.
     * `board-surface-*` is the bounded form and needs no width utility.
     *
     * Only the `border` *width* utility counts. A bare `border-[color:…]` on a chip is a different
     * pattern — it sets a colour for an edge the chip does not draw, which is inert but not misleading —
     * and several small badges legitimately carry it.
     */
    const offenders: string[] = []
    const src = join(__dirname, '../..')
    for (const dir of DIRS) {
      for (const entry of readdirSync(join(src, dir), { withFileTypes: true })) {
        if (!entry.isFile() || !entry.name.endsWith('.vue')) continue
        const text = readFileSync(join(src, dir, entry.name), 'utf8')
        text.split(/\r?\n/).forEach((line, index) => {
          // Comments explain the defect and necessarily quote it; skip them or the guard fails on its
          // own documentation — a trap this repo has hit three times.
          if (/^\s*(\/\/|\*|<!--)/.test(line)) return
          // An UNPREFIXED chip role only. `hover:board-chip-info` tints on hover and does not claim the
          // resting border, so a `focus:ring` or a resting border beside it is not a contradiction.
          if (!/(^|[\s'"])board-chip-[a-z]+/.test(line)) return
          // Any border the chip would silence: the bare width utility or a numeric width. Measured: a
          // chip role zeroes `border-2 border-dashed` exactly as it zeroes `border`, while the same
          // markup without the chip renders 2px dashed.
          if (!/(^|[\s'"])border(-[0-9]+)?(?=[\s'"])/.test(line)) return
          offenders.push(`${dir}/${entry.name}:${index + 1}  ${line.trim().slice(0, 90)}`)
        })
      }
    }

    expect(offenders, `a chip role cannot render a border; use board-surface-* instead:\n${offenders.join('\n')}`)
      .toEqual([])
  })
})
