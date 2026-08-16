import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Colour ownership, enforced rather than remembered.
 *
 * The components once carried 1,529 raw Tailwind hue utilities and 233 `dark:` counterparts, so each
 * module had picked its own palette and the product read as several tools stitched together. Dark
 * theme was patched on top by 28 class-keyed `!important` rules that rewrote hues by class name, which
 * meant the source said what a colour *looked like in one theme* and never what it *meant*.
 *
 * All of that is gone. These checks exist because the state is only worth reaching if it holds: a
 * single `text-amber-700` added in review restarts the drift, and it is invisible in a diff.
 */

const COMPONENT_DIR = join(__dirname, '../../components')
const VIEW_DIR = join(__dirname, '../../views')

/** Hues that carry meaning. Structural neutrals (slate/gray/zinc/stone) are deliberately allowed. */
const SEMANTIC_HUES = [
  'red', 'orange', 'amber', 'yellow', 'lime', 'green', 'emerald', 'teal',
  'cyan', 'sky', 'blue', 'indigo', 'violet', 'purple', 'fuchsia', 'pink', 'rose'
].join('|')

const PROPERTIES = 'bg|text|border|from|to|via|ring|divide|placeholder|accent|outline|decoration'

const sources = () => {
  const files: Array<{ name: string, text: string }> = []
  for (const dir of [COMPONENT_DIR, VIEW_DIR]) {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      if (entry.isFile() && entry.name.endsWith('.vue')) {
        files.push({ name: entry.name, text: readFileSync(join(dir, entry.name), 'utf8') })
      }
    }
  }
  return files
}

const matchesIn = (text: string, pattern: RegExp) => text.match(pattern) || []

/**
 * `sources()` reads one directory level, which is every file the rules above were written against.
 * `components/common/` holds six more (the toggles, the tooltips, the public header), and a hover
 * defect is exactly as invisible there. This walks instead of listing.
 */
const allSources = () => {
  const files: Array<{ name: string, text: string }> = []
  const walk = (dir: string, prefix: string) => {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const path = join(dir, entry.name)
      if (entry.isDirectory()) walk(path, `${prefix}${entry.name}/`)
      else if (entry.name.endsWith('.vue')) {
        files.push({ name: `${prefix}${entry.name}`, text: readFileSync(path, 'utf8') })
      }
    }
  }
  walk(COMPONENT_DIR, '')
  walk(VIEW_DIR, '')
  return files
}

/**
 * The lines an ink/fill pair can legitimately be spread across: one `class="…"` literal or one
 * `:class="[ … ]"` array.
 *
 * A fixed +/-3 window looked equivalent and is not. The rule recommendation panel's Apply button is a
 * five-line binding whose `text-white` sits four lines above its fill, so the pale-surface hover defect in
 * it fell one line outside the window — the check ran, found nothing, and the button hovered white ink onto
 * `--warning-surface` in shipped code. Widening the constant to 5 would have re-broken on a six-line
 * binding; the binding itself is the unit the markup actually uses.
 */
const enclosingBinding = (lines: string[], index: number): string => {
  const opens = (text: string) => /:?class="/.test(text)
  let first = index
  while (first > 0 && !opens(lines[first])) first -= 1
  let last = index
  while (last < lines.length - 1 && !/"/.test(lines[last].replace(/:?class="/, ''))) last += 1
  // A run-away scan means the heuristic did not find a boundary; fall back to a bounded window rather
  // than joining half the file, which would make an unrelated `text-white` manufacture a hit.
  if (index - first > 12 || last - index > 12) {
    return lines.slice(Math.max(0, index - 3), index + 4).join(' ')
  }
  return lines.slice(first, last + 1).join(' ')
}

describe('semantic colour ownership', () => {
  it('uses no raw semantic-hue utility in any component or view', () => {
    const pattern = new RegExp(`\\b(?:${PROPERTIES})-(?:${SEMANTIC_HUES})-[0-9]{2,3}\\b`, 'g')
    const offenders = sources()
      .map(({ name, text }) => ({ name, hits: [...new Set(matchesIn(text, pattern))] }))
      .filter(({ hits }) => hits.length > 0)

    // Named rather than counted: the failure should say which class to replace with which role.
    expect(offenders.map(o => `${o.name}: ${o.hits.join(', ')}`)).toEqual([])
  })

  it('needs no per-theme hue override, because the roles are theme-aware', () => {
    const pattern = new RegExp(`dark:(?:${PROPERTIES})-(?:${SEMANTIC_HUES})-[0-9]{2,3}`, 'g')
    const offenders = sources()
      .map(({ name, text }) => ({ name, hits: [...new Set(matchesIn(text, pattern))] }))
      .filter(({ hits }) => hits.length > 0)

    expect(offenders.map(o => `${o.name}: ${o.hits.join(', ')}`)).toEqual([])
  })

  it('never rewrites a hue by class name in a theme block', () => {
    // The `!important` class-keyed remaps that used to darken raw hues for dark theme. Reinstating one
    // would mean a component had gone back to declaring appearance instead of meaning.
    const boardCss = readFileSync(join(__dirname, '../board.css'), 'utf8')
    const darkBlocks = boardCss.match(/\.dark [^{]*\{[^}]*\}/g) || []
    const remaps = darkBlocks.filter(block =>
      new RegExp(`\\.(?:text|bg|border)-(?:${SEMANTIC_HUES})-[0-9]{2,3}`).test(block))

    expect(remaps).toEqual([])
  })

  it('gives every element one role, never two', () => {
    // A surface and a text colour from different roles on one element states two meanings at once —
    // the mechanical hue-to-role sweep produced exactly this, e.g. warning text inside an info panel,
    // which also measured below AA. `hover:` is excluded: a destructive control is legitimately muted
    // at rest and danger on hover.
    const conflicts: string[] = []
    for (const { name, text } of sources()) {
      for (const [, cls] of text.matchAll(/\sclass="([^"{}]*)"/g)) {
        const resting = cls.replace(/hover:\S+/g, '')
        const surfaces = new Set(
          (resting.match(/board-(?:surface|chip)-(danger|warning|success|info|accent)/g) || [])
            .map(match => match.split('-').pop()))
        const texts = new Set(
          (resting.match(/board-text-(danger|warning|success|info)/g) || [])
            .map(match => match.split('-').pop()))
        const mixed = surfaces.size > 1 || texts.size > 1
          || (surfaces.size === 1 && texts.size === 1 && ![...surfaces][0] === ![...texts][0]
            && [...surfaces][0] !== [...texts][0])
        if (mixed) conflicts.push(`${name}: surfaces=[${[...surfaces]}] texts=[${[...texts]}]`)
      }
    }

    expect(conflicts).toEqual([])
  })

  it('never hovers a filled role button onto its own pale surface', () => {
    // White text on a pale tint is unreadable. Collapsing gradients produced three of these, and no
    // rendering test would have caught them: they are hover states on three specific buttons.
    // Per line, and matching the fill half too.
    //
    // This rule was written against `class="…"` literals, whose matcher excludes braces — so it never saw a
    // single `:class="[ … ]"` binding, which is where nearly all of these buttons actually live. Recreating
    // the defect inside one passed the spec. It also only knew the bare role, so the same button hovering
    // from `--danger-fill` to a pale surface would slip through.
    //
    // Ink can sit several lines from the fill inside a multi-line binding, so the unit is the enclosing
    // binding — see `enclosingBinding` for the five-line case that a fixed window missed in shipped code.
    const offenders: string[] = []
    for (const { name, text } of allSources()) {
      const lines = text.split('\n')
      lines.forEach((line, index) => {
        for (const role of ['danger', 'warning', 'success', 'accent', 'info']) {
          const filled = [`bg-[color:var(--${role})]`, `bg-[color:var(--${role}-fill)]`]
            .some(token => line.includes(token))
          if (!filled) continue
          if (!line.includes(`hover:bg-[color:var(--${role}-surface)]`)) continue
          if (!/\btext-white\b/.test(enclosingBinding(lines, index))) continue
          offenders.push(`${name}:${index + 1} filled ${role} hovers to --${role}-surface under white text`)
        }
      })
    }

    expect(offenders).toEqual([])
  })

  it('never hovers a control onto the colour it already has', () => {
    /*
     * A `hover:` that names its own resting value renders nothing. It is not a contrast failure, so the
     * rules above pass it, and it is invisible in a diff because the line *looks* like it handles hover.
     *
     * Four sites had this, all `bg-[color:var(--danger-fill)] hover:bg-[color:var(--danger-fill)]`:
     * `spec-add-condition-a`, `spec-add-condition-if`, `spec-create`, and the counterexample View button.
     * So the accent buttons beside them lit up under the pointer (`--accent-fill-hover` exists and is
     * solved per theme) while the red ones stayed inert — the pattern read as reused, and was not.
     *
     * Scanned per line and per property, so a class list that legitimately hovers `bg` while keeping
     * `text` is untouched. `shadow` is excluded: `hover:shadow-lg` beside `shadow-md` is a real change
     * and the two are different tokens anyway.
     *
     * A bare `hover:` with nothing after it is the degenerate case and is checked too: the counterexample
     * rail's unvisited marker ended in `'bg-white border-slate-300 hover:'`, a truncated edit that emits no
     * rule at all. Its sibling rail in `SimulationTimeline.vue` hovers the border to the accent, so the
     * intent was legible and only the class was missing.
     */
    const offenders: string[] = []
    for (const { name, text } of allSources()) {
      text.split('\n').forEach((line, index) => {
        // Only inside a quoted class list. A preceding class token was not enough of a discriminator:
        // these prefixes are ordinary English before a colon, and the comments in this repo write
        // "receives focus:", "the violet is dark:" and "or disabled:" — three false hits, no real ones.
        // A truncated variant always ends the string it is in, so the quote is the signal.
        for (const [, prefix] of line.matchAll(
          /[\w\]/-]\s((?:group-)?(?:hover|focus-visible|focus|active|disabled|dark)):(?=['"])/g
        )) {
          offenders.push(`${name}:${index + 1} dangling ${prefix}: with no utility after it`)
        }
      })
    }
    const properties = ['bg', 'text', 'border', 'ring', 'outline', 'fill', 'stroke']
    for (const { name, text } of allSources()) {
      text.split('\n').forEach((line, index) => {
        for (const property of properties) {
          // `group-hover:` and `focus:` are the same promise made by a different trigger, and the import
          // dropzone's icon tile was a `group-hover:` instance — matched here only because it contains
          // the substring `hover:`. Named rather than left to that accident.
          const hovers = [...line.matchAll(
            new RegExp(`((?:group-)?(?:hover|focus-visible|focus)):${property}-(\\[[^\\]]+\\]|[\\w./-]+)`, 'g')
          )]
          for (const [, prefix, value] of hovers) {
            // `(?![\w/-])` and not `(?![\w-])`: `text-white/70` hovering to `text-white` is a real
            // change, and treating the opacity suffix as absent made every one of those a false hit.
            const resting = new RegExp(`(?<![\\w:/-])${property}-${value
              .replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w/-])`)
            if (resting.test(line)) {
              offenders.push(`${name}:${index + 1} ${prefix}:${property}-${value} equals its resting value`)
            }
          }
        }
      })
    }

    expect(offenders).toEqual([])
  })

  it('fills with the fill half of a role, never the text half, under light ink', () => {
    // The sibling of the rule above, and the same mistake one step earlier: not hovering onto a pale tint,
    // but *starting* on the wrong half of the role.
    //
    // Each bare role token is tuned to be legible **as text on the page ground**, so the dark theme lightens
    // it. Used as a fill under white ink that inverts: measured `--accent` **2.54:1**, `--warning` **1.44**,
    // `--danger` **1.90**, `--success` **1.52** in dark theme, across 40 sites — every primary action on the
    // board. `--accent-strong` is worse still (1.80), and it is the *hover*, so contrast fell as the user
    // interacted with the control. Light theme passed throughout, which is why this survived so long: one
    // dark blue happens to serve both jobs there.
    //
    // The `-fill` halves are theme-stable and solved for white ink at >= 4.5:1. A fill with no ink on it
    // (progress bar, playback rail, pulse ring, 1px stripe) legitimately keeps the bare role — its contrast
    // obligation is 3:1 against a neighbour, not against text — so this only fires when light ink is present.
    // Scanned per *line*, not per `class="…"` literal.
    //
    // The rule above uses `\sclass="([^"{}]*)"`, whose `[^{}]` deliberately skips dynamic bindings. Inheriting
    // that here made this rule miss most of the codebase: `:class="[ … ]"` arrays contain braces, and
    // `Board.vue` alone has 51 of them. A mutation reverting a real fill inside one of those bindings passed
    // this spec — the check existed and could not fail for the case it was written for, which is worse than
    // no check. "Ink and fill sit on the same line in every one of these bindings" was the next wrong
    // premise, and it made this rule catch **zero** of the real cases: in a multi-line `:class="[…]"` array
    // the shared classes (including `text-white`) are the first element and the conditional fill is the
    // second, so they are never on one line. Seven inversions were sitting behind that — the four Stop
    // buttons on `bg-[color:var(--danger)]` and three recommendation "Applied" states on
    // `bg-[color:var(--success)]`, i.e. 1.90:1 and 1.52:1 in dark theme. The window is the same +/-3 lines
    // the sibling rule above already uses, and it is scoped to the enclosing binding rather than the file
    // so an unrelated `text-white` further down cannot manufacture a hit.
    const offenders: string[] = []
    for (const { name, text } of allSources()) {
      const lines = text.split('\n')
      lines.forEach((line, index) => {
        for (const role of ['accent', 'danger', 'warning', 'success', 'info']) {
          for (const suffix of ['', '-strong']) {
            if (!line.includes(`bg-[color:var(--${role}${suffix})]`)) continue
            if (!/\btext-white\b|\btext-white\/\d+\b/.test(enclosingBinding(lines, index))) continue
            offenders.push(`${name}:${index + 1} light ink on bg-[color:var(--${role}${suffix})] — use --${role}-fill`)
          }
        }
      })
    }

    expect(offenders).toEqual([])
  })

  it('defines every role fill as a theme-stable token', () => {
    // The point of the pair is that the fill does *not* flip with the theme, so one ink is correct in both.
    // The panel banner proved why: it used `--accent`, so black ink measured 4.06 in light and 8.26 in dark
    // while white measured the reverse — meaning no single markup could be right, and one panel title
    // rendered at 1.44:1. A fill token that differs between the light and dark blocks recreates that trap.
    const base = readFileSync(join(__dirname, '../base.css'), 'utf8')
    const valuesOf = (token: string) => [...base.matchAll(new RegExp(`--${token}:\\s*(#[0-9a-f]{6})`, 'gi'))]
      .map(m => m[1].toLowerCase())

    // No `info` here: nothing in the product puts light ink on an info fill, so an `--info-fill` token would be
    // speculative — I added one for symmetry and removed it on review. The lines above still *check* for `info`
    // misuse, which costs nothing and would catch the first real one.
    // `danger-fill-hover` and `warning-fill-hover` are included, unlike `accent-fill-hover`. That is not a
    // symmetry choice: `--accent-fill` has headroom to brighten in dark theme, `--danger-fill` (4.83 under
    // white ink) does not — #ef4444 measures 3.76 — so both roles must darken in both themes, and a later
    // "the dark theme should brighten this, like accent does" edit would put them under AA. Pinned here so
    // the constraint is checked rather than only explained in `base.css`.
    const drifted: string[] = []
    for (const token of ['accent-fill', 'danger-fill', 'warning-fill', 'success-fill',
      'danger-fill-hover', 'warning-fill-hover']) {
      const values = valuesOf(token)
      // Three theme blocks declare each token (light, dark, and the explicit light reset).
      if (values.length !== 3) { drifted.push(`--${token} declared ${values.length}x, expected 3`); continue }
      if (new Set(values).size !== 1) drifted.push(`--${token} differs by theme: ${values.join(', ')}`)
    }

    expect(drifted).toEqual([])
  })

  it('keeps white ink above AA on every fill token, including the hover and disabled states', () => {
    // The values themselves, checked arithmetically. The rules above enforce that the right *token* is used
    // and that the base fill does not flip; neither would notice if someone edited a fill to a value white
    // text cannot sit on — which is precisely the original defect, one layer down.
    //
    // `--accent-fill-hover` is deliberately excluded from the theme-stability rule above, because "darker" and
    // "brighter" swap meaning with the ground: light darkens, dark brightens. It is *not* excluded from this
    // one. A hover is where the old defect was worst (`--accent-strong` at 1.80:1), so both values are
    // checked, and my own first dark hover pick was #3b74ee at **4.27** — plausible, and under the line.
    const base = readFileSync(join(__dirname, '../base.css'), 'utf8')
    const channel = (v: number) => {
      const x = v / 255
      return x <= 0.03928 ? x / 12.92 : ((x + 0.055) / 1.055) ** 2.4
    }
    const whiteInkRatio = (hex: string) => {
      const [r, g, b] = [1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16))
      const lum = 0.2126 * channel(r) + 0.7152 * channel(g) + 0.0722 * channel(b)
      return (1.05) / (lum + 0.05)
    }

    const tokens = ['accent-fill', 'accent-fill-hover', 'accent-fill-disabled',
      'danger-fill', 'danger-fill-hover', 'warning-fill', 'warning-fill-hover', 'success-fill']

    const failures: string[] = []
    for (const token of tokens) {
      const values = [...base.matchAll(new RegExp(`--${token}:\\s*(#[0-9a-f]{6})`, 'gi'))].map(m => m[1])
      expect(values.length, `--${token} should be declared in all three theme blocks`).toBe(3)
      for (const value of values) {
        const ratio = whiteInkRatio(value)
        if (ratio < 4.5) failures.push(`--${token}: ${value} gives white ink ${ratio.toFixed(2)}:1`)
      }
    }

    expect(failures).toEqual([])
  })

  it('keeps the device-runtime box from swallowing its own accent icon', () => {
    /*
     * A component's scoped CSS carries the `[data-v-…]` attribute, so a broad element selector inside it
     * outranks any global class rule — and `color: inherit` on a bare element name is as broad as it gets.
     *
     * `ControlCenter` had `.device-runtime-box span { color: inherit }` to neutralise the Tailwind slate
     * utilities its markup still carries. That also matched the one span asking for `board-text-accent`, so the
     * accent icon painted `rgb(148,163,184)` instead of the accent (measured; now 5.17:1 light / 4.91:1 dark
     * against the box). The defect is invisible from either side in review: the global rule looks correct and
     * the scoped rule looks like ordinary theme normalisation. Two attempted fixes failed before CDP
     * matched-styles named the winner — adding `.iot-board` for specificity did not help, and neither did
     * appending an identical rule last, because equal specificity was never the problem.
     *
     * This pins the one real instance rather than trying to detect the pattern generally. A general check needs
     * to prove DOM containment between a scoped ancestor and an ink-carrying element, which the two attempts
     * before this could not do from source text: both produced false positives on selectors that cannot meet
     * the inks they were accused of swallowing, and a guard that cries wolf is worse than none.
     */
    const control = readFileSync(join(COMPONENT_DIR, 'ControlCenter.vue'), 'utf8')
    expect(control, 'the accent icon should still be there to protect').toContain('board-text-accent')

    const at = control.indexOf('.device-runtime-box summary')
    expect(at, 'the runtime-box normaliser should exist').toBeGreaterThan(-1)
    const rule = control.slice(at, control.indexOf('}', at))
    expect(rule, 'the blanket span rule must exempt the role ink')
      .toMatch(/span:not\(\.board-text-accent\)/)
  })
})
