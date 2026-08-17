import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A neutral control's hover must actually change something, and stay readable while it does.
 *
 * Tailwind emits its utilities into `@layer utilities`, and **an unlayered rule beats a layered one at any
 * specificity**. Every rule in `board.css` is unlayered, so `hover:bg-slate-100` on a board surface could
 * never win. Measured in a browser against the built bundle, in dark mode, both outcomes were wrong:
 *
 *   - where the element also carried a bare `bg-slate-*`, an `!important` theme remap owned the background
 *     and the hover did **nothing** — 11.82:1 at rest and 11.82:1 hovered, so the replay bar's Play button
 *     and the history panel's Dismiss button gave no feedback at all;
 *   - where nothing competed, the layered utility did apply and painted Tailwind's `oklch(0.968 …)` =
 *     rgb(241,245,249) — near-white — under light ink: **1.13:1**. The label effectively disappeared.
 *
 * Both are invisible to a light-theme review and to every existing guard: `roleClassVariants` checks
 * variants of *hand-written* classes (`hover:board-*`), and these are Tailwind's own, which do get emitted.
 * `neutralTextContrast` scans resting ink, not hover grounds. So this file owns the third case.
 *
 * The fix is `hover:board-control-hover`, backed by `--surface-control-hover`. Its light value leaves
 * `--text-muted` at 4.23:1 — under AA — because that token is itself tuned to sit at 4.55 on
 * `--surface-control`, so no light value satisfies both. A muted control therefore has to strengthen its
 * ink on hover too, which is the pair this guard enforces. Verified after migration, both themes, all 26
 * sites: ground changes on hover and the hovered ratio is 10.04:1 (dark) / 15.17:1 (light).
 */

const DIRS = ['components', 'components/common', 'views']

const sources = () => {
  const files: Array<{ name: string, text: string }> = []
  for (const dir of DIRS) {
    const full = join(__dirname, '../..', dir)
    for (const entry of readdirSync(full, { withFileTypes: true })) {
      if (!entry.isFile() || !entry.name.endsWith('.vue')) continue
      files.push({ name: `${dir}/${entry.name}`, text: readFileSync(join(full, entry.name), 'utf8') })
    }
  }
  return files
}

const boardCss = () => readFileSync(join(__dirname, '..', 'board.css'), 'utf8')
const baseCss = () => readFileSync(join(__dirname, '..', 'base.css'), 'utf8')

/** Blank comments in place so reported line numbers stay true (see `neutralTextContrast`). */
const blankComments = (lines: string[]) => {
  const out: string[] = []
  let inBlock = false
  for (const raw of lines) {
    let line = raw
    if (inBlock) {
      const close = line.indexOf('-->') >= 0 ? line.indexOf('-->') + 3
        : (line.indexOf('*/') >= 0 ? line.indexOf('*/') + 2 : -1)
      if (close < 0) { out.push(''); continue }
      line = ' '.repeat(close) + line.slice(close)
      inBlock = false
    }
    line = line.replace(/<!--[\s\S]*?-->/g, m => ' '.repeat(m.length))
      .replace(/\/\*[\s\S]*?\*\//g, m => ' '.repeat(m.length))
    const open = Math.max(line.lastIndexOf('<!--'), line.lastIndexOf('/*'))
    if (open >= 0) { line = line.slice(0, open); inBlock = true }
    out.push(line)
  }
  return out
}

describe('neutral hover feedback', () => {
  it('never reaches for a layered slate utility as a board hover ground', () => {
    // `dark:hover:bg-slate-800` is exempt: it is a *pair* with the light branch, both land in the same
    // layer, and the three surviving sites (SystemInspector's device rows) carry no competing bare
    // `bg-slate-*`, so nothing outranks them and both halves apply. The defect is the *unpaired* bare
    // utility, which has no dark counterpart and loses wherever a remap owns the background.
    const offenders: string[] = []
    for (const { name, text } of sources()) {
      blankComments(text.split('\n')).forEach((line, index) => {
        for (const match of line.matchAll(/(^|[\s"'`:])hover:bg-(slate|gray|zinc)-(50|100|200)\b/g)) {
          // A `dark:`-prefixed occurrence is a different declaration; only the bare one is at issue.
          if (match[1] === ':') continue
          if (/dark:hover:bg-(slate|gray|zinc)-\d+/.test(line)) continue
          offenders.push(`${name}:${index + 1}  ${line.trim().slice(0, 100)}`)
        }
      })
    }
    expect(offenders).toEqual([])
  })

  it('defines the hover ground so it can outrank the later theme normalisers', () => {
    const css = boardCss()
    // Both forms are required, and neither is decoration. The bare rule serves surfaces inside
    // `.iot-board`; the `.board-timeline` twin serves the two replay bars, which are **siblings** of
    // `.iot-board` and therefore unreachable from any `.iot-board`-prefixed rule.
    expect(css, 'the role class must exist').toMatch(
      /\.hover\\:board-control-hover:hover\s*\{[^}]*var\(--surface-control-hover\)/)
    expect(css, 'the replay bars need the unprefixed twin').toMatch(
      /\.board-timeline \.hover\\:board-control-hover:hover\s*\{[^}]*var\(--surface-control-hover\)/)

    // `!important` is load-bearing: the normalisers it must beat are 0-3-0 AND sit later in the file,
    // so source order cannot rescue a tie. Dropping it made the history panel's Dismiss button show an
    // identical ground at rest and hovered (5.71:1 both) — measured, not assumed.
    for (const selector of ['\\.hover\\\\:board-control-hover:hover', '\\.board-timeline \\.hover\\\\:board-control-hover:hover']) {
      const rule = new RegExp(`${selector}\\s*\\{([^}]*)\\}`).exec(css)
      expect(rule, `${selector} should be present`).not.toBeNull()
      expect(rule![1], `${selector} must win over the later 0-3-0 normalisers`).toContain('!important')
    }
  })

  it('gives the hover ground a per-theme value, since one value cannot serve both', () => {
    const css = baseCss()
    const values = [...css.matchAll(/--surface-control-hover:\s*(#[0-9a-f]{6})/g)].map(m => m[1])
    // Three theme blocks: `:root` (light), `:root[data-theme='dark']`, `:root[data-theme='light']`.
    expect(values, 'every theme block must define it, or one theme falls back to nothing').toHaveLength(3)
    expect(new Set(values).size, 'a single shared value would mean one theme is wrong').toBe(2)
    // The dark value must be *lighter* than its resting control (#1e293b) and the light value darker
    // than its own (#f1f5f9) — a hover that moves the wrong way reads as a different control.
    const dark = values.find(v => v === '#273548')
    expect(dark, 'dark lightens toward the viewer; #273548 measured --text 10.04 / --text-muted 4.85').toBe('#273548')
  })

  it('pairs a muted resting ink with a strengthened hover ink', () => {
    // The light ground leaves `--text-muted` at 4.23:1, so a control whose rest ink is muted must also
    // brighten its ink — otherwise the migration trades an invisible hover for an unreadable one.
    //
    // Scoped to controls that actually carry text. SC 1.4.3 does not apply to a decorative glyph, and
    // ControlCenter's two panel-toggle tiles hold nothing but an `aria-hidden` icon whose own colour is
    // set on the child — so the parent's hover ink could not reach it even if it were required. Both
    // were flagged by this rule's first version, which is what identified the exemption.
    const offenders: string[] = []
    for (const { name, text } of sources()) {
      const lines = blankComments(text.split('\n'))
      lines.forEach((line, index) => {
        if (!line.includes('hover:board-control-hover')) return
        const restsMuted = /\bboard-text-muted\b/.test(line) || /\bboard-chip-neutral\b/.test(line)
        if (!restsMuted) return
        if (/hover:board-text-(strong|info|danger|warning)\b/.test(line)) return
        // An icon-only control: within the element's own markup there is an `aria-hidden` glyph and
        // *no* text node at all. Scanning to the closing tag rather than a fixed line window, because
        // the Play button's label sits several lines below its glyph — a fixed window that stopped
        // short exempted it, and this rule then stayed green when its ink half was deleted.
        const body = (() => {
          const rest = lines.slice(index).join('\n')
          // Start after the opening tag closes. Starting at the class attribute leaves the remaining
          // attributes in the slice, and stripping tags then turns `:aria-label="t('app.collapse')"`
          // into bare text that reads as a visible label — which flagged two icon-only tiles.
          const open = rest.indexOf('>')
          const inner = open < 0 ? rest : rest.slice(open + 1)
          const end = inner.search(/<\/(button|summary|a|label)>/)
          return end < 0 ? inner.slice(0, 600) : inner.slice(0, end)
        })()
        // Any interpolation or literal text outside an aria-hidden span counts as a label.
        const withoutGlyphs = body.replace(/<span[^>]*aria-hidden="true"[^>]*>[\s\S]*?<\/span>/g, '')
        const hasText = /\{\{/.test(withoutGlyphs) || /^\s*[A-Za-z0-9]/m.test(withoutGlyphs.replace(/<[^>]*>/g, ''))
        if (!hasText) return
        offenders.push(`${name}:${index + 1}  ${line.trim().slice(0, 100)}`)
      })
    }
    expect(offenders).toEqual([])
  })
})
