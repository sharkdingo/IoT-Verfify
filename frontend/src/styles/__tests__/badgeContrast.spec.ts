import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A count badge on a filled tab must darken its ground, not lighten it.
 *
 * Measured on a 12-device board: the active inspector tab badge used `bg-white/20 text-white`, putting white text on
 * the accent fill lightened by 20% white — **3.62:1**, under the 4.5 floor that applies because the text is 11px.
 * Lightening a fill and then writing white on it moves both sides toward each other, so the intuitive "fix" of
 * `white/30` is worse still (3.02:1). `black/20` darkens the same fill: **7.24:1**.
 *
 * Two things make this worth pinning rather than just fixing.
 *
 * First, `white/N` on a filled control is a genuinely tempting pattern — it looks like a subtle recess, it works
 * against dark fills, and it fails silently against mid-tone ones. Nothing else in the suite would catch it.
 *
 * Second, it took **density** to surface. The count is the badge's entire purpose: it is how a reader knows a section
 * holds twelve devices without opening it. With two devices the digit is easy to overlook, which is why a dozen prior
 * contrast sweeps on 2-device boards all reported clean.
 *
 * The inactive badge measures 4.54:1 and is deliberately left alone. I changed it first, on a class-name guess, before
 * reading the computed colours — the measurement is what identified the active badge as the real offender.
 */

const inspector = () => readFileSync(join(__dirname, '../../components/SystemInspector.vue'), 'utf8')

describe('badge contrast', () => {
  const withoutComments = (text: string) => text.replace(/<!--[\s\S]*?-->/g, '')

  it('darkens the active count badge rather than lightening it', () => {
    const source = withoutComments(inspector())
    // Anchor on the badge's own class, not on the first `activeSection === tab.id`: that binding belongs to the tab
    // button's styling and appears earlier in the file, so slicing from it read the wrong element entirely.
    const badgeAt = source.indexOf('shrink-0 rounded-full px-1.5 py-0.5')
    expect(badgeAt, 'the count badge should exist').toBeGreaterThan(-1)
    const binding = source.slice(badgeAt, badgeAt + 260)

    expect(binding, 'the active badge should darken its ground').toMatch(/bg-black\/\d+/)
    expect(binding, 'lightening the ground puts white text on a near-white fill')
      .not.toMatch(/bg-white\/\d+/)
  })

  it('keeps the inactive badge at a readable slate pair', () => {
    // The inactive badge sits on a light surface, so it needs a dark enough foreground rather than a darker ground.
    // slate-600 measures 6.15:1 nominal on slate-200; slate-500 would be 3.86:1.
    const source = withoutComments(inspector())
    const badgeAt = source.indexOf('shrink-0 rounded-full px-1.5 py-0.5')
    const binding = source.slice(badgeAt, badgeAt + 260)
    expect(binding, 'the inactive badge should use slate-600, not slate-500')
      .toMatch(/text-slate-600/)
    expect(binding, 'slate-500 on slate-200 is 3.86:1, under the 4.5 floor for this 11px text')
      .not.toMatch(/bg-slate-200 text-slate-500/)
  })

  it('never reintroduces a translucent white fill under white text anywhere in the panel', () => {
    // The sibling sweep. `bg-white/N` paired with `text-white` is the shape of the defect, wherever it appears —
    // scanning the whole file keeps a second instance from being added elsewhere and going unnoticed.
    const source = withoutComments(inspector())
    const offenders: string[] = []
    source.split('\n').forEach((line, index) => {
      if (/bg-white\/\d+/.test(line) && /text-white/.test(line)) {
        offenders.push(`SystemInspector.vue:${index + 1}`)
      }
    })
    expect(offenders, 'white text on a translucent white fill cannot reach 4.5:1 over a mid-tone accent')
      .toEqual([])
  })
})
