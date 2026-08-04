import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Structural rules for text that must stay readable.
 *
 * These pin the shape of fixes that took six passes to land, because the defect they prevent is
 * invisible in a diff and invisible in a unit test: a name given 23px of the 102px it needs still
 * renders, still has its `title`, and still passes every assertion about its content.
 *
 * The measurements behind each rule live in `.audit/LEDGER.md`; the point here is that a later edit
 * cannot quietly reintroduce the layout that caused them.
 */

const read = (relative: string) =>
  readFileSync(join(__dirname, '..', relative), 'utf8')

describe('label legibility', () => {
  it('gives the device name its own line rather than a share of the row', () => {
    const source = read('SystemInspector.vue')
    const nameAt = source.indexOf(':data-full-text="device.name"')
    expect(nameAt).toBeGreaterThan(-1)
    const row = source.slice(nameAt - 1400, nameAt + 1600)

    // The button stacks: name on one line, qualifier chips on the next.
    expect(row).toContain('flex-col')
    // Both qualifiers live below the name rather than beside it.
    expect(row).toContain(':data-full-text="device.type"')
    expect(row).toContain(':data-full-text="device.state"')
    // The name must not carry `flex-1`: that is `flex-basis: 0`, so it entered every squeeze at zero
    // width and grew only from what the chips left over — measured at 23px of the 102px
    // "Air Conditioner" needs.
    const nameSpan = source.slice(source.lastIndexOf('<span', nameAt), nameAt)
    expect(nameSpan).not.toContain('flex-1')
  })

  it('sizes the template grid by available width, not a fixed column count', () => {
    const source = read('ControlCenter.vue')
    const grid = source.slice(
      source.indexOf('template-group__grid'),
      source.indexOf('template-group__grid') + 200
    )

    // `grid-cols-2` in a 320px panel left each title 51px regardless of the name; one needed 217px.
    expect(grid).not.toMatch(/grid-cols-2\b/)
    expect(grid).toContain('auto-fill')
  })

  it('wraps guidance sentences instead of truncating them to a fragment', () => {
    const source = read('ControlCenter.vue')
    const hint = source.slice(
      source.indexOf('app.deviceTemplateSchemaHint') - 700,
      source.indexOf('app.deviceTemplateSchemaHint') + 200
    )

    // A name's prefix still identifies it; a sentence cut at 26% breaks off mid-word.
    expect(hint).toContain('line-clamp-3')
    expect(hint).not.toMatch(/class="[^"]*\btruncate\b[^"]*"[^>]*>\s*\{\{ t\('app\.deviceTemplateSchemaHint'\)/)
  })

  it('drops the inspector tab icon before the label that names the section', () => {
    const source = read('SystemInspector.vue')

    // Derived from the panel's own resizable width (240–520px), never the viewport: a viewport query
    // would hide the icon on a wide screen with a narrow panel and show it on the reverse.
    expect(source).toMatch(/const tabIconsFit = computed\(\(\) => resolvedPanelWidth\.value >= \d+\)/)
    const tabAt = source.indexOf('role="tab"')
    const tabButton = source.slice(tabAt, tabAt + 2200)
    expect(tabButton).toContain('v-if="tabIconsFit"')
    // The label itself is never conditional — it is what identifies the section.
    expect(tabButton).toContain(':data-full-text="tab.label"')
    expect(tabButton).not.toMatch(/v-if="tabIconsFit"[^>]*>\{\{ tab\.label \}\}/)
  })
})
