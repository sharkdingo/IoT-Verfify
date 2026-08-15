import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A `data-testid` prefix is an interface, and overlapping prefixes make it ambiguous.
 *
 * `trace-timeline-state-{i}` names the per-step buttons on a counterexample rail. A `<details>` panel beside
 * it was called `trace-timeline-state-details`, so `[data-testid^="trace-timeline-state-"]` matched both.
 * Measuring a 27-state trace through that selector reported **28 steps, one 598px-wide "step", an
 * overlapping pair, and a step missing its accessible name** — four false findings from one name, each
 * plausible enough to chase. `SimulationTimeline` had the identical collision.
 *
 * The cost lands on whoever writes the next selector, which is why this belongs in a test rather than a
 * convention document.
 */

const DIRS = ['components', 'views']

const sources = () => {
  const files: Array<{ name: string, text: string }> = []
  for (const dir of DIRS) {
    const full = join(__dirname, '../..', dir)
    for (const entry of readdirSync(full, { withFileTypes: true })) {
      if (entry.isFile() && entry.name.endsWith('.vue')) {
        files.push({ name: `${dir}/${entry.name}`, text: readFileSync(join(full, entry.name), 'utf8') })
      }
    }
  }
  return files
}

describe('test-id namespaces', () => {
  it('never puts a static id inside an indexed family\'s prefix', () => {
    const staticIds: Array<{ id: string, where: string }> = []
    const indexedPrefixes = new Set<string>()

    for (const { name, text } of sources()) {
      for (const match of text.matchAll(/data-testid="([a-z0-9-]+)"/g)) {
        staticIds.push({ id: match[1], where: name })
      }
      // `:data-testid="`family-${expr}`"` declares the family `family`.
      for (const match of text.matchAll(/data-testid="`([a-z0-9-]+)-\$\{/g)) {
        indexedPrefixes.add(match[1])
      }
    }

    const collisions = staticIds
      .filter(({ id }) => [...indexedPrefixes].some((prefix) => {
        if (!id.startsWith(`${prefix}-`)) return false
        // A static id that the family itself can generate is the same element, not a collision:
        // `control-tab-${tab.id}` legitimately produces `control-tab-devices`. Only a *suffix that the
        // family could never emit* is ambiguous — in practice a descriptive word rather than a key.
        const suffix = id.slice(prefix.length + 1)
        return /^(details|panel|wrapper|container|list|header|footer|summary|body)$/.test(suffix)
      }))
      .map(({ id, where }) => `${where}: ${id}`)

    expect(collisions).toEqual([])
  })

  it('keeps the step-values panels outside the step families', () => {
    // The two that were wrong, pinned by name so a rename back is caught rather than re-measured.
    const board = readFileSync(join(__dirname, '../Board.vue'), 'utf8')
    const timeline = readFileSync(join(__dirname, '../../components/SimulationTimeline.vue'), 'utf8')

    expect(board).toContain('data-testid="trace-step-values"')
    expect(board).not.toContain('data-testid="trace-timeline-state-details"')
    expect(timeline).toContain('data-testid="simulation-step-values"')
    expect(timeline).not.toContain('data-testid="simulation-timeline-state-details"')
  })

  it('gives each playback timeline one x-axis control rather than two', () => {
    // The counterexample viewer and the simulation timeline both had a `<input type="range">` slider
    // labelled "jump to state" stacked directly above a clickable state rail, both full-width, both
    // horizontal, both mapping x-position to the same state index, both drawn in the same accent hue.
    // Two controls over one axis read as two timelines for a single sequence. The rail is the one that
    // cannot be replaced, because only it can show where the violation sits relative to where you are,
    // so the slider was deleted and the rail took over its drag capability via pointer capture.
    //
    // This guard locks the decision in place: if a range input reappears in either overlay, something
    // drifted back to the old shape.
    const board = readFileSync(join(__dirname, '../Board.vue'), 'utf8')
    const timeline = readFileSync(join(__dirname, '../../components/SimulationTimeline.vue'), 'utf8')

    // Scope by region, not by attribute order: the deleted slider carried its testid *before*
    // `type="range"`, so a pattern requiring that order could never match it back and the guard would
    // pass by construction. Comments are stripped for the same reason -- both files now describe the
    // slider they no longer render.
    const strip = (source: string) => source.replace(/<!--[\s\S]*?-->/g, '')

    // The counterexample overlay, from its host element to the panel that follows it.
    const boardMarkup = strip(board)
    const overlayStart = boardMarkup.indexOf('board-timeline-host--trace')
    expect(overlayStart, 'the trace overlay should be found').toBeGreaterThan(-1)
    const overlay = boardMarkup.slice(overlayStart, boardMarkup.indexOf('<SimulationTimeline', overlayStart))
    // The slice must actually contain the rail, or an empty window would assert nothing.
    const railAt = overlay.indexOf('data-testid="trace-timeline-track"')
    expect(railAt, 'the slice should contain the rail').toBeGreaterThan(-1)
    expect(overlay, 'the counterexample rail must be the only x-axis control')
      .not.toContain('type="range"')
    // Positive assertion: the rail itself must NOT be a range input, and must carry the expected
    // role. This catches a rename-and-reintroduce: if the rail were renamed to `trace-rail` and a
    // new `<input type="range" data-testid="trace-timeline-track">` appeared, the testid check would
    // pass but the element would be wrong.
    const railTag = overlay.slice(Math.max(0, railAt - 220), railAt + 280)
    expect(railTag, 'the rail must not be an input element').not.toContain('<input')
    expect(railTag, 'the rail must be a group with pointer interaction').toContain('role="group"')

    // Rail before the step values, matching the simulation timeline.
    //
    // The two rails had opposite reading orders: this one put the step's values above the rail, while
    // `SimulationTimeline.vue` puts the rail first. Nothing defended either choice, and the same
    // information in two sequences is the kind of drift a reader pays for without being able to name.
    // Navigate-then-read is the order the sibling surface already used, so it is the one that stands.
    const valuesAt = overlay.indexOf('data-testid="trace-step-values"')
    expect(valuesAt, 'the slice should contain the step values').toBeGreaterThan(-1)
    expect(railAt, 'the rail must precede the step values, as on the simulation timeline')
      .toBeLessThan(valuesAt)

    // The simulation timeline keeps its number input and +/-1 buttons: exact entry and discrete
    // stepping are a different modality, not a second x-axis. Scoped to the template, because the
    // script's own JSDoc names the deleted slider and `strip` only removes HTML comments -- matching
    // that prose is how this assertion first failed against correct markup.
    const timelineTemplate = strip(timeline.slice(timeline.indexOf('<template>')))
    const simRailAt = timelineTemplate.indexOf('data-testid="simulation-timeline-track"')
    expect(simRailAt, 'the simulation rail should be found').toBeGreaterThan(-1)
    expect(timelineTemplate, 'the simulation rail must be the only x-axis control')
      .not.toContain('type="range"')
    const simRailTag = timelineTemplate.slice(Math.max(0, simRailAt - 220), simRailAt + 280)
    expect(simRailTag, 'the simulation rail must not be an input element').not.toContain('<input')
    expect(simRailTag, 'the simulation rail must be a group with pointer interaction').toContain('role="group"')
  })
})
