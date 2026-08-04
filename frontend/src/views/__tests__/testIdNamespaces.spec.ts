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
})
