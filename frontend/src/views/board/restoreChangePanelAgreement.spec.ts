import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * "Show step changes" must be offered only when the step-changes popover is actually gone.
 *
 * The two replay bars own the same control, and they disagreed. The simulation bar gates it on
 * `changePanelVisible === false`, bound from `showPlaybackChangePopover` — the condition itself. The
 * counterexample bar gated it on `playbackChangesDismissedKey !== null`, a proxy that answers a
 * different question: *has the user ever dismissed*, not *is it hidden now*.
 *
 * The two come apart because the dismissed key is `kind:stepIndex`, so it is scoped to one step by
 * design (dismissing at step 3 must not silence step 4). Dismiss at step 3 and scrub to step 4: the
 * popover returns, `showPlaybackChangePopover` goes true, and the key stays `counterexample:2`. The
 * proxy therefore left a button offering to restore a panel that was already on screen — beside it,
 * not instead of it — and it stayed there for the rest of the playback session, since only
 * `resetPlaybackChanges` clears the key.
 *
 * `!showPlaybackChangePopover` is the whole condition rather than a narrowing of the old one:
 * `activePlaybackChangeKey` is null only when there is no playback or no states, and
 * `validateTraceStatePayload` rejects an empty state list at the boundary while the bar's own `v-if`
 * requires a loaded run — so whenever this button can render at all, the computed reduces to
 * "dismissed at the step being viewed".
 *
 * Asserted by reading the source because `Board.vue` is not unit-mountable (no spec mounts it). The
 * assertions anchor on the two conditions and their `data-testid`s rather than on byte offsets, so an
 * unrelated edit nearby cannot redden them.
 */
describe('restore-change-panel agreement across the two replay bars', () => {
  const board = readFileSync(join(process.cwd(), 'src/views/Board.vue'), 'utf8')
  const simulationBar = readFileSync(
    join(process.cwd(), 'src/components/SimulationTimeline.vue'),
    'utf8'
  )

  /** The `v-if` on the `HintTooltip` wrapping a button with this test id. */
  const restoreButtonCondition = (source: string, testId: string): string => {
    const buttonIndex = source.indexOf(`data-testid="${testId}"`)
    expect(buttonIndex, `${testId} must exist`).toBeGreaterThan(-1)
    const tooltipIndex = source.lastIndexOf('<HintTooltip', buttonIndex)
    expect(tooltipIndex, `${testId} must be wrapped in a HintTooltip`).toBeGreaterThan(-1)
    const match = /v-if="([^"]+)"/.exec(source.slice(tooltipIndex, buttonIndex))
    expect(match, `${testId}'s tooltip must carry a v-if`).not.toBeNull()
    return match![1]
  }

  it('gates the counterexample bar on the popover being absent, not on a past dismissal', () => {
    const condition = restoreButtonCondition(board, 'trace-timeline-restore-changes')

    expect(condition).toBe('!showPlaybackChangePopover')
    // The specific proxy this replaced. Named so a revert reddens here with its reason attached.
    expect(condition).not.toContain('playbackChangesDismissedKey')
  })

  it('gates the simulation bar on the same condition, through its prop', () => {
    expect(restoreButtonCondition(simulationBar, 'simulation-timeline-restore-changes'))
      .toBe('changePanelVisible === false')

    // ...and that prop carries `showPlaybackChangePopover`, which is what makes the two bars agree
    // rather than merely look similar.
    const timelineTag = board.slice(
      board.indexOf('<SimulationTimeline'),
      board.indexOf('/>', board.indexOf('<SimulationTimeline')) + 2
    )
    expect(timelineTag).toContain(':change-panel-visible="showPlaybackChangePopover"')
  })

  it('keeps the dismissed key step-scoped, which is why the proxy could not stand in for it', () => {
    const keyStart = board.indexOf('const activePlaybackChangeKey = computed(')
    expect(keyStart).toBeGreaterThan(-1)
    const key = board.slice(keyStart, board.indexOf('})', keyStart))

    // The step index in the key is the whole reason the two conditions diverge: drop it and a
    // dismissal would silence every step, at which point the proxy would have been equivalent.
    expect(key).toContain('activePlaybackStateIndex.value')
    expect(key).toContain('activePlaybackKind.value')
  })
})
