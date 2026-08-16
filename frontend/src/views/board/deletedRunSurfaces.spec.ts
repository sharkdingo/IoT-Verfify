import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * Deleting a run must close every surface still showing it.
 *
 * Found by behaviour, not by reading: run a sync verification, leave the result dialog open, delete that
 * run, then click its model download. Measured on the running app — the dialog stayed open, the download
 * stayed enabled, and the click answered *"SMV model not available (may be a record saved before model
 * persistence was enabled)"*. Two separate defects in one journey:
 *
 * 1. `deleteVerificationRun` removed the run from the history list and nothing else, so the dialog kept
 *    rendering a verdict, per-specification results and counterexample evidence for a record the server
 *    had already deleted — a result surface outliving its own run.
 * 2. That 404 message named a cause the client cannot know. The server's 404 covers *two* states, "the
 *    run is gone" and "the run stored no model", and the copy asserted the second as fact. So the
 *    explanation for a deletion one click old was a historical persistence limitation.
 *
 * Source-text assertions rather than a mounted render (`Board.vue` is far too large to mount cheaply,
 * per `actionDockHierarchy.spec.ts`).
 */
describe('surfaces for a deleted verification run', () => {
  const board = readFileSync(join(process.cwd(), 'src/views/Board.vue'), 'utf8')
  const i18n = readFileSync(join(process.cwd(), 'src/assets/i18n.ts'), 'utf8')

  it('tears down the open result and any replay of the deleted run', () => {
    const at = board.indexOf('const deleteVerificationRun')
    expect(at, 'the deletion handler should exist').toBeGreaterThan(-1)
    const body = board.slice(at, board.indexOf('\n}', board.indexOf('finally', at)))

    expect(body, 'deletion must invalidate the surfaces showing that run')
      .toContain('dismissRunSurfacesForDeletedVerificationRun(runId)')
    // After the server confirmed the delete, not before: an unconfirmed delete must leave the surface
    // alone, because the run may still exist.
    expect(body.indexOf('dismissRunSurfacesForDeletedVerificationRun'))
      .toBeGreaterThan(body.indexOf('await boardApi.deleteVerificationRun'))
  })

  it('matches on the run id, so deleting one run cannot close another run\'s surface', () => {
    const at = board.indexOf('const dismissRunSurfacesForDeletedVerificationRun')
    expect(at, 'the teardown helper should exist').toBeGreaterThan(-1)
    const body = board.slice(at, board.indexOf('\n}', at) + 2)

    // The dialog's run is identified by its persistence record; a playing counterexample by the run it
    // belongs to. Closing unconditionally would shut a dialog showing an unrelated run.
    expect(body, 'the open result is matched by its persisted run id')
      .toContain('historyPersistence?.runId')
    expect(body, 'a playing counterexample is matched through its owning run')
      .toContain('verificationTaskId')
    expect(body, 'both comparisons are against the deleted id')
      .toMatch(/=== runId/)

    // `dismissResultDialog`, not `closeResultDialog`: the deep link has to go too, or the URL sync
    // reopens the deleted run and then fails to load it.
    expect(body, 'the deep link must be cleared with the surface')
      .toContain('dismissResultDialog()')
    expect(body, 'and the replay teardown clears its own deep link via closeTraceAnimation')
      .toContain('closeTraceAnimation()')
    expect(body, 'stale evidence for the deleted run must not survive in savedTraces')
      .toContain('savedTraces.value = []')
  })

  it('reconciles the open result when the deletion happened somewhere else', () => {
    /*
     * `deleteVerificationRun` only covers deletions this tab performed, and the result dialog is
     * `aria-modal`, so the history panel is unreachable while it is open — meaning the same-tab path is
     * the *impossible* one. The reachable paths both arrive as a history reload:
     *
     *  - the assistant's `DeleteVerificationRunTool`, which emits `REFRESH_DATA run_history`
     *    (verified: `component/aitool/verification/DeleteVerificationRunTool.java` exists, and the chat
     *    toggle has layout while the dialog is open)
     *  - another tab deleting the run, whose invalidation lands in the same reload
     *
     * So the reconciliation has to hang off the reload, not off the delete handler.
     */
    const at = board.indexOf('const reconcileOpenRunAgainstHistory')
    expect(at, 'the reconciliation should exist').toBeGreaterThan(-1)
    const body = board.slice(at, board.indexOf('\n}', at) + 2)

    expect(body, 'it reuses the same teardown as an in-tab deletion')
      .toContain('dismissRunSurfacesForDeletedVerificationRun')
    expect(body, 'and tells the user why the surface closed')
      .toContain('openRunDeletedElsewhere')

    // The guard that keeps this from destroying a live verdict: an empty list is also what a
    // still-loading or scoped-empty history looks like, so only absence from a POPULATED list counts.
    expect(body, 'an empty history must not be read as "deleted"')
      .toContain('verificationRuns.value.length === 0')
    expect(body, 'and a run still present must be left alone')
      .toMatch(/some\(run => run\.id === openRunId\)/)

    // Wired to a *successful* reload only: a failed load leaves the lists stale, and treating that as a
    // deletion would close a surface over a transport error.
    //
    // Anchored on the full declaration: `indexOf('const refreshRunHistory')` matches the *chat adapter*
    // `refreshRunHistoryFromChat`, which is declared ~3500 lines earlier, so the window landed on the
    // wrong function entirely.
    const reloadAt = board.indexOf('const refreshRunHistory = async')
    const reload = board.slice(reloadAt, board.indexOf('\n}', reloadAt) + 2)
    expect(reload, 'reconciliation runs after the reload succeeded')
      .toMatch(/if \(results\.every\(Boolean\)\) reconcileOpenRunAgainstHistory\(\)/)
  })

  it('does not blame model persistence for a model the server simply does not have', () => {
    // The old copy asserted "may be a record saved before model persistence was enabled", which is one of
    // two possible causes and was stated for both. Naming a specific historical limitation is what made
    // it convincing enough that a user would not re-check their history.
    /*
     * Comment lines are stripped first, and that matters: the comment recording *why* the old wording was
     * wrong necessarily quotes it. Checking the raw file made this assertion fail on its own explanation —
     * the third time in this session that a guard matched a comment instead of the code it guards.
     */
    const strings = i18n
      .split('\n')
      .filter(line => !line.trim().startsWith('//') && !line.trim().startsWith('*'))
      .join('\n')
    expect(strings, 'the misleading persistence excuse must not return')
      .not.toContain('before model persistence was enabled')
    expect(strings, 'nor its Chinese equivalent').not.toContain('模型持久化功能上线前')
    // Both causes named, neither asserted, and an action the user can take.
    const at = i18n.indexOf('smvModelNotAvailable:', i18n.indexOf('smvModelNotAvailable:') + 1)
    const english = i18n.slice(at, at + 400)
    expect(english, 'names deletion as a possible cause').toMatch(/deleted/i)
    expect(english, 'names the modelless-record cause too').toMatch(/without one|no model/i)
    expect(english, 'and tells the user how to tell which').toMatch(/history/i)
  })
})
