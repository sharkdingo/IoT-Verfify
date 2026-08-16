import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A verdict that arrives after the board changed under it must arrive stale.
 *
 * `markVerificationResultStale` can only raise the flag on a result that *exists* — it reads
 * `verificationResult.value` / `lastSimulationResult.value` and returns early on null. Both run
 * paths null their result ref before submitting, so for the entire duration of a run there is
 * nothing to mark: a device edit, a rule change or an applied fix made while NuSMV is working
 * marked nothing at all. The completion paths then wrote `stale = false` unconditionally, so the
 * verdict presented itself as describing the canvas the user was now looking at — and kept offering
 * the per-counterexample Fix action, computed against a scene that no longer existed. That is the
 * one thing the repo's staleness rule exists to prevent.
 *
 * A watcher on the result ref cannot close this: the gap is precisely the window in which the ref
 * is null. The mechanism has to be a counter captured at submission and compared on arrival, which
 * is what this pins.
 *
 * It counts `semanticSceneChangeCount` rather than `boardMutationAdmissionEpoch` on purpose, and
 * the difference is load-bearing: the epoch counts *admitted mutations*, incremented before
 * `trackSemanticChange` is consulted, so the undo-history preview and clear advance it while
 * touching only the journal. Comparing that would mark a perfectly current verdict stale. The
 * counter increments inside `markVerificationResultStale` itself, so the two mechanisms cannot
 * disagree about what counts as a semantic change.
 *
 * Asserted over `Board.vue`'s source: the logic is inline in a component too large to mount
 * cheaply (see `actionDockHierarchy.spec.ts`), and extracting a comparison of one module-scoped
 * counter would need the reactive scope injected — the pass-through layer the frontend rules
 * forbid. `loopRangeAgreement.spec.ts` uses the same approach for the same reason.
 */
describe('a run that completes after the board changed', () => {
  const board = readFileSync(join(process.cwd(), 'src/views/Board.vue'), 'utf8')

  /** Strip comments before locating anything: this file explains the mechanism in prose beside it. */
  const stripComments = (source: string): string => source
    .replace(/\/\*[\s\S]*?\*\//g, '')
    .replace(/\/\/[^\n]*/g, '')

  /** Comment-free source, so a brace scan cannot be thrown off by prose or by commented-out code. */
  const code = stripComments(board)

  /**
   * One named function body, delimited by matching braces from its arrow.
   *
   * Cutting at the next `\n}` instead is what a first draft did, and it silently produced a body
   * containing only the signature: `handleSimulate` declares a multi-line inline parameter type
   * whose closing `}` sits in column 0. Every assertion then ran against the wrong text, and the
   * failure blamed the code rather than the extractor.
   */
  const bodyOf = (declaration: string): string => {
    const at = code.indexOf(declaration)
    expect(at, `${declaration} should exist in Board.vue`).toBeGreaterThan(-1)
    const open = code.indexOf('=> {', at)
    expect(open, `${declaration} should be an arrow function`).toBeGreaterThan(at)

    let depth = 0
    for (let index = open + 3; index < code.length; index++) {
      if (code[index] === '{') depth += 1
      else if (code[index] === '}') {
        depth -= 1
        if (depth === 0) return code.slice(at, index + 1)
      }
    }
    throw new Error(`${declaration} has unbalanced braces`)
  }

  it('counts semantic changes from the hook that owns the staleness rule', () => {
    const hook = bodyOf('const markVerificationResultStale = ')
    expect(hook, 'the counter must advance from the same callback that flags an open result')
      .toMatch(/semanticSceneChangeCount \+= 1/)
    // The epoch counts admitted mutations, which includes journal-only operations. Using it here
    // would mark a current verdict stale after an undo-history preview.
    expect(hook, 'the counter is not the mutation-admission epoch')
      .not.toContain('boardMutationAdmissionEpoch')
  })

  /*
   * Every function that awaits a run and then writes a staleness flag. `watchSimulationTask` is the
   * one reached from the task inbox, which is when a user is most likely to keep editing; it had the
   * same unconditional `false` as the others. `watchVerificationTask` is absent on purpose — it
   * delegates to `pollAsyncVerification`, which owns the capture, so a second one there would
   * measure the wrong window.
   */
  it.each([
    ['const handleVerify = ', 'verificationResultStale'],
    ['const handleSimulate = ', 'simulationResultStale'],
    ['const pollAsyncVerification = ', 'verificationResultStale'],
    ['const watchSimulationTask = ', 'simulationResultStale']
  ])('%s captures the counter at submission and compares it on arrival', (declaration, flag) => {
    const body = bodyOf(declaration)

    // The trailing `$` matters: without it this also matches the *comparison*
    // (`const boardChangedDuringRun = semanticSceneChangeCount !== …`), so the count came out at 2
    // and the captured name was the comparison's.
    const captures = [...body.matchAll(/const (\w+) = semanticSceneChangeCount$/gm)]
    expect(captures, `${declaration} must snapshot the counter before awaiting the run`)
      .toHaveLength(1)
    const captured = captures[0][1]

    // The comparison must reach the flag. Asserting only that a comparison exists somewhere would
    // pass on a captured value that is computed and then dropped.
    const comparison = new RegExp(`semanticSceneChangeCount !== ${captured}`)
    expect(body, `${declaration} must compare the counter across the run`).toMatch(comparison)

    // Every write of the flag that happens *after* the capture must be derived from the comparison
    // rather than a bare `false`. Writes before the capture are the pre-submission reset, which is
    // legitimate — and which lives in `handleVerify`/`handleSimulate` but not in
    // `pollAsyncVerification`, so the count of writes differs by path and cannot be asserted.
    const captureAt = body.search(/const \w+ = semanticSceneChangeCount$/m)
    const arrivalWrites = [...body.matchAll(new RegExp(`${flag}\\.value =([^\\n]*)`, 'g'))]
      .filter(match => (match.index ?? 0) > captureAt)
    expect(arrivalWrites.length, `${declaration} should write ${flag} on arrival`).toBeGreaterThan(0)
    for (const write of arrivalWrites) {
      expect(write[1].trim(), `${flag} must not be forced current after the run completed`)
        .not.toBe('false')
    }
  })

  it('leaves a freshly loaded historical run current', () => {
    // The counter answers "did the board change while *this* run was in flight". A run read back
    // from history was not in flight, so its flag stays a plain `false` — comparing a counter there
    // would make the banner depend on unrelated editing history. Pinned so the mechanism above is
    // not spread onto paths it does not describe.
    const open = bodyOf('const openVerificationRun = ')
    expect(open, 'a history read is not a run in flight').toContain('verificationResultStale.value = false')
    expect(open, 'and needs no counter comparison').not.toContain('semanticSceneChangeCount')
  })
})
