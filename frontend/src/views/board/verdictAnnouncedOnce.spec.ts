import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

/**
 * A verdict is announced once, by the surface that owns it.
 *
 * `utils/feedback.ts` states the rule: "a success whose result is already visible on screen gets no
 * toast at all." `presentFuzzingRun` had applied it for years, calling `dismissAllNotifications()` with
 * the note that transient notices must not cover the result's title or primary actions. Verification
 * had not: `showResultDialog` derives from `verificationResult`, so setting the result opened the dialog
 * and then toasted the same fact over it — measured in a browser as a toast reading "Found 1
 * specification violation(s)" covering a dialog subtitled "Found 1 violation(s)".
 *
 * The toast is still wanted when nothing on screen carries the verdict — an async run finishing while
 * the user is elsewhere — so the guard is per-call-site, not a blanket removal. Text assertions over the
 * source, as `actionDockHierarchy.spec.ts` records, because `Board.vue` is far too large to mount.
 */
describe('verification verdict is announced once', () => {
  const board = readFileSync(join(process.cwd(), 'src/views/Board.vue'), 'utf8')

  it('suppresses the outcome toast at every call site that also opens the dialog', () => {
    const calls = [...board.matchAll(/notifyVerificationOutcome\(([^)]*)\)/g)]
      .map(match => match[1])
      // The declaration itself is not a call.
      .filter(args => !args.startsWith('result: any'))

    expect(calls.length, 'the outcome notifier should still be called').toBeGreaterThan(1)

    // A call that passes `verificationResult.value` is presenting: that assignment is what opens the
    // dialog. Such a call must carry the suppression flag.
    const presenting = calls.filter(args => args.includes('verificationResult.value'))
    expect(presenting.length, 'the presenting call sites should exist').toBeGreaterThan(0)
    for (const args of presenting) {
      expect(args, 'a call that opens the dialog must not also toast the verdict')
        .toContain('presenting: true')
    }

    // And at least one call must NOT suppress, or the background-completion notice is gone entirely.
    expect(
      calls.some(args => !args.includes('presenting: true')),
      'a run completing while the user is elsewhere must still be announced'
    ).toBe(true)
  })

  it('keeps the guard independent of declaration order', () => {
    // `showResultDialog` is declared ~11k lines below the notifier. Reading it there would work only
    // because every current caller runs on user action, long after setup — a property no reader can see
    // from the notifier itself, in a file where things move.
    const at = board.indexOf('const notifyVerificationOutcome')
    expect(at).toBeGreaterThan(-1)
    // Comments stripped: the explanation beside the guard names `showResultDialog` in order to say why
    // it is *not* read, so matching raw text here would fail on its own rationale.
    const body = board.slice(at, at + 900).replace(/\/\/[^\n]*/g, '').replace(/\/\*[\s\S]*?\*\//g, '')
    expect(body, 'the guard must come from its argument, not a far-below computed')
      .not.toContain('showResultDialog')
    expect(body).toContain('options.presenting')
  })

  it('does not suppress the separate persistence-failure notice', () => {
    // A save that did not happen is not a fact the verdict dialog states, so it keeps its own toast.
    expect(board).toMatch(/verificationHistorySaveOutcomeUnknown|verificationHistorySaveFailed/)
  })
})
