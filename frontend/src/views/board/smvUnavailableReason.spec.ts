import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

import { smvUnavailableReasonKey } from './smvUnavailableReason'

/**
 * An unavailable SMV model must not blame the wrong cause.
 *
 * The single message this notice used to render told every reader to "check whether the run is still in
 * your history". That is sound only for a run that was saved. Three of the four `RunPersistenceStatus`
 * values reach the same notice with no history record to check and none forthcoming — the user did not
 * ask to save, the save failed, or its outcome is unconfirmed — so the advice named a cause that was not
 * theirs and an action that could not succeed.
 */
describe('SMV unavailable reason', () => {
  it('sends a saved run to its history record', () => {
    expect(smvUnavailableReasonKey({ status: 'SAVED' })).toBe('app.smvModelNotAvailable')
  })

  it('does not send an unsaved run to a history record it will never have', () => {
    expect(smvUnavailableReasonKey({ status: 'NOT_REQUESTED' })).toBe('app.smvModelNotPersisted')
    expect(smvUnavailableReasonKey({ status: 'FAILED' })).toBe('app.smvModelNotPersisted')
  })

  it('keeps an unconfirmed write distinct from a confirmed absence', () => {
    // The whole point of `OUTCOME_UNKNOWN`: the client does not know whether the row exists. Reporting
    // it as "not saved" would resolve an unknown into a fact the client cannot support.
    expect(smvUnavailableReasonKey({ status: 'OUTCOME_UNKNOWN' }))
      .toBe('app.smvModelPersistenceUnknown')
  })

  it('treats an unrecognized or absent status as making no claim about why', () => {
    // Not knowing what a status means is not evidence that nothing was saved, so this falls through to
    // the wording that does not assert a cause.
    expect(smvUnavailableReasonKey({ status: 'SOMETHING_NEW' } as never))
      .toBe('app.smvModelNotAvailable')
    expect(smvUnavailableReasonKey(undefined)).toBe('app.smvModelNotAvailable')
  })

  it('every key it can return is defined in both locales', () => {
    /*
     * A reason key that resolves to nothing renders as the raw `app.…` literal — the exact failure the
     * user reported for the verification result panel. Asserting over the i18n source rather than
     * importing it, because these are nested object literals and both locales must be checked
     * separately; a missing key in one language only shows up when the interface is in that language.
     */
    const i18n = readFileSync(join(process.cwd(), 'src/assets/i18n.ts'), 'utf8')
    const keys = [
      'smvModelNotAvailable',
      'smvModelNotPersisted',
      'smvModelPersistenceUnknown'
    ]
    for (const key of keys) {
      const occurrences = i18n.split(`${key}:`).length - 1
      expect(occurrences, `${key} should be declared in zh-CN and en`).toBe(2)
    }
  })
})
