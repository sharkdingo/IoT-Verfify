import type { RunPersistence } from '@/types/runPersistence'

/**
 * Which explanation an unavailable SMV model gets — the run's persistence status decides.
 *
 * `smvModelNotAvailable` tells the reader to check whether the run is still in their history, which is
 * only sound advice when the run was *saved*. Four `RunPersistenceStatus` values reach this notice, and
 * for three of them there is no history record to check and never will be: a run the user did not ask to
 * save, one whose save failed, and one whose save outcome is unconfirmed. Sending those users to history
 * names a cause that is not theirs and an action that cannot succeed.
 *
 * `OUTCOME_UNKNOWN` gets its own wording rather than folding into "not saved", because an unconfirmed
 * write is not a confirmed absence — the same distinction the Fix action already draws
 * (`verificationTracePersistenceUnknownFixUnavailable`), and one an unknown state must keep rather than
 * resolving to whichever side reads more simply.
 *
 * A status this client does not recognize falls through to `smvModelNotAvailable`: not knowing what a
 * status means is not evidence that nothing was saved, and the run-addressable wording is the one that
 * makes no claim about why.
 */
export const smvUnavailableReasonKey = (persistence?: Pick<RunPersistence, 'status'>): string => {
  switch (persistence?.status) {
    case 'OUTCOME_UNKNOWN':
      return 'app.smvModelPersistenceUnknown'
    case 'FAILED':
    case 'NOT_REQUESTED':
      return 'app.smvModelNotPersisted'
    default:
      return 'app.smvModelNotAvailable'
  }
}
