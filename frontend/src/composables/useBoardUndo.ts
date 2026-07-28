import { onBeforeUnmount, onMounted, readonly, ref } from 'vue'

import boardApi from '@/api/board'
import type { BoardUndoResult } from '@/types/boardEdit'
import { resolveBoardUndoIntent, targetOwnsNativeUndo } from './boardUndoShortcut'

/**
 * Owns the board's undo/redo affordance: the keyboard accelerators, the in-flight guard, and the
 * availability the server reports.
 *
 * Deliberately holds **no history of its own**. The server journal is the authority for what is
 * reversible, and every result carries the authoritative rule and specification lists, so this
 * never has to invert an edit locally or reconcile a snapshot stack. That is also why `canUndo`
 * starts false: until the server has told us otherwise, we do not claim an edit is reversible.
 *
 * Scope boundaries this composable maintains:
 * - Undo reverses a *persisted board edit*. It does not cancel a run, close a dialog, dismiss a
 *   result, or navigate browser history — those have their own controls.
 * - Text fields, `contenteditable` editors, and active IME compositions keep native undo.
 */
export const useBoardUndo = (options: {
  /** Applies the authoritative post-operation collections to the board. */
  applyResult: (result: BoardUndoResult) => void
  /**
   * Runs the request through the caller's board-mutation queue.
   *
   * Undo is a board mutation and must serialize with the others: a delete still in flight when
   * Ctrl+Z fires would otherwise race it, and whichever response landed last would win
   * permanently — leaving the rule list and the undo affordance describing a server state that no
   * longer exists. `isApplying` only guards against a second *undo*, and the keyboard listener is
   * on `window`, so a disabled button cannot prevent this either.
   */
  submit: <T>(work: () => Promise<T>) => Promise<T>
  /**
   * Follow-ups the applied result owes beyond the collections themselves.
   *
   * Undo is a semantic scene change, so recommendations built on the pre-undo scene are stale. The
   * mutation queue's own scene-change hook cannot do this: undo passes `trackSemanticChange: false`
   * because the commit path already owns verification staleness.
   */
  onApplied?: () => void
  /**
   * True for a rejection that is a normal lifecycle outcome, not a failure to report — the board
   * unmounting or the auth scope changing while the request sat in the queue. Reporting those pops
   * an error toast on whatever page the user has moved to.
   */
  isIgnorableError?: (error: unknown) => boolean
  /** True while something else must not be interrupted (playback, scene replacement, a run). */
  isBlocked: () => boolean
  /** Called with a stable reason code so the caller owns all user-visible wording. */
  report: (
    reasonCode: 'blocked' | 'nothing' | 'conflict' | 'failed',
    direction: 'undo' | 'redo',
    error?: unknown
  ) => void
}) => {
  const canUndo = ref(false)
  const canRedo = ref(false)
  const isApplying = ref(false)
  // Bumped by every applied undo/redo. An availability read runs outside the mutation queue, so one
  // started before an undo could otherwise land after it and overwrite the post-undo availability
  // with the pre-undo journal state.
  let availabilityEpoch = 0

  /**
   * Mirrors the availability the server returned with an ordinary mutation.
   *
   * Reversible mutations report it; the rest omit it, and omitting must not silently clear a real
   * availability, so a missing value is ignored rather than treated as false.
   */
  const syncAvailability = (availability: { canUndo?: boolean, canRedo?: boolean }) => {
    if (typeof availability.canUndo === 'boolean') canUndo.value = availability.canUndo
    if (typeof availability.canRedo === 'boolean') canRedo.value = availability.canRedo
  }

  const apply = async (direction: 'undo' | 'redo') => {
    if (isApplying.value) return
    if (options.isBlocked()) {
      options.report('blocked', direction)
      return
    }

    isApplying.value = true
    try {
      const result = await options.submit(() => boardApi.applyBoardEditUndo(direction))
      availabilityEpoch += 1
      // Availability comes from the journal even when nothing was applied, so a stale local
      // guess is corrected rather than persisted.
      syncAvailability(result)
      if (!result.applied) {
        options.report('nothing', direction)
        return
      }
      options.applyResult(result)
      options.onApplied?.()
    } catch (error) {
      // A queued request can be rejected because the board went away, not because the undo failed.
      if (options.isIgnorableError?.(error)) return
      // A conflict means the record changed after the edit was recorded; the board is unchanged
      // and the caller must refresh rather than assume either state.
      const status = (error as { response?: { status?: number } })?.response?.status
      options.report(status === 409 ? 'conflict' : 'failed', direction, error)
      // A conflict leaves the entry in the journal, so availability is unchanged and the button stays
      // enabled — on an entry guaranteed to conflict again. Re-read it so the affordance reflects the
      // journal rather than inviting the user to loop on the same failure.
      if (status === 409) await loadAvailability()
    } finally {
      isApplying.value = false
    }
  }

  /**
   * Loads availability from the server, so a fresh page has the right affordance before the user
   * does anything. Failure is silent: the buttons simply stay disabled until a mutation reports
   * availability, which is the safe direction to be wrong in.
   */
  const loadAvailability = async () => {
    const epoch = availabilityEpoch
    try {
      const availability = await boardApi.getBoardEditAvailability()
      // A mutation landed while this was in flight; its availability is newer than ours.
      if (epoch !== availabilityEpoch) return
      syncAvailability(availability)
    } catch {
      // Leaving undo disabled never destroys work; claiming it is available might.
    }
  }

  const handleKeydown = (event: KeyboardEvent) => {
    if (targetOwnsNativeUndo(event.target)) return
    const intent = resolveBoardUndoIntent(event)
    if (!intent) return
    // Only claim the keystroke once we are sure it is ours, so the browser's own undo still
    // works everywhere we decline.
    event.preventDefault()
    void apply(intent)
  }

  onMounted(() => window.addEventListener('keydown', handleKeydown))
  onBeforeUnmount(() => window.removeEventListener('keydown', handleKeydown))

  return {
    canUndo: readonly(canUndo),
    canRedo: readonly(canRedo),
    isApplying: readonly(isApplying),
    loadAvailability,
    syncAvailability,
    undo: () => apply('undo'),
    redo: () => apply('redo')
  }
}
