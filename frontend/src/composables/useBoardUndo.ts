import { onBeforeUnmount, onMounted, readonly, ref } from 'vue'

import boardApi from '@/api/board'
import type { BoardUndoResult } from '@/types/boardEdit'
import { resolveBoardUndoIntent, targetOwnsNativeUndo } from './boardUndoShortcut'

/**
 * Owns the board's undo/redo affordance: the keyboard accelerators, the in-flight guard, and the
 * availability the server reports.
 *
 * Deliberately holds **no history of its own**. The server journal is the authority for what is
 * reversible, and every applied result carries all four authoritative semantic collections, so
 * this never has to invert an edit locally or reconcile a snapshot stack. That is also why
 * `canUndo` starts false: until the server has told us otherwise, we do not claim an edit is
 * reversible.
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
  /** Reconciles an unconfirmed or conflicted request through the same mutation queue. */
  reconcile: () => Promise<boolean>
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
    error?: unknown,
    reconciled?: boolean
  ) => void
}) => {
  const canUndo = ref(false)
  const canRedo = ref(false)
  const isApplying = ref(false)
  // Bumped by every applied undo/redo. An availability read runs outside the mutation queue, so one
  // started before an undo could otherwise land after it and overwrite the post-undo availability
  // with the pre-undo journal state.
  let availabilityEpoch = 0
  // Latest-started read wins among reads from the same mutation epoch. Without this, two foreground
  // refreshes can complete out of order and let the older request overwrite the newer one.
  let availabilityReadSequence = 0

  const assignAvailability = (availability: { canUndo?: boolean, canRedo?: boolean }) => {
    if (typeof availability.canUndo === 'boolean') canUndo.value = availability.canUndo
    if (typeof availability.canRedo === 'boolean') canRedo.value = availability.canRedo
  }

  /**
   * Mirrors the availability the server returned with an ordinary mutation.
   *
   * Reversible mutations report it; the rest omit it, and omitting must not silently clear a real
   * availability, so a missing value is ignored rather than treated as false.
   */
  const syncAvailability = (availability: { canUndo?: boolean, canRedo?: boolean }) => {
    if (typeof availability.canUndo !== 'boolean'
      && typeof availability.canRedo !== 'boolean') return
    // This is called by authoritative mutation responses. Invalidate every availability read that
    // began before the mutation committed, including reads raced by ordinary edits rather than only
    // undo/redo itself.
    availabilityEpoch += 1
    assignAvailability(availability)
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
      // The request may have committed despite the rejected response. Invalidate availability reads
      // started before it just as a confirmed mutation would.
      availabilityEpoch += 1
      const status = (error as { response?: { status?: number } })?.response?.status
      // A 409 proves this request made no write, but also proves the local board may be stale. Every
      // other failure is less certain: the server may have committed before the response was lost or
      // rejected by the client contract parser. Reconcile both through the mutation queue before
      // describing the outcome, and never claim the board was unchanged when it is unknown.
      const reconciled = await options.reconcile().catch(() => false)
      await loadAvailability()
      options.report(status === 409 ? 'conflict' : 'failed', direction, error, reconciled)
    } finally {
      isApplying.value = false
    }
  }

  /**
   * Loads availability from the server, so a fresh page has the right affordance before the user
   * does anything. Failure is silent and preserves the last confirmed values; inventing either
   * availability or unavailability would misdescribe server history.
   */
  const loadAvailability = async () => {
    const epoch = availabilityEpoch
    const readSequence = ++availabilityReadSequence
    try {
      const availability = await boardApi.getBoardEditAvailability()
      // A mutation landed while this was in flight, or a later refresh was already requested.
      if (epoch !== availabilityEpoch || readSequence !== availabilityReadSequence) return
      assignAvailability(availability)
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
