import { onBeforeUnmount, readonly, ref, watch, type Ref } from 'vue'

/**
 * Prevents the page behind an open modal from scrolling.
 *
 * Reference-counted because modals nest (a confirmation opened from a dialog): the lock
 * is released only when the last owner closes, and the original `overflow` value is
 * restored rather than assumed to be `visible`.
 */
let lockCount = 0
let restoreOverflow: string | null = null
const openModalCount = ref(0)

/**
 * How many modal surfaces are currently open.
 *
 * Exposed because a `window`-level keyboard accelerator cannot tell on its own that a dialog is
 * covering the board: `event.target` is the modal's own button, which owns no native undo, so the
 * keystroke leaks through to the surface behind it.
 *
 * Registration is deliberately separate from the scroll lock. Element Plus `MessageBox`
 * confirmations (`utils/feedback.ts`) are modal for the user but pass `lockScroll: false`, because
 * the board shell is a fixed `100vh` surface that Element Plus's scrollbar compensation would
 * shift — so they must count here without taking the lock. Wiring depth to the lock alone left
 * every `confirmDestructive` window unguarded.
 */
export const openModalDepth = readonly(openModalCount)

/**
 * Registers a modal surface that manages its own scrolling, and returns the release function.
 *
 * For surfaces outside the Vue component lifecycle (an awaited `MessageBox`), where a composable
 * with `onBeforeUnmount` does not apply.
 */
export const registerModalSurface = (): (() => void) => {
  openModalCount.value += 1
  let released = false
  return () => {
    // Idempotent: a confirmation can settle through confirm, cancel, or dismiss, and the caller
    // releases in a `finally` that must not double-decrement.
    if (released) return
    released = true
    openModalCount.value = Math.max(0, openModalCount.value - 1)
  }
}

const acquire = () => {
  openModalCount.value += 1
  if (typeof document === 'undefined') return
  if (lockCount === 0) {
    restoreOverflow = document.body.style.overflow
    document.body.style.overflow = 'hidden'
  }
  lockCount += 1
}

const release = () => {
  openModalCount.value = Math.max(0, openModalCount.value - 1)
  if (typeof document === 'undefined' || lockCount === 0) return
  lockCount -= 1
  if (lockCount === 0) {
    document.body.style.overflow = restoreOverflow ?? ''
    restoreOverflow = null
  }
}

export const useBodyScrollLock = (isLocked: Ref<boolean>) => {
  let held = false

  const sync = (locked: boolean) => {
    if (locked && !held) {
      acquire()
      held = true
      return
    }
    if (!locked && held) {
      release()
      held = false
    }
  }

  // Synchronous so the lock is in place before the modal paints, and released the
  // instant it closes — a deferred flush lets one frame of background scroll through.
  watch(isLocked, sync, { immediate: true, flush: 'sync' })
  onBeforeUnmount(() => sync(false))
}
