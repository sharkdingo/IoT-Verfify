import type { VNode } from 'vue'
import { ElMessage, ElMessageBox } from 'element-plus'

import { i18n } from '@/assets/i18n'

/**
 * The one place user feedback is produced.
 *
 * Call sites state the *intent* ("this destructive action needs confirming"), not the
 * widget, so wording shape, icon, button order, and focus behaviour stay uniform and can be
 * changed in one edit. See docs/guides/frontend-ui-conventions.md for which mechanism
 * belongs to which situation — in particular, a success whose result is already visible on
 * screen gets no toast at all.
 */

const t = (key: string, named?: Record<string, unknown>) =>
  named ? i18n.global.t(key, named) : i18n.global.t(key)

/** Toast durations: long enough to read, short enough not to sit over the canvas. */
const DURATION = { short: 2600, normal: 3600, long: 5200 } as const

export const notifySuccess = (message: string) => {
  ElMessage.success({ message, duration: DURATION.short })
}

export const notifyInfo = (message: string) => {
  ElMessage.info({ message, duration: DURATION.short })
}

/**
 * The action was refused because of current UI/session state (playback open, another run
 * in flight). Tells the user what to close, so it is a warning rather than an error.
 */
export const notifyBlocked = (message: string) => {
  ElMessage.warning({ message, duration: DURATION.normal })
}

export const notifyError = (message: string) => {
  ElMessage.error({ message, duration: DURATION.long })
}

/**
 * Clears every open toast. Used when the board changes context wholesale (scene replacement,
 * playback teardown) and older toasts would describe a state that no longer exists.
 */
export const dismissAllNotifications = () => {
  ElMessage.closeAll()
}

type ConfirmOptions = {
  title: string
  /**
   * Plain text, or a VNode when the surface needs structure (per-field diagnostics with the
   * raw cause tucked into a "Technical Details" disclosure rather than shown inline).
   */
  message: string | VNode
  /** Defaults to a generic "Confirm"; name the action instead where possible. */
  confirmText?: string
  cancelText?: string
  /** Only for surfaces that need extra layout (the full-scene replacement preview). */
  customClass?: string
}

/**
 * Element Plus teleports MessageBox to <body>, so it sits above every app surface via the
 * `--z-message-box` layer. `lockScroll: false` because the board shell is a fixed
 * `100vh; overflow: hidden` surface — Element Plus's scrollbar compensation would otherwise
 * shift the whole fixed layout.
 */
const BASE_BOX = { appendTo: 'body', lockScroll: false } as const

/**
 * A destructive but reversible action (delete one device, discard a draft).
 * Resolves `true` on confirm and `false` on cancel/dismiss — cancelling is a normal
 * outcome, never an exception the caller has to catch.
 */
export const confirmDestructive = async (options: ConfirmOptions): Promise<boolean> => {
  try {
    await ElMessageBox.confirm(options.message, options.title, {
      ...BASE_BOX,
      type: 'warning',
      confirmButtonText: options.confirmText ?? t('app.confirm'),
      cancelButtonText: options.cancelText ?? t('app.cancel'),
      confirmButtonClass: 'el-button--danger',
      ...(options.customClass ? { customClass: options.customClass } : {})
    })
    return true
  } catch (error) {
    // A dismissal rejects with 'cancel'/'close'. Anything else is a real failure, and treating it as
    // a deliberate cancel silently is safe for the user but hides the cause from the next debugger.
    if (error !== 'cancel' && error !== 'close') {
      console.error('Confirmation dialog failed:', error)
    }
    return false
  }
}

/**
 * Dismisses whatever confirmation is on screen. Needed when the surface that raised it goes
 * away underneath it (its owning dialog closes), which would otherwise leave a confirmation
 * asking about state the user can no longer see. Resolves the pending call as cancelled.
 */
export const dismissOpenConfirmation = () => {
  ElMessageBox.close()
}

/** Acknowledgement of something the user cannot act on further. */
export const acknowledge = async (
  options: Omit<ConfirmOptions, 'cancelText'> & { tone?: 'warning' | 'error' }
): Promise<void> => {
  try {
    await ElMessageBox.alert(options.message, options.title, {
      ...BASE_BOX,
      type: options.tone ?? 'warning',
      confirmButtonText: options.confirmText ?? t('app.confirm')
    })
  } catch {
    // Dismissing an acknowledgement is equivalent to confirming it.
  }
}
