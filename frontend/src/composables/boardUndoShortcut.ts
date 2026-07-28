/**
 * Whether a keyboard event should be treated as a *board* undo/redo rather than left to the
 * platform.
 *
 * Split out from the composable so the scoping rules — the part that decides whether we steal a
 * keystroke from a text field or an IME — can be tested without a mounted board.
 */

/** Elements whose own undo stack must always win. */
const NATIVE_UNDO_TAGS = new Set(['INPUT', 'TEXTAREA'])

/**
 * True when the event originates somewhere the platform already provides undo.
 *
 * Text fields, `contenteditable` regions (rich text and code editors), and anything inside them
 * keep their native per-field history: a user fixing a typo expects `Ctrl+Z` to restore the
 * character they just deleted, not to resurrect a rule they deleted a minute ago.
 */
export const targetOwnsNativeUndo = (target: EventTarget | null): boolean => {
  if (!(target instanceof HTMLElement)) return false
  if (NATIVE_UNDO_TAGS.has(target.tagName)) return true
  // `isContentEditable` is true for descendants too, which is what we want: a code editor's
  // inner spans must not leak the keystroke to the board.
  return Boolean(target.isContentEditable)
}

export type BoardUndoIntent = 'undo' | 'redo' | null

/**
 * Classifies a keydown as a board undo, redo, or neither.
 *
 * Accelerators: `Ctrl+Z` / `Meta+Z` to undo, `Ctrl+Shift+Z` / `Meta+Shift+Z` to redo, and
 * `Ctrl+Y` for the Windows convention. `event.key` is used rather than `code` so a non-QWERTY
 * layout reports the character the user actually typed.
 *
 * Returns `null` while an IME composition is active: during Chinese/Japanese/Korean input the
 * keystroke belongs to the composition, and hijacking it would discard half-typed text.
 */
export const resolveBoardUndoIntent = (event: KeyboardEvent): BoardUndoIntent => {
  if (event.isComposing || event.keyCode === 229) return null
  if (event.altKey) return null

  // Exactly one of Ctrl/Meta, so browser and OS shortcuts that add the other are left alone.
  const primaryModifier = event.ctrlKey !== event.metaKey
  if (!primaryModifier) return null

  const key = event.key.toLowerCase()
  if (key === 'z') return event.shiftKey ? 'redo' : 'undo'
  // Ctrl+Y is redo on Windows. Shift+Ctrl+Y is not a convention anywhere, so it stays unhandled.
  if (key === 'y' && !event.shiftKey) return 'redo'
  return null
}
