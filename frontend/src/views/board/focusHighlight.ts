/**
 * "Show me where that is" — a one-shot cue, not a selection.
 *
 * The board can point at a device, a rule, or a specification: clicking an inspector list row pans the
 * canvas to it, and the assistant does the same for something it just created. The canvas then paints the
 * target with a 28px accent bloom and an *infinitely* pulsing ring (`.node-focused`,
 * `.edge-line--focused`).
 *
 * That visual is a cue — it exists to carry the eye to a target after the canvas moves. It was stored as if
 * it were a selection: three plain refs, cleared only by whoever happened to remember. Measured, five exits
 * did not: clicking empty canvas, pressing Escape, closing the device dialog, focusing a different device by
 * any other path, and simply moving on. So one device kept a pulsing halo indefinitely while its neighbours
 * had none, with no way for the user to infer the cause — which is how it was reported ("why do some device
 * instances glow and others don't?").
 *
 * Adding a clear to each exit is the wrong fix: it makes correctness depend on enumerating every future exit,
 * and this round proved that enumeration fails. Instead the cue owns its own lifetime. It expires on a timer,
 * so a missed exit costs a second of highlight rather than a permanent one, and the three targets are mutually
 * exclusive by construction rather than by three hand-written clears per setter.
 *
 * Pure and framework-free so it can be unit-tested against a fake clock; `Board.vue` wraps the result in refs.
 */

/** Which kind of thing the board is currently pointing at. */
export type FocusHighlightKind = 'node' | 'rule' | 'spec'

export interface FocusHighlightTarget {
  kind: FocusHighlightKind
  id: string
}

/**
 * How long the cue stays up.
 *
 * Long enough to find the target after the canvas finishes panning, short enough that it reads as a pointer
 * rather than a state. The pulse animation is 1.2s, so this is a little over two cycles: the user sees it
 * pulse, understands it as motion directed at them, and it leaves.
 */
export const FOCUS_HIGHLIGHT_DURATION_MS = 2600

export interface FocusHighlightPorts {
  /** Called whenever the active target changes, including when it expires (with `null`). */
  onChange: (target: FocusHighlightTarget | null) => void
  /** Injected so tests drive a fake clock instead of waiting. */
  setTimer: (callback: () => void, delayMs: number) => number
  clearTimer: (handle: number) => void
}

export interface FocusHighlightController {
  /** Point at something. Replaces any current target and restarts the timer. */
  show: (kind: FocusHighlightKind, id: string) => void
  /** Drop the cue now — used when the thing being pointed at stops existing. */
  clear: () => void
  /**
   * Drop the cue if it points at one of the ids that no longer exist.
   *
   * Deleting the focused device must not leave a highlight addressing a missing id, which is the one case
   * where waiting for the timer would paint a cue for something that is gone.
   */
  reconcile: (exists: (target: FocusHighlightTarget) => boolean) => void
  /** Release the pending timer. Call on unmount so a fired callback cannot touch a dead component. */
  dispose: () => void
}

export const createFocusHighlight = (ports: FocusHighlightPorts): FocusHighlightController => {
  let current: FocusHighlightTarget | null = null
  let handle: number | null = null

  const cancelTimer = () => {
    if (handle === null) return
    ports.clearTimer(handle)
    handle = null
  }

  const set = (target: FocusHighlightTarget | null) => {
    cancelTimer()
    // Report every transition, including target-to-target, so the canvas cannot keep painting the old one.
    current = target
    ports.onChange(target)
    if (!target) return
    handle = ports.setTimer(() => {
      handle = null
      current = null
      ports.onChange(null)
    }, FOCUS_HIGHLIGHT_DURATION_MS)
  }

  return {
    show: (kind, id) => set({ kind, id }),
    clear: () => {
      if (!current) return
      set(null)
    },
    reconcile: (exists) => {
      if (!current) return
      if (!exists(current)) set(null)
    },
    dispose: cancelTimer
  }
}
