import { describe, expect, it } from 'vitest'

import {
  createFocusHighlight,
  FOCUS_HIGHLIGHT_DURATION_MS,
  type FocusHighlightTarget
} from './focusHighlight'

/** A fake clock: timers fire only when the test advances them, so no assertion waits on real time. */
const harness = () => {
  const changes: (FocusHighlightTarget | null)[] = []
  let nextHandle = 1
  const timers = new Map<number, { callback: () => void; dueAt: number }>()
  let now = 0

  const controller = createFocusHighlight({
    onChange: target => changes.push(target),
    setTimer: (callback, delayMs) => {
      const handle = nextHandle++
      timers.set(handle, { callback, dueAt: now + delayMs })
      return handle
    },
    clearTimer: handle => { timers.delete(handle) }
  })

  const advance = (ms: number) => {
    now += ms
    for (const [handle, timer] of [...timers]) {
      if (timer.dueAt <= now) {
        timers.delete(handle)
        timer.callback()
      }
    }
  }

  return { controller, changes, advance, pending: () => timers.size }
}

describe('focus highlight lifetime', () => {
  it('expires on its own, so a missed exit cannot leave a permanent halo', () => {
    const { controller, changes, advance } = harness()

    controller.show('node', 'device-1')
    expect(changes).toEqual([{ kind: 'node', id: 'device-1' }])

    // Still up just before the deadline: the cue must survive long enough to be seen.
    advance(FOCUS_HIGHLIGHT_DURATION_MS - 1)
    expect(changes).toHaveLength(1)

    advance(1)
    expect(changes).toEqual([{ kind: 'node', id: 'device-1' }, null])
  })

  it('replaces the previous target instead of highlighting two things at once', () => {
    const { controller, changes, advance, pending } = harness()

    controller.show('node', 'device-1')
    expect(pending()).toBe(1)
    controller.show('rule', 'rule-7')
    expect(changes).toEqual([
      { kind: 'node', id: 'device-1' },
      { kind: 'rule', id: 'rule-7' }
    ])

    // The first target's timer was cancelled when the second show() was called.
    expect(pending()).toBe(1)

    // The first target's timer must not fire and blank the second one early. Before this was one
    // controller, mutual exclusion was three hand-written clears in each of three setters.
    advance(FOCUS_HIGHLIGHT_DURATION_MS)
    expect(changes.filter(change => change === null)).toHaveLength(1)
  })

  it('restarts the clock when the same target is pointed at again', () => {
    const { controller, changes, advance } = harness()

    controller.show('node', 'device-1')
    advance(FOCUS_HIGHLIGHT_DURATION_MS - 100)
    controller.show('node', 'device-1')
    advance(FOCUS_HIGHLIGHT_DURATION_MS - 100)

    // Only the re-show, no expiry yet: clicking the same row twice should not blank the cue mid-pulse.
    expect(changes.filter(change => change === null)).toHaveLength(0)
    advance(100)
    expect(changes[changes.length - 1]).toBeNull()
  })

  it('drops a cue whose target no longer exists, without waiting for the timer', () => {
    const { controller, changes, advance, pending } = harness()

    controller.show('node', 'device-1')
    expect(pending()).toBe(1)

    controller.reconcile(target => target.id !== 'device-1')
    expect(changes[changes.length - 1]).toBeNull()

    // The timer must have been cancelled; advancing should not fire a stale callback.
    expect(pending()).toBe(0)
    advance(FOCUS_HIGHLIGHT_DURATION_MS)
    expect(changes[changes.length - 1]).toBeNull()
  })

  it('keeps a cue whose target still exists', () => {
    const { controller, changes } = harness()

    controller.show('spec', 'spec-3')
    controller.reconcile(() => true)
    expect(changes).toEqual([{ kind: 'spec', id: 'spec-3' }])
  })

  it('reports nothing when clearing or reconciling with no cue up', () => {
    const { controller, changes } = harness()

    controller.clear()
    controller.reconcile(() => false)
    expect(changes).toEqual([])
  })

  it('releases its timer on dispose, so a fired callback cannot touch a dead component', () => {
    const { controller, changes, advance, pending } = harness()

    controller.show('node', 'device-1')
    expect(pending()).toBe(1)
    controller.dispose()
    expect(pending()).toBe(0)

    advance(FOCUS_HIGHLIGHT_DURATION_MS * 2)
    expect(changes).toEqual([{ kind: 'node', id: 'device-1' }])
  })
})
