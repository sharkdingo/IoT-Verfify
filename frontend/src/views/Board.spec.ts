import { describe, expect, it, vi } from 'vitest'
import {
  collectBundledEnvironmentNames,
  clampFloatingMenuPosition,
  createLatestBoardRequestGuard,
  createScopedBoardInvalidationBinding,
  focusCollapsedNarrowPanelToggle,
  isAccountDeletionOutcomeUncertain,
  loadBoardResultWithRetry,
  reconcileBoardNodeSnapshot,
  resolveCurrentBoardNode,
  shouldRedirectNarrowPanelFocus
} from './Board.vue'

describe('Board node snapshot reconciliation', () => {
  it('preserves object identity and every pending or active layout while merging server fields', () => {
    const first = { id: 'a', label: 'Old A', position: { x: 1, y: 2 }, width: 100, height: 80 }
    const second = { id: 'b', label: 'Old B', position: { x: 3, y: 4 }, width: 110, height: 90 }
    const incoming = [
      { id: 'a', label: 'Server A', position: { x: 10, y: 20 }, width: 120, height: 100 },
      { id: 'b', label: 'Server B', position: { x: 30, y: 40 }, width: 130, height: 110 }
    ]
    const pending = new Map([['a', {
      layout: { position: { x: 50, y: 60 }, width: 140, height: 120 }
    }]])

    const result = reconcileBoardNodeSnapshot([first, second], incoming, pending, new Set(['b']))

    expect(result[0]).toBe(first)
    expect(result[1]).toBe(second)
    expect(result[0]).toMatchObject({
      label: 'Server A', position: { x: 50, y: 60 }, width: 140, height: 120
    })
    expect(result[1]).toMatchObject({
      label: 'Server B', position: { x: 3, y: 4 }, width: 110, height: 90
    })
  })

  it('uses the server layout once no local interaction owns the node', () => {
    const current = { id: 'a', position: { x: 1, y: 2 }, width: 100, height: 80 }
    const incoming = { id: 'a', position: { x: 10, y: 20 }, width: 120, height: 100 }

    const [result] = reconcileBoardNodeSnapshot([current], [incoming], new Map(), new Set())

    expect(result).toBe(current)
    expect(result).toMatchObject(incoming)
  })

  it('rebinds open surfaces to the current snapshot and invalidates removed nodes', () => {
    const stale = { id: 'a', label: 'Stale label' }
    const replacement = { id: 'a', label: 'Current label' }

    expect(resolveCurrentBoardNode([replacement], stale.id)).toBe(replacement)
    expect(resolveCurrentBoardNode([], stale.id)).toBeNull()
    expect(resolveCurrentBoardNode([replacement], null)).toBeNull()
  })
})

describe('Board floating-menu positioning', () => {
  it('keeps the full menu inside every viewport edge', () => {
    expect(clampFloatingMenuPosition(
      { x: 995, y: 795 },
      { width: 220, height: 180 },
      { width: 1000, height: 800 }
    )).toEqual({ x: 772, y: 612 })
    expect(clampFloatingMenuPosition(
      { x: -20, y: -10 },
      { width: 220, height: 180 },
      { width: 1000, height: 800 }
    )).toEqual({ x: 8, y: 8 })
  })
})

describe('Board completed-result recovery', () => {
  it('retries transient detail failures and returns the recovered result', async () => {
    const load = vi.fn()
      .mockRejectedValueOnce(new Error('temporary 503'))
      .mockRejectedValueOnce(new Error('temporary network failure'))
      .mockResolvedValue({ id: 17 })
    const waitBeforeRetry = vi.fn().mockResolvedValue(undefined)

    await expect(loadBoardResultWithRetry({
      load,
      shouldRetry: () => true,
      waitBeforeRetry,
      maxAttempts: 3
    })).resolves.toEqual({ id: 17 })

    expect(load).toHaveBeenCalledTimes(3)
    expect(waitBeforeRetry).toHaveBeenNthCalledWith(1, 1)
    expect(waitBeforeRetry).toHaveBeenNthCalledWith(2, 2)
  })

  it('does not retry permanent response errors', async () => {
    const error = new Error('malformed response')
    const load = vi.fn().mockRejectedValue(error)
    const waitBeforeRetry = vi.fn().mockResolvedValue(undefined)

    await expect(loadBoardResultWithRetry({
      load,
      shouldRetry: () => false,
      waitBeforeRetry,
      maxAttempts: 3
    })).rejects.toBe(error)

    expect(load).toHaveBeenCalledTimes(1)
    expect(waitBeforeRetry).not.toHaveBeenCalled()
  })

  it('bounds retries when a transient detail endpoint stays unavailable', async () => {
    const error = new Error('still unavailable')
    const load = vi.fn().mockRejectedValue(error)
    const waitBeforeRetry = vi.fn().mockResolvedValue(undefined)

    await expect(loadBoardResultWithRetry({
      load,
      shouldRetry: () => true,
      waitBeforeRetry,
      maxAttempts: 3
    })).rejects.toBe(error)

    expect(load).toHaveBeenCalledTimes(3)
    expect(waitBeforeRetry).toHaveBeenCalledTimes(2)
  })
})

describe('Board model-fingerprint request ordering', () => {
  it('rejects older responses and invalidates in-flight requests on a model change', () => {
    const guard = createLatestBoardRequestGuard()
    const older = guard.begin()
    const newer = guard.begin()

    expect(guard.isCurrent(older)).toBe(false)
    expect(guard.isCurrent(newer)).toBe(true)

    guard.invalidate()
    expect(guard.isCurrent(newer)).toBe(false)
  })
})

describe('Board invalidation ownership', () => {
  it('unsubscribes the previous account before binding the next account', () => {
    const aliceUnsubscribe = vi.fn()
    const bobUnsubscribe = vi.fn()
    const subscribe = vi.fn()
      .mockReturnValueOnce(aliceUnsubscribe)
      .mockReturnValueOnce(bobUnsubscribe)
    const listener = vi.fn()
    const binding = createScopedBoardInvalidationBinding(subscribe, listener)

    binding.bind(1)
    binding.bind(2)

    expect(subscribe).toHaveBeenNthCalledWith(1, 1, listener)
    expect(subscribe).toHaveBeenNthCalledWith(2, 2, listener)
    expect(aliceUnsubscribe).toHaveBeenCalledOnce()
    expect(bobUnsubscribe).not.toHaveBeenCalled()

    binding.dispose()
    expect(bobUnsubscribe).toHaveBeenCalledOnce()
  })
})

describe('account deletion outcome classification', () => {
  it('keeps explicit client rejections retryable in the current session', () => {
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 400 } })).toBe(false)
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 401 } })).toBe(false)
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 409 } })).toBe(false)
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 429 } })).toBe(false)
  })

  it('treats missing responses and server failures as an unknown commit outcome', () => {
    expect(isAccountDeletionOutcomeUncertain(new Error('network disconnected'))).toBe(true)
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 500 } })).toBe(true)
    expect(isAccountDeletionOutcomeUncertain({ response: { status: 503 } })).toBe(true)
  })
})

describe('Board model-token provenance', () => {
  it('localizes a shared environment token only when every declaring provider is bundled', () => {
    expect(collectBundledEnvironmentNames([
      { bundled: true, names: ['weather', 'temperature'] },
      { bundled: true, names: ['weather'] }
    ])).toEqual(['weather', 'temperature'])

    expect(collectBundledEnvironmentNames([
      { bundled: true, names: ['weather', 'temperature'] },
      { bundled: false, names: ['weather', 'customReading'] }
    ])).toEqual(['temperature'])
  })

  it('does not let an unresolved provider claim bundled provenance', () => {
    expect(collectBundledEnvironmentNames([
      { bundled: false, names: [] }
    ])).toEqual([])
  })
})

describe('Board narrow-panel focus isolation', () => {
  it('keeps focus in the visible drawer, scrim, navigation, or an active modal', () => {
    const root = document.createElement('div')
    const nav = document.createElement('nav')
    nav.className = 'board-nav-bar'
    const navButton = document.createElement('button')
    nav.append(navButton)

    const panel = document.createElement('aside')
    const panelButton = document.createElement('button')
    panel.append(panelButton)

    const scrim = document.createElement('button')
    const backgroundButton = document.createElement('button')
    const modal = document.createElement('div')
    modal.setAttribute('aria-modal', 'true')
    const modalButton = document.createElement('button')
    modal.append(modalButton)
    root.append(nav, panel, scrim, backgroundButton, modal)
    document.body.append(root)

    expect(shouldRedirectNarrowPanelFocus(true, panelButton, panel, scrim)).toBe(false)
    expect(shouldRedirectNarrowPanelFocus(true, scrim, panel, scrim)).toBe(false)
    expect(shouldRedirectNarrowPanelFocus(true, navButton, panel, scrim)).toBe(false)
    expect(shouldRedirectNarrowPanelFocus(true, modalButton, panel, scrim)).toBe(false)
    expect(shouldRedirectNarrowPanelFocus(true, backgroundButton, panel, scrim)).toBe(true)
    expect(shouldRedirectNarrowPanelFocus(false, backgroundButton, panel, scrim)).toBe(false)

    root.remove()
  })

  it('restores focus to the collapsed toggle after either drawer closes', () => {
    const root = document.createElement('div')
    const control = document.createElement('aside')
    control.dataset.testid = 'control-center'
    control.className = 'is-collapsed'
    const controlToggle = document.createElement('button')
    control.append(controlToggle)

    const inspector = document.createElement('aside')
    inspector.dataset.testid = 'system-inspector'
    inspector.className = 'is-collapsed'
    const inspectorToggle = document.createElement('button')
    inspector.append(inspectorToggle)
    root.append(control, inspector)
    document.body.append(root)

    expect(focusCollapsedNarrowPanelToggle('control', root)).toBe(true)
    expect(document.activeElement).toBe(controlToggle)
    expect(focusCollapsedNarrowPanelToggle('inspector', root)).toBe(true)
    expect(document.activeElement).toBe(inspectorToggle)

    root.remove()
  })
})
