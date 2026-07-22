import { describe, expect, it, vi } from 'vitest'
import {
  createLatestBoardRequestGuard,
  createScopedBoardInvalidationBinding,
  isAccountDeletionOutcomeUncertain,
  loadBoardResultWithRetry
} from './Board.vue'

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
