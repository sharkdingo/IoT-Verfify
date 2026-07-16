import { describe, expect, it } from 'vitest'
import { FUZZ_RESPONSE_INCOMPLETE_CODE } from '../fuzzingResponse'
import {
  FUZZ_INLINE_RESULT_RECOVERY_MAX_FAILURES,
  classifyTrackedFuzzRunError,
  clearStoredFuzzNotifications,
  fuzzNotificationStorageKeyForUser,
  fuzzRunRetryDelayMs,
  isTransientTaskHttpStatus
} from '../fuzzingRecovery'

describe('tracked fuzz-run recovery', () => {
  it('stops retrying malformed response data and explicit client errors', () => {
    expect(classifyTrackedFuzzRunError({ code: FUZZ_RESPONSE_INCOMPLETE_CODE }))
      .toBe('UNAVAILABLE')
    expect(classifyTrackedFuzzRunError({ response: { status: 400 } }))
      .toBe('UNAVAILABLE')
    expect(classifyTrackedFuzzRunError({ response: { status: 404 } }))
      .toBe('UNAVAILABLE')
    expect(classifyTrackedFuzzRunError({ response: { status: 422 } }))
      .toBe('UNAVAILABLE')
  })

  it('retries network failures and server errors', () => {
    expect(classifyTrackedFuzzRunError({ code: 'ERR_NETWORK' })).toBe('RETRY')
    expect(classifyTrackedFuzzRunError({ response: { status: 408 } })).toBe('RETRY')
    expect(classifyTrackedFuzzRunError({ response: { status: 425 } })).toBe('RETRY')
    expect(classifyTrackedFuzzRunError({ response: { status: 429 } })).toBe('RETRY')
    expect(classifyTrackedFuzzRunError({ response: { status: 500 } })).toBe('RETRY')
    expect(classifyTrackedFuzzRunError({ response: { status: 503 } })).toBe('RETRY')
    expect(isTransientTaskHttpStatus(408)).toBe(true)
    expect(isTransientTaskHttpStatus(425)).toBe(true)
    expect(isTransientTaskHttpStatus(429)).toBe(true)
    expect(isTransientTaskHttpStatus(503)).toBe(true)
    expect(isTransientTaskHttpStatus(422)).toBe(false)
  })

  it('backs off completed-result recovery with a bounded delay', () => {
    expect(FUZZ_INLINE_RESULT_RECOVERY_MAX_FAILURES).toBe(3)
    expect(fuzzRunRetryDelayMs(0)).toBe(5_000)
    expect(fuzzRunRetryDelayMs(1)).toBe(10_000)
    expect(fuzzRunRetryDelayMs(4)).toBe(60_000)
    expect(fuzzRunRetryDelayMs(50)).toBe(60_000)
  })

  it('clears per-user notification storage without overriding account deletion', () => {
    const key = fuzzNotificationStorageKeyForUser(17)
    const removed: string[] = []
    clearStoredFuzzNotifications(key, { removeItem: value => removed.push(value) })

    expect(key).toBe('iot_verify_fuzz_notifications_17')
    expect(fuzzNotificationStorageKeyForUser(0)).toBe('iot_verify_fuzz_notifications_anonymous')
    expect(removed).toEqual([key])
    expect(() => clearStoredFuzzNotifications(key, {
      removeItem: () => { throw new Error('storage disabled') }
    })).not.toThrow()
  })
})
