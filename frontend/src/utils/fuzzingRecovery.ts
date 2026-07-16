import { FUZZ_RESPONSE_INCOMPLETE_CODE } from './fuzzingResponse'

export type TrackedFuzzRunRecovery = 'RETRY' | 'UNAVAILABLE'

const TRANSIENT_HTTP_STATUSES = new Set([408, 425, 429])
export const FUZZ_INLINE_RESULT_RECOVERY_MAX_FAILURES = 3

export const fuzzNotificationStorageKeyForUser = (userId?: number | null): string => {
  const suffix = Number.isSafeInteger(userId) && Number(userId) > 0
    ? Number(userId)
    : 'anonymous'
  return `iot_verify_fuzz_notifications_${suffix}`
}

export const clearStoredFuzzNotifications = (
  storageKey: string,
  storage: Pick<Storage, 'removeItem'> | undefined = typeof localStorage === 'undefined'
    ? undefined
    : localStorage
): void => {
  if (!storage) return
  try {
    storage.removeItem(storageKey)
  } catch {
    // Server-side account deletion already succeeded; browser cleanup is best-effort.
  }
}

export const isTransientTaskHttpStatus = (value: unknown): boolean => {
  const status = Number(value)
  return Number.isFinite(status) && (TRANSIENT_HTTP_STATUSES.has(status) || status >= 500)
}

export const fuzzRunRetryDelayMs = (
  attempt: number,
  baseDelayMs = 5_000,
  maximumDelayMs = 60_000
): number => {
  const normalizedAttempt = Number.isSafeInteger(attempt) ? Math.max(0, attempt) : 0
  const normalizedBase = Math.max(1, Math.floor(baseDelayMs))
  const normalizedMaximum = Math.max(normalizedBase, Math.floor(maximumDelayMs))
  return Math.min(normalizedMaximum, normalizedBase * (2 ** Math.min(normalizedAttempt, 20)))
}

export const classifyTrackedFuzzRunError = (error: any): TrackedFuzzRunRecovery => {
  if (error?.code === FUZZ_RESPONSE_INCOMPLETE_CODE) return 'UNAVAILABLE'

  const status = Number(error?.response?.status)
  if (!Number.isFinite(status)) return 'RETRY'
  if (isTransientTaskHttpStatus(status)) return 'RETRY'
  return status >= 400 && status < 500 ? 'UNAVAILABLE' : 'RETRY'
}
