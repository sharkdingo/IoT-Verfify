export type InteractiveCancellationRetryOptions = {
  cancel: () => Promise<boolean>
  waitBeforeRetry: (failedAttempt: number) => Promise<void>
  shouldContinue?: () => boolean
  maxAttempts?: number
}

/**
 * A stop request can arrive a few milliseconds before the matching POST has
 * registered its server-side execution. Retry that narrow race without
 * treating a truthful `false` response as terminal cancellation.
 */
export const requestInteractiveCancellation = async ({
  cancel,
  waitBeforeRetry,
  shouldContinue = () => true,
  maxAttempts = 5
}: InteractiveCancellationRetryOptions): Promise<boolean> => {
  const attempts = Math.max(1, Math.floor(maxAttempts))
  let lastError: unknown

  for (let attempt = 1; attempt <= attempts && shouldContinue(); attempt += 1) {
    try {
      if (await cancel()) return true
      lastError = undefined
    } catch (error) {
      lastError = error
    }

    if (attempt < attempts && shouldContinue()) {
      await waitBeforeRetry(attempt)
    }
  }

  if (lastError) throw lastError
  return false
}
