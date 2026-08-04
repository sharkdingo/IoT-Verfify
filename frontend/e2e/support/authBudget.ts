/**
 * Fail fast when the backend's auth rate limit cannot accommodate the run.
 *
 * A full suite makes ~67 `createAuthenticatedUser` calls, each of which registers an account, against a
 * per-source register budget whose default is **60 per hour**. So a full run cannot pass on the defaults —
 * and it does not fail in a way that says so. It fails as 16 unrelated-looking tests dying inside the shared
 * fixture with a raw 429, in whichever order the workers happened to reach them. That has now cost several
 * passes of this audit: the failures look like product defects until you grep every `error-context.md` for
 * `AUTH_REGISTER_RATE_LIMIT_REACHED`, and a *partial* exhaustion is worse still, because some tests pass and
 * the rest look like real regressions.
 *
 * This turns that into one legible message before any browser starts. It does not raise the limit — the guard
 * reads its values into `final` fields at construction, so only the JVM under test can — but it says exactly
 * what to set and what the current headroom is.
 */
import { request } from '@playwright/test'

const apiBaseURL = process.env.E2E_API_BASE_URL || 'http://127.0.0.1:8080'

/** Registrations a full pass needs, measured from the specs rather than guessed. */
export const REGISTRATIONS_PER_FULL_RUN = 67

/**
 * Ask the register endpoint whether it still has budget, without spending any.
 *
 * The payload has to be **well-formed but unable to create an account**, and getting that wrong makes the
 * whole check useless. My first version sent deliberately invalid fields, reasoning that a valid payload would
 * consume the very registration it was testing for. But `@Valid` sits on the controller *parameter*, so
 * malformed input is rejected before the method body ever runs and the rate-limit guard is never consulted:
 * the probe returned 400 whether the budget was full or empty. A check that cannot detect the condition it
 * exists for is worse than no check, because it reports safety.
 *
 * The guard runs as the first statement of the method body, ahead of `authService.register`. So a valid
 * payload whose phone is already taken passes validation, is seen by the limiter, and is then refused as a
 * duplicate — it can never create an account. Verified against the live backend: invalid → 400 (guard not
 * reached), valid-and-duplicate → 429 with `AUTH_REGISTER_RATE_LIMIT_REACHED`.
 *
 * When budget *is* available this returns 409 (duplicate), which costs one register slot against the window.
 * That is one out of sixty, spent once per run, to convert a scatter of sixteen misleading failures into a
 * single legible line — and the well-known number below is never a real account.
 */
const PROBE_PHONE = '13800000001'

const PROBE_PASSWORD = 'Probe#Passw0rd'
const PROBE_USERNAME = 'e2e_budget_probe'

export const readAuthBudget = async (): Promise<{ exhausted: boolean, retryAfterSeconds?: number }> => {
  const context = await request.newContext()
  try {
    const response = await context.post(`${apiBaseURL}/api/auth/register`, {
      data: { phone: PROBE_PHONE, username: PROBE_USERNAME, password: PROBE_PASSWORD },
      failOnStatusCode: false
    })

    if (response.status() === 429) {
      const body = await response.json().catch(() => null)
      return { exhausted: true, retryAfterSeconds: body?.data?.retryAfterSeconds }
    }

    // 2xx means the probe phone was not registered yet and this call created it. Clean up rather than leave an
    // account behind — a diagnostic must not mutate the database it is diagnosing. On the next run the same
    // phone is free again, so the probe stays self-contained either way.
    if (response.ok()) {
      const token = (await response.json().catch(() => null))?.data?.token
      if (token) {
        await context.delete(`${apiBaseURL}/api/auth/account`, {
          headers: { Authorization: `Bearer ${token}` },
          data: { password: PROBE_PASSWORD, confirmation: PROBE_PHONE },
          failOnStatusCode: false
        })
      }
    }

    return { exhausted: false }
  } catch {
    // Backend unreachable is a different problem, and the specs report it far better than this probe can.
    return { exhausted: false }
  } finally {
    await context.dispose()
  }
}

export const budgetAdviceMessage = (retryAfterSeconds?: number) => {
  const wait = typeof retryAfterSeconds === 'number'
    ? `The current window resets in ~${Math.ceil(retryAfterSeconds / 60)} minutes.`
    : 'The window resets on the hour boundary the limiter opened.'

  return [
    '',
    'The backend has no register budget left, so this run would fail inside the shared auth fixture',
    'rather than on any product assertion.',
    '',
    `A full pass needs ~${REGISTRATIONS_PER_FULL_RUN} registrations; the per-source default is 60 per hour.`,
    'The limiter reads its values into final fields at construction, so raising them needs a backend restart:',
    '',
    '  AUTH_SOURCE_REGISTER_RATE_LIMIT_PER_HOUR=600 \\',
    '  AUTH_REGISTER_RATE_LIMIT_PER_HOUR=600 \\',
    '  AUTH_SOURCE_LOGIN_RATE_LIMIT_PER_MINUTE=600 \\',
    '  AUTH_LOGIN_RATE_LIMIT_PER_MINUTE=600 \\',
    '  mvn spring-boot:run',
    '',
    'Exporting these in the Playwright shell does nothing — they are read by the JVM, not by the tests.',
    wait,
    ''
  ].join('\n')
}
