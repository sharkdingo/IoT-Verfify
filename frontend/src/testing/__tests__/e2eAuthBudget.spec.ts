import { describe, expect, it } from 'vitest'
import { REGISTRATIONS_PER_FULL_RUN, budgetAdviceMessage } from '../../../e2e/support/authBudget'

/**
 * The preflight's arithmetic and advice, checked without a backend.
 *
 * Lives under `src/` because `vitest.config.ts` excludes `e2e/**` — Playwright owns that directory, so a spec
 * placed beside the helper would never have run. It imports across the boundary, which is the honest trade:
 * the code under test is E2E tooling, but the check for it belongs where the unit runner looks.
 *
 * `readAuthBudget` itself needs a live server, and its two branches cannot both be exercised on demand: the
 * "exhausted" branch only exists while the hour window is closed, and the "available" branch only while it is
 * open. What *can* be pinned here is everything that made the first version of this check useless — the wrong
 * assumption about which numbers matter, and advice that omits a variable the JVM actually reads.
 *
 * The first version was worse than useless: it probed with an invalid payload, which `@Valid` rejects before
 * the rate-limit guard is ever consulted, so it returned 400 whether the budget was full or empty. It reported
 * safety unconditionally. That is the failure mode this file exists to keep out.
 */
describe('e2e auth budget preflight', () => {
  it('states a registration count that a full suite can actually exceed', () => {
    // The point of the whole check: the suite needs more registrations than the per-source default allows, so
    // a full pass cannot succeed on the defaults. If this ever stops being true the preflight is pointless and
    // should be deleted rather than left to cry wolf.
    const PER_SOURCE_DEFAULT_PER_HOUR = 60
    expect(REGISTRATIONS_PER_FULL_RUN).toBeGreaterThan(PER_SOURCE_DEFAULT_PER_HOUR)
  })

  it('names every variable the backend reads, not just the one that failed', () => {
    const advice = budgetAdviceMessage(600)
    // Register is what fails first; login is what fails next, and a run that raises only the first hits the
    // second — which cost five board specs in an earlier session. Both scopes of both limits are named.
    for (const key of [
      'AUTH_SOURCE_REGISTER_RATE_LIMIT_PER_HOUR',
      'AUTH_REGISTER_RATE_LIMIT_PER_HOUR',
      'AUTH_SOURCE_LOGIN_RATE_LIMIT_PER_MINUTE',
      'AUTH_LOGIN_RATE_LIMIT_PER_MINUTE'
    ]) {
      expect(advice, `${key} should appear in the advice`).toContain(key)
    }
  })

  it('says the values must be set on the JVM, because exporting them in the test shell does nothing', () => {
    // The limiter reads these into `final` fields at construction. Anyone who exports them next to the
    // Playwright command sees no effect and concludes the advice is wrong, so the advice says so itself.
    expect(budgetAdviceMessage()).toMatch(/read by the JVM, not by the tests/)
    expect(budgetAdviceMessage()).toMatch(/spring-boot:run/)
  })

  it('reports a concrete wait when the limiter supplies one, and no false precision when it does not', () => {
    expect(budgetAdviceMessage(600)).toMatch(/resets in ~10 minutes/)
    // Without a number from the server, do not invent one.
    expect(budgetAdviceMessage()).not.toMatch(/~\d+ minutes/)
    expect(budgetAdviceMessage()).toMatch(/hour boundary/)
  })
})
