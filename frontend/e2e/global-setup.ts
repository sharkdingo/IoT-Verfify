/**
 * One legible failure instead of sixteen misleading ones.
 *
 * See `support/authBudget.ts` for why: the suite needs more registrations than the default per-source budget
 * allows, and exhausting it mid-run produces a scatter of 429s inside the shared fixture that look exactly
 * like product regressions. Checking once, before any browser launches, costs one HTTP request.
 *
 * Deliberately a *warning* rather than a hard stop when the budget is gone. A developer running a single spec
 * needs one registration and should not be blocked by a full-suite calculation, and this cannot tell which
 * case it is in. So it prints the diagnosis loudly and lets the run proceed — the point is that the next
 * person reading a wall of 429s knows within seconds what they are looking at.
 */
import { budgetAdviceMessage, readAuthBudget } from './support/authBudget'

export default async function globalSetup() {
  const budget = await readAuthBudget()
  if (!budget.exhausted) return

  const banner = '='.repeat(96)
  console.warn(`\n${banner}`)
  console.warn('E2E PREFLIGHT: auth register budget exhausted — failures below are NOT product defects')
  console.warn(budgetAdviceMessage(budget.retryAfterSeconds))
  console.warn(`${banner}\n`)
}
