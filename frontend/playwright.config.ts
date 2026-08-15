import { defineConfig, devices } from '@playwright/test'

const baseURL = process.env.E2E_BASE_URL || 'http://127.0.0.1:3000'
const shouldStartFrontend = !process.env.E2E_BASE_URL

export default defineConfig({
  testDir: './e2e',
  /**
   * Diagnose an exhausted auth budget before any browser starts.
   *
   * A full pass needs ~67 registrations against a per-source default of 60/hour, so it cannot pass on the
   * defaults — and it fails as a scatter of raw 429s inside the shared fixture, which reads as sixteen
   * unrelated product regressions. This prints what to set and what the headroom is. See
   * `e2e/support/authBudget.ts`.
   */
  globalSetup: './e2e/global-setup.ts',
  timeout: 60_000,
  expect: {
    timeout: 5_000
  },
  /**
   * One, matching the full-suite contract in `.github/scripts/run-e2e.sh` — Playwright otherwise
   * defaults to half the logical cores, which is what a local run silently got.
   *
   * CI passes `--workers` explicitly on every path (1 for the complete run, 2 for the risk-routed
   * subsets), and a CLI flag overrides this, so it changes CI not at all. What it fixes is that a bare
   * local `npx playwright test` took half the logical cores — 14 on the 28-thread machine this was
   * measured on — against one backend, one MySQL and one NuSMV. Measured consequence: a rule-builder
   * save whose `check-duplicate` pre-check errored under that load left a confirm overlay open and
   * failed a spec that passes when serialized — indistinguishable from a product regression, and it
   * cost a full investigation.
   *
   * Use `--workers=2` for a narrow subset, as CI does. Raising it for wall-clock time is what this
   * default exists to prevent.
   */
  workers: 1,
  use: {
    baseURL,
    screenshot: 'only-on-failure',
    trace: 'on-first-retry'
  },
  /**
   * Serve a production build rather than the dev server.
   *
   * Vite's dev server transforms modules on demand, so two parallel browsers loading the board at
   * once could exceed the 30s `board-root` wait and fail a test that has nothing wrong with it.
   * A prebuilt bundle removes that variable, and it is also closer to what users run.
   *
   * `reuseExistingServer` is off deliberately. With it on, any process already holding the port —
   * typically a dev server someone left running — is adopted silently, the build is skipped, and
   * the suite reports green against stale code. Set `E2E_BASE_URL` to point at a server you are
   * managing yourself instead.
   */
  webServer: shouldStartFrontend
    ? {
        command: 'npm run build && npm run preview -- --port 3000 --strictPort',
        url: baseURL,
        reuseExistingServer: false,
        timeout: 180_000
      }
    : undefined,
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] }
    }
  ]
})
