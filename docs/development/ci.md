# CI pipeline

Two tiers, chosen by what a change can actually break rather than by how large it is.

## Why it is split

Measured on this repo before the split (four consecutive `main` runs, GitHub-hosted `ubuntu-latest`):

| job | duration |
| :--- | ---: |
| frontend | ~95s |
| backend | ~103s |
| Full-stack E2E | ~590s |
| **wall clock** | **~700s** |

The E2E job was 85% of the critical path, and inside it the suite itself was 478s of 588s. Two specs
(`authority-model-audit`, `board-full-flow`) were **59% of that** with 20 of 93 tests. Every push paid
all of it, including a README fix.

It also redid work the other jobs had already done: Java setup, Node setup, NuSMV install, a full
backend recompile, and a second `npm ci` — **~73s per run** of pure duplication.

## Tier 1 — Fast CI (`fast-ci.yml`)

Runs on every push and pull request. Required for merge.

1. **Route by risk** — computes the changed paths and asks [`ci-risk-router.mjs`](../../.github/ci-risk-router.mjs)
   which tiers to run. Runs the router's own tests first, so a broken router fails loudly instead of
   silently routing everything to the cheap tier.
2. **Frontend** — `npm ci`, typecheck, unit tests, build. Typecheck runs before tests because it is
   the cheapest check that catches the largest class of mistake.
3. **Backend** — `mvn package` (tests plus the jar), with NuSMV available so the real-solver tests run.
4. **E2E smoke** — a browser-driven barrier against real MySQL, Redis, and the packaged jar.

The smoke barrier is 22 tests in ~44s (measured locally), chosen for coverage per second:

| spec | cost | what it protects |
| :--- | ---: | :--- |
| `error-contract` | 0.9s | the REST error envelope every screen depends on |
| `board-recovery` | 4.7s | the stack recovers instead of wedging |
| `canvas-runtime-environment` | 8.0s | a board renders and shared values reach the canvas |
| `ui-contracts` | 15.6s | 14 tests of cross-page contracts — the cheapest broad net |

That is ~9% of the full suite's runtime for a genuine barrier: the app boots, authenticates, renders a
board, and reports errors in the agreed shape.

## Tier 2 — Full CI (`full-ci.yml`)

The complete suite (91 tests) against real infrastructure. Runs where completeness matters:

- **`main`** — what gets released.
- **Nightly (03:17 UTC)** — the only thing that catches decay in code nobody touched.
- **Manual dispatch** — release candidates, or re-checking a suspicious branch.
- **High-risk branch pushes** — escalated automatically by the router.

## What counts as high risk

Not diff size. A one-line change in any of these gets the full suite, because a wrong edit here can
produce a wrong *verdict*, leak data, corrupt persisted state, or break a contract another layer
already trusts:

| area | why |
| :--- | :--- |
| `component/nusmv/`, `component/fuzz/` | a wrong model produces confident false verdicts |
| `device-template-schema.json`, `deviceTemplate/` | the authoring contract and bundled semantics |
| `security/`, `filter/`, `*Auth*`, `*Jwt*`, `*RateLimit*` | authentication, authorization, rate limiting |
| `db/`, `po/`, `repository/` | migrations and persistence mapping |
| `dto/`, `controller/` | cross-layer REST contracts |
| `frontend/src/{stores,router,api}/` | cross-cutting frontend state |
| `frontend/src/utils/{modelRequest,device,modelSemantics}.ts` | shared model contract |
| `.github/`, `playwright.config`, `e2e/`, `pom.xml`, `package-lock.json` | the pipeline and its harness |

**Unrecognised paths escalate.** A new top-level directory has unbounded blast radius, so failing
safe costs a slow pipeline while failing open ships something nothing validated.

To add a rule, state *why* in the same commit. The test suite asserts every reason is non-trivial so
the list stays a standard rather than folklore.

## Tier 3 — Live AI (`live-ai-ci.yml`)

The two tests that call a real external model endpoint, on their own gate: nightly and on demand,
never a merge blocker. Three reasons:

- A provider outage would fail the run for reasons unrelated to the commit. This repo has already seen
  it — a different one of the two tests failed on consecutive runs with identical code. A required
  check that goes red on someone else's outage teaches people to ignore red checks.
- It costs real quota per run.
- It needs a secret, unavailable to fork pull requests.

It is the only tier without `--fail-on-flaky-tests`, for the same reason: a transport failure is not a
defect in this repository.

## Caching

| cached | key derived from | why it is safe |
| :--- | :--- | :--- |
| Maven repository | `pom.xml` (via `setup-java`) | immutable released artifacts |
| npm modules | `package-lock.json` (via `setup-node`) | lockfile pins exact versions |
| Playwright browsers | resolved Playwright version + OS | a dependency bump misses, so new test code never runs against an old browser |
| NuSMV 2.7.1 | version + sha256 + OS + arch | fixed URL, verified digest; the runner image is in the key because the binary links against system libraries |

**Deliberately not cached:** the MySQL and Redis service containers, the compiled backend jar across
runs, build outputs, and apt packages. Caching mutable application state or generated results is how a
pipeline starts hiding the defect it exists to catch. The jar *is* passed between jobs within one run
as an artifact, which is reuse of a verified build rather than a stale one.

## Other decisions

- **Concurrency cancellation** on non-`main` refs. A superseded push is wasted capacity and leaves a
  misleading red X on an old commit. `main` never cancels: every landed commit needs its own verdict.
- **Fail-fast ordering**: route → typecheck → unit → build → smoke. Each stage is cheaper than the one
  it gates.
- **Artifact reuse**: the backend jar and frontend bundle are built once and downloaded by the E2E
  tier, replacing a 33s recompile and a second `npm ci`.
- **Shared startup**: [`run-e2e.sh`](../../.github/scripts/run-e2e.sh) owns the readiness probe and
  process lifecycle for all three tiers. Duplicated inline in YAML, a subtly different probe in one job
  reports "never became ready" for a backend that was fine.
- **Aggregate status check**: `fast-ci` succeeds only if no required tier failed, so branch protection
  can require one stable check name instead of a list that changes whenever routing does.

## Branch protection

Require exactly one check: **`Fast CI / fast-ci`**. It rolls up the routed tiers, so a docs-only PR is
green in about a minute without weakening anything, and a high-risk PR still cannot merge until its
escalated Full CI run passes.

Do not require `Full CI` directly — on a low-risk PR it never runs, and a required check that never
runs blocks every such PR forever.

## Local equivalents

```bash
node --test .github/ci-risk-router.test.mjs   # routing logic
cd backend  && mvn test                       # backend suite
cd frontend && npm run test:unit -- --run     # frontend unit
cd frontend && npm run test:e2e               # full E2E (needs MySQL + Redis + NuSMV)
```

To see how a change would route:

```bash
CHANGED_PATHS="$(git diff --name-only origin/main)" node .github/ci-risk-router.mjs
```
