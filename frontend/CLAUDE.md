# CLAUDE.md — IoT-Verify Frontend

Guidance for Claude Code when working in `frontend/`. Read the repo-root
[../CLAUDE.md](../CLAUDE.md) first for cross-cutting rules (doc-sync, language, git).
Detailed reference lives in [../docs/](../docs/README.md); when code and docs disagree,
**code wins — fix the doc in the same change**.

## What this is

Vue 3 + TypeScript single-page app (Vite) for the IoT-Verify platform: a visual device
canvas, rule/spec builders, bounded candidate-path exploration, verification + formal
counterexample visualization, an AI chat panel, and bilingual (zh-CN / en) UI. Talks to the Spring Boot backend over HTTP
(`Result<T>` JSON) plus one SSE stream for chat.

Stack: Vue 3 (Composition API), TypeScript, Vite, Tailwind CSS, Ant Design Vue,
Element Plus, Vue Router, Vue I18n.

This project is in active development and has no released compatibility contract.
Unless the user explicitly requests a migration path, remove superseded client contracts
and dead UI branches instead of adding legacy payload adapters, deprecated aliases, or
silent fallbacks for old development data.

## Commands

```bash
npm install
npm run dev        # dev server :3000, proxies /api → http://localhost:8080
npm run build      # vue-tsc type-check + production build (run this to verify)
npm run preview
npm run test:unit  # Vitest
npm run test:e2e   # Playwright; needs the backend on :8080
```

`test:e2e` takes minutes — delegate it to a background subagent (see the root CLAUDE.md) instead of
blocking on it, and keep reading source while it runs.

E2E runs against a **production build** served by `vite preview`, not the dev server: on-demand
module transforms made two parallel browsers exceed the board's load timeout, failing tests that had
nothing wrong with them. A failure that appears only under `--workers=2` is usually this class of
cause — diagnose it rather than forcing `--workers=1`, which hides it and triples the runtime. Two
further consequences worth knowing before you debug an E2E result:

- `vite.config.ts` needs its `/api` proxy declared under `preview` as well as `server` — `vite
  preview` does not inherit `server.proxy`.
- Port 3000 must be free. `reuseExistingServer` is off precisely so a leftover dev server cannot be
  adopted silently, which would skip the build and test **stale code** while reporting green. A
  `PreToolUse` hook (`.claude/hooks/guard-e2e-port.sh`) blocks the command while the port is held, so this
  is enforced rather than remembered. Free the port, or set `E2E_BASE_URL` to a server you manage — as an
  inline prefix or an exported variable, the hook accepts either. It only matches commands that actually
  start Playwright's web server, so a script that drives a browser or the API client against a server you
  are already running is not blocked.
- **A full E2E pass cannot succeed on the default auth rate limits.** `AUTH_SOURCE_REGISTER_RATE_LIMIT_PER_HOUR`
  defaults to **60**, and the suite makes **~67** `createAuthenticatedUser` calls, each of which registers an
  account. This note used to claim "a full run stays under the cap by design" on the strength of
  `sharedReadOnlyAccount` being worker-scoped; measurement says otherwise, and a false reassurance here is
  worse than no note — it sent several sessions hunting product defects in a wall of 429s.
  The limits are constructor-injected into `final` fields, so **exporting them next to the Playwright command
  does nothing**; they have to be set on the JVM under test. `e2e/global-setup.ts` now checks the budget once
  before any browser starts and prints the four variables and the reset time, so this is diagnosed rather than
  rediscovered. When it exhausts mid-run the failures scatter across the shared fixture and read exactly like
  regressions — check the `reasonCode` before believing any of them.
- **To actually run a full pass, start a second backend with raised caps and point the whole run at it.** Do
  not restart the one someone is developing against:

  ```bash
  # terminal 1 — a dedicated E2E backend, same database (the suite creates and deletes its own accounts)
  cd backend
  SERVER_PORT=8081 \
    AUTH_SOURCE_REGISTER_RATE_LIMIT_PER_HOUR=2000 AUTH_REGISTER_RATE_LIMIT_PER_HOUR=2000 \
    AUTH_SOURCE_LOGIN_RATE_LIMIT_PER_MINUTE=2000 AUTH_LOGIN_RATE_LIMIT_PER_MINUTE=2000 \
    mvn spring-boot:run > e2e-backend.log 2>&1

  # terminal 2
  cd frontend && E2E_API_BASE_URL=http://127.0.0.1:8081 npx playwright test
  ```

  One variable moves the whole run because `vite.config.ts` now reads it for the `/api` proxy target as well.
  It used to hardcode `localhost:8080` in both `server` and `preview`, so pointing a run elsewhere *silently
  half-worked*: the specs' direct API calls followed `E2E_API_BASE_URL` while the browser kept going to 8080,
  and one run talked to two servers. Redirect the API and the proxy together or not at all.
- **Raising only the register limit is not enough — the login ceiling is what a full run actually
  hits.** `AUTH_SOURCE_LOGIN_RATE_LIMIT_PER_MINUTE` (default 120) is a per-source, per-minute
  window, and `board-full-flow.spec.ts` logs in far more often than it registers. A run with only
  the register cap raised failed five board specs with `AUTH_LOGIN_RATE_LIMIT_REACHED`
  (`scope: SOURCE`) — including the account-cleanup fixture, which then reported a second,
  misleading error. Every failure was the rate limiter, not the product. Raise
  `AUTH_SOURCE_LOGIN_RATE_LIMIT_PER_MINUTE` and `AUTH_LOGIN_RATE_LIMIT_PER_MINUTE` alongside the
  register caps on the JVM under test, and read the `reasonCode` before believing a board failure.
- **A pointer position computed from the canvas is stale the moment you await.** CI runs with
  `--fail-on-flaky-tests`, so one retry-passing test still fails the job. The edge-label hover check
  measured a hitarea midpoint once and moved the mouse there; under CI load the canvas was still
  settling, the edge had moved, and no label appeared. Re-derive the coordinate *inside* the poll and
  re-hover each attempt rather than widening the timeout around a single stale move — the assertion
  keeps its original strength and stops depending on when the animation happened to land.
- **A route mock must satisfy the same validators as the real response.** `api/chat.ts` validates
  every field it depends on, so a fixture returning a convenient subset is rejected at the boundary —
  and the failure surfaces far from the cause. A session mock missing `active`/`userId`/`updatedAt`
  made session creation throw, so the turn never sent, so a `REFRESH_DATA` command never arrived, and
  the test failed on an unrelated undo-button assertion. When an E2E failure makes no sense, read the
  browser console in the Playwright trace (`--trace=retain-on-failure`) before theorising: two rounds
  of plausible guesses cost more than one look at the actual error.

## Codebase map

```
src/
  api/        HTTP layer:
              http.ts       axios instance + interceptors (token, 401 redirect)
              auth.ts       authApi — returns the full Result<T> (read .data)
              board.ts      default-export object: board CRUD + verification + fix
              chat.ts       named exports: sessions (axios) + SSE streaming (fetch)
              rules.ts      rules + rule recommendation (cancellable)
              simulation.ts default-export object: simulation calls
              fuzzing.ts    default-export object: exploration tasks/runs/findings
  types/      TypeScript contracts (auth, device, node, edge, rule, spec, verify, fuzzing, fix, …)
  stores/     reactive state (auth, chat)
  router/     index.ts       routes + auth guard (reads the auth store, never localStorage)
              loginRedirect.ts  the single owner of the "session gone → login" location
  composables/ useTheme, useModalAccessibility, useBodyScrollLock, useRovingTablist
  views/      Landing / Board / NotFound
              board/  Board.vue's extracted domain logic — pure, unit-tested modules with no
                      component dependencies (deep links, semantic commit, assistant refresh
                      targets, scene-import diagnostics, recommendation wording, portable scene)
  components/ CanvasBoard, ChatView, ControlCenter, SystemInspector,
              TraceHistoryPanel, SimulationTimeline, FixResultDialog,
              RuleBuilderDialog, DeviceDialog, AccountDeleteDialog, …
  assets/     static assets + i18n (zh-CN / en)
```

How the frontend calls the backend (real shapes, unwrapping, SSE):
[../docs/guides/frontend-integration.md](../docs/guides/frontend-integration.md).

## Conventions (hard rules)

- **Keep types aligned with backend DTOs.** Fields are camelCase on both sides
  (`userId`, not `user_id`). When a backend DTO changes, update the matching
  `src/types/*.ts` **and** the owning `docs/api/*.md` in the same change.
- **Two response-unwrapping conventions — do not mix them up:**
  - `board.ts` / `simulation.ts` / `fuzzing.ts` / `rules.ts` return **already-unwrapped** `T` (a local
    `unpack` returns `response.data.data`).
  - `authApi` returns the **full** `Result<T>` (`response.data`) — read `res.data.token`,
    not `res.token`, and check `res.code`.
- **`verifyAsync(req)` / `simulateAsync(req)` return the authoritative accepted task
  DTO**, including the server-generated `id`, current status/progress, and frozen
  `modelSnapshot`; the client does not pass an id in or fabricate a local task row.
  Acceptance does not mean the run completed.
- Verification/fix live on `boardApi` (there is **no** `api/verify.ts`); trace types
  live in `types/verify.ts` (there is **no** `types/trace.ts`).
- Counterexample exploration lives in `api/fuzzing.ts` and `types/fuzzing.ts`. A fuzz
  finding is replay-only candidate evidence: never expose the formal Fix action for it,
  and never render `BUDGET_EXHAUSTED` as safe or satisfied.
- Bilingual: user-facing strings go through Vue I18n (`assets` i18n, zh-CN + en) — do
  not hardcode display text. Backend/LLM free-text `message`, `reason`, `warning`, and
  `errorMessage` fields are technical diagnostics unless their contract explicitly says
  they follow the requested language. Prefer stable reason/status codes; otherwise use
  `utils/userMessage.ts` for ordinary fallback copy and keep the raw text in Technical
  Details or logs.

### Frontend anti-slop checks

- Keep one explicit owner for each server snapshot, local draft, pending mutation, and dialog
  intent. Background refreshes and late responses must not overwrite active edits or reopen a
  surface the user closed.
- Treat loading, empty, partial, stale, cancelled, unknown-outcome, and failed states as
  distinct. Never replace missing authoritative data with fabricated success, placeholder
  domain objects, or a toast that contradicts the persisted state.
- Reuse typed API validators and established composables. Avoid component-local copies of
  contract parsing, translation provenance, modal focus logic, or responsive breakpoints.
- Verify user workflows at narrow/short and desktop viewports, light and dark themes, keyboard
  and pointer input, low canvas zoom, slow responses, repeated actions, and cross-tab refresh
  whenever the touched surface can encounter them.
- Tests must assert accessible roles, user-visible outcomes, and authoritative reconciliation;
  do not couple them to obsolete raw tokens, CSS accidents, arbitrary sleeps, or mocks that
  bypass the failure being fixed.

## Gotchas (the "why")

- **The board's URL owns "which run is open", and nothing else.** `run=<kind>:<id>` plus
  `trace`/`finding` are the only deep-linked state; panel layout, widths, `activeSection`,
  and canvas pan/zoom are persisted server-side per user via `BoardLayoutDto`, so putting
  them in the URL would create a second authority. Openers navigate and a single watcher
  applies the URL — never assign result state and the URL separately. Opening is `push`,
  correcting/clearing is `replace`. Rules and the full inventory:
  [../docs/guides/frontend-ui-conventions.md](../docs/guides/frontend-ui-conventions.md).
- **A disabled submit must say why, inline.** Derive the disabled state and the message from
  one `*BlockedReason` computed and link it with `aria-describedby`; never also toast what the
  form already shows. Result-surface closers come in pairs: `close*` for internal transitions
  (which must not touch the URL) and `dismiss*` for a user-facing close (which clears the deep
  link). Getting this backwards makes a replay strip its own link, or leaves `run=` behind so
  the sync reopens the surface the user just closed.
- **Validate response cross-field invariants in both directions.** A one-way check leaves the
  mirror case free to fabricate: a `VERIFIED` strategy attempt with no suggestion passed because
  `fixable` is derived from suggestions alone, and a scenario could apply a whole scene while
  reporting zero inspected candidates because only the standalone path tied `validatedCount` to its
  kept items. When a count or status claims evidence, assert the evidence exists — and prefer a
  bound over an equality where a legitimate case differs (a synthesized adjustment adds an applied
  item with no validated candidate behind it).
- **Undo reverses a persisted board edit — nothing else.** It is not cancel, stop, delete-result,
  dialog close, or browser Back; each of those has its own control. The server journal is the
  authority: `useBoardUndo` keeps no snapshot stack, applies the authoritative collections the
  response carries, and reads availability from `/board/edits/availability`. Never intercept
  `Ctrl+Z` in an input, textarea, `contenteditable`, or during an IME composition
  (`boardUndoShortcut.ts` owns that scoping). Reversible: device create/update/rename/delete, direct
  Environment Pool edits, rule/spec create+delete, rule reorder, and automatic-fix apply. Device
  deletion is one compound entry containing its cascades and Environment Pool state; automatic fix
  is one ordered rule-set entry. Confirmed scene replace/clear, template deletion, and default-template
  reset are history boundaries because they can remove or replace manifest semantics used by snapshots.
  Show the server-reported history count before confirmation and re-read availability afterward.
  Clearing an unusable journal is separately confirmed and
  carries the exact `/board/edits/clear-preview` token; stale confirmation must preserve history.
  A non-`409` undo/redo failure is an unconfirmed mutation outcome, not proof that the board stayed
  unchanged: reconcile the complete snapshot through the mutation queue before reporting it. A
  `409` wrote nothing but still triggers reconciliation because the local board may be stale.
- **Shrink `Board.vue` by extracting rules, not by adding layers.** Worthwhile moves take their
  inputs as arguments (including `t`/`locale`) and land in `views/board/` or `utils/` with tests:
  boundary parsing, wording, decision tables, freshness predicates. Do **not** extract code needing
  many injected reactive getters — that trades size for indirection, the pass-through layer the root
  CLAUDE.md forbids. Two things that look extractable but are not: the four recommendation panels
  diverge in most of their markup (a shared component would need more slots than it saves), and the
  fuzzing refs are interleaved with simulation and task-inbox state rather than contiguous.
- **Every ordinary targeted device/Environment Pool/rule/spec mutation commits through
  `board/semanticCommit.ts`.** It applies the
  authoritative collections and then everything derived from them — canvas edges, dangling
  inspector focus, undo availability, verdict staleness — in a fixed order. Never hand-assemble
  those follow-ups at a call site: that is what let reorder skip undo availability and undo skip
  the canvas edges, each hidden by a later refresh that happened to repair the state. An undo is
  itself a semantic mutation, so it uses this path and must match `isBoardMutationRequest`. Pass
  `semanticChanged: false` only for an explicit server-confirmed no-op; it still reconciles state and
  availability without making a current verdict stale. Authoritative partial/full refreshes are not
  mutations, but they must reuse `reconcileBoardFocus` so removed items cannot remain selected.
- **A path that changes the undo journal must re-read it.** Scene replace/clear calls
  `notifyUndoJournalCleared()`; reversible mutations carry availability or reload it, and a wholesale
  semantic reload (`refreshBoardSnapshot`) re-reads availability explicitly at the end. A board
  invalidation does
  **not** cover the publishing tab — `BroadcastChannel` never delivers to the context that posted,
  and `publishBoardInvalidation` only calls `postMessage` — so the origin tab depends on that
  explicit re-read, not on its own broadcast. The assistant relies on it, so an assistant-created
  device or rule is as undoable as a user-created one (`views/board/assistantRefresh.ts` owns the target
  table; verified against the real model in `e2e/live-ai-no-mock.spec.ts`). The assistant cannot
  delete in one turn — destructive tool actions need a confirmation token, so do not write features
  assuming otherwise. Availability reads run outside the mutation queue: every mutation response
  carrying availability must invalidate older reads, and only the latest concurrent read may land.
- **All user feedback goes through `utils/feedback.ts`.** Call sites state the intent
  (`notifySuccess`/`notifyInfo`/`notifyBlocked`/`notifyError`, `confirmDestructive`,
  `acknowledge`), never `ElMessage`/`ElMessageBox` directly — that is what kept 421 toast
  call sites and three different confirmation styles from agreeing. A success whose result is
  already visible on screen gets **no** toast. Field validation is inline, not a toast. A
  failed load that leaves state unknown is a persistent banner, not a toast.
- **One owner for "the session is gone".** The axios 401 interceptor, the SSE transport,
  and `App.vue`'s auth watcher all route through `router/loginRedirect.ts`. Never build a
  second `{ path: '/', query: { mode: 'login', redirect } }` literal, and never re-read
  `localStorage` to decide whether the user is signed in — the auth store is authoritative
  (it initializes from storage at module load, before the first guard runs). The route guard
  calls `revalidateSession()`, which drops a session whose JWT expired while the tab stayed
  open; `isLoggedIn` alone is only decided at load/login and would keep reading as true.
- **Complementary media queries must split at one value.** Write
  `max-width: 1023.98px` / `min-width: 1024px`, never `1023px` / `1024px`: a fractional
  viewport width (routine on scaled displays) matches neither rule, so an element gets
  neither the narrow nor the wide layout. The same applies to `max-height: 599.98px` and to
  any hand-written breakpoint that must not overlap a Tailwind prefix — `sm:` starts at
  640px, so its compact counterpart ends at 639.98px.
- **`role="dialog"` implies a focus trap.** The board's floating tool panels
  (verification, simulation, the four recommendation panels, fuzzing, run history) are
  non-modal on purpose: the canvas stays live and `useModalAccessibility` is given
  `trapFocus: false`. Those are `role="region"`. Anything that claims
  `role="dialog"` + `aria-modal="true"` must keep the trap — and therefore also gets the
  background scroll lock, which `useModalAccessibility` applies for exactly that case. A trapping
  modal also gets a document-level Escape fallback: the element-bound handler only sees the key once
  focus is inside the dialog, and focus arrives a tick later, so a deep link that opens the surface on
  load had its first Escape silently dropped. Non-modal panels are excluded — one keypress must not
  close several of them. Element-bound handlers must also ignore an already-default-prevented event,
  so an Escape consumed by a nested modal cannot bubble on and close its ancestor.
- **"Modal to the user" is not the same as "takes the scroll lock".** `openModalDepth`
  (`useBodyScrollLock`) is what tells window-level accelerators such as the board's Ctrl+Z that a
  surface is covering the board. Element Plus `MessageBox` confirmations pass `lockScroll: false` on
  purpose — the board shell is a fixed `100vh` surface that Element Plus's scrollbar compensation
  would shift — so they register depth through `registerModalSurface()` in `utils/feedback.ts`
  instead. Wiring depth to the scroll lock alone left every `confirmDestructive` window unguarded,
  and Ctrl+Z reversed the previous edit behind the prompt.
- **A `clamp()` whose middle term can never win is a fixed size wearing responsive syntax.** `cqmin` is a
  percentage of the *container*, so on a 110–137px canvas node `4.3cqmin` is 4.7–5.9px: the declared floor
  was the rendered size at every viewport, and three node declarations printed 9.28px and 10px under an
  11px minimum. Before writing a sub-floor floor, compute what the preferred term evaluates to at the
  container's real size — and if a test exempts the pattern, the exemption needs a measurement, not a
  comment. `typographyFloor.spec.ts` exempted these on a claim that they "render at 16px", which was
  false, so the check certified the defect it existed to catch. `--canvas-zoom` is the one legitimate
  exemption because it *divides*: 11px at 1.0× becomes 14.4px at 0.4×.
- **A semantic role has an ink half and a paper half.** `--accent`/`--danger`/`--warning`/`--success` are
  tuned as *text*, so the dark theme lightens them — and a fill under light ink inverts that (measured 1.44 to
  2.54:1 across 60 sites, light theme passing throughout, which is why a light-only check misses it). Fill with
  `--<role>-fill`; a fill carrying no ink keeps the bare role. Disable by desaturating, never by fading
  opacity, which fades the label with it. Structural neutrals have a floor: `slate-400` is 2.56:1 on white.
  Values, tables and the reasoning:
  [../docs/guides/frontend-ui-conventions.md](../docs/guides/frontend-ui-conventions.md) §5.
- **A `position: fixed` overlay cannot read a variable scoped to the board.** `--board-floating-gap`,
  `--board-control-width` and `--board-inspector-width` are declared on `.iot-board`, but the two timeline hosts
  are **siblings** of it — deliberately, so they float above every panel. Inside them those variables do not
  resolve, `calc()` becomes invalid at computed-value time, and `left`/`right` fall back to `auto`. A fixed box
  with both set to `auto` shrink-wraps its content at its static position, i.e. flush against x=0. Measured: the
  trace overlay sat hard against the left edge with the right half of a 2556px screen empty, and its width was
  *identical* at 2556 and 1440 (859.859px) — that identity is the tell, because a corridor-positioned element
  must change with the viewport. On a 101-state trace the shrink-wrap reached **3258px** and put the play button
  at x=2086, off-screen at a laptop viewport, so playback became unreachable.
  `var(…, 1rem)` fallbacks had been hiding this, and removing them as "dead text" is what exposed it — the
  premise that the gap lives at `:root` was wrong, and a test comment had recorded that wrong premise. Restoring
  a fallback only hides it again: inject the variables onto the fixed element (`boardShellStyle` does this) so it
  is positioned by values it can see. `boardDockGeometry.spec.ts` pins the injected value against the stylesheet's.
- **Stacking order is a named scale, not a literal.** Add a layer to the `--z-*` block in
  `styles/base.css` and reference it (`z-[var(--z-modal)]` in Tailwind,
  `var(--z-modal)` in CSS). Values inside a component's own stacking context stay local
  and small. A raw four-digit `z-index` is a bug.
- **Side panels are optionally controlled.** `ControlCenter` / `SystemInspector` accept
  `activeSection` but must not declare a default for it: a default makes the prop look
  permanently "controlling", which silently discards internal selection changes when no
  parent is managing it.

- **Base URL comes from one place, relative by default.** Both `http.ts` (axios,
  appends `/api`) and `chat.ts` (SSE) read `import.meta.env.VITE_API_BASE_URL`. Empty
  (default) → relative `/api` via the Vite/Nginx proxy; set an absolute URL only for
  cross-origin. Don't hardcode an absolute `localhost` URL (it bypasses the dev proxy
  and, in prod, points at the user's own machine). See
  [../docs/guides/frontend-integration.md](../docs/guides/frontend-integration.md).
- **Chat streaming bypasses axios**: `sendStreamChat` uses native `fetch` +
  `response.body.getReader()`, so it sets the `Authorization` header manually and the
  axios interceptors do not apply. Protocol:
  [../docs/api/chat-sse.md](../docs/api/chat-sse.md).
- **Rule references are node-id authoritative.** `RuleBuilderDialog` stores new rule
  source/target device references as canonical `DeviceNode.id` values; labels are only
  shown to users. Never synthesize dummy trigger conditions in `board.ts`; validate and
  surface an error instead.
- **Verification warnings are user-visible.** `disabledRuleCount`,
  `skippedSpecCount`, and `[rule-disabled]` / `[spec-skipped]` entries in `checkLogs`
  must be shown even when `safe === true`.
- **Own a streaming row by identity, never by position.** The assistant's in-flight row is found by
  `turnId`: "load older messages" prepends a page and shifts every array index, which sent chunks
  and terminal status into an archived message. Browsing history during a stream is legitimate — do
  not "fix" this class of bug by disabling the operation.
- **Staleness belongs to the run, not to the dialog showing it.** `lastSimulationResult` survives
  every dialog close while `simulationResult` does not, so flag and clear against the surviving run.
  Closing a surface is not a fresh result and must not clear a stale flag; only a new run is.
- **A displayed verdict only describes the model that was verified.** Any semantic board
  change (applying a fix, editing rules/specs/devices from the inspector or chat) makes an
  open verification result stale: `Board.vue` flags it from the single semantic-scene-change
  hook in the mutation queue, then withdraws the per-counterexample Fix action and shows the
  re-run banner. Counterexample replay remains available because it renders the run's frozen
  scene rather than the current canvas. Never let a stale verdict keep offering actions that
  imply it describes the current canvas, and always clear the flag when a fresh result is
  presented.
- **Run history has two user layers.** Task Status contains only active or no-result
  failed/cancelled jobs. History Results contains one item per completed verification
  or saved simulation; verification counterexamples are nested summary evidence, not
  peer runs. Load full run/trace states only when opened, and keep malformed rows as
  unavailable placeholders rather than failing the whole list.
- **Exploration is background-only.** Closing its panel must not cancel the accepted
  task; keep it visible in the global task indicator/inbox and move completed work into
  History Results with nested finding summaries.
- **A stopped chat transport is not a cancelled tool operation.** Wait for the session
  activity endpoint to become idle before switching/deleting the session or allowing a
  new assistant mutation, then reconcile board and run-history state. Match the reloaded
  terminal assistant row by `turnId`; never let an older completed turn replace the current
  local request.
- **Chat history is cursor-paged.** Preserve `nextBeforeId`/`hasMore`, prepend older
  pages without replacing recent messages, and remove optimistic turns only when the
  SSE request was rejected before transport acceptance.

## Reference (link, don't duplicate)

- Backend API contracts: [../docs/api/rest-endpoints.md](../docs/api/rest-endpoints.md)
  and the domain docs under [../docs/api/](../docs/api/overview.md)
- Exploration contract and role: [../docs/api/fuzzing.md](../docs/api/fuzzing.md) and
  [../docs/architecture/fuzzing-flow.md](../docs/architecture/fuzzing-flow.md)
- Config / env vars: [../docs/getting-started/configuration.md](../docs/getting-started/configuration.md)
