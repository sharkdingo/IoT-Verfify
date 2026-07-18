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

## Commands

```bash
npm install
npm run dev        # dev server :3000, proxies /api → http://localhost:8080
npm run build      # vue-tsc type-check + production build (run this to verify)
npm run preview
npm run test:unit  # Vitest
```

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
  router/     routes + auth guard
  views/      Landing / Board / NotFound
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

## Gotchas (the "why")

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

## Reference (link, don't duplicate)

- Backend API contracts: [../docs/api/rest-endpoints.md](../docs/api/rest-endpoints.md)
  and the domain docs under [../docs/api/](../docs/api/overview.md)
- Exploration contract and role: [../docs/api/fuzzing.md](../docs/api/fuzzing.md) and
  [../docs/architecture/fuzzing-flow.md](../docs/architecture/fuzzing-flow.md)
- Config / env vars: [../docs/getting-started/configuration.md](../docs/getting-started/configuration.md)
