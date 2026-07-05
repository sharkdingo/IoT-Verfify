# CLAUDE.md — IoT-Verify Frontend

Guidance for Claude Code when working in `frontend/`. Read the repo-root
[../CLAUDE.md](../CLAUDE.md) first for cross-cutting rules (doc-sync, language, git).
Detailed reference lives in [../docs/](../docs/README.md); when code and docs disagree,
**code wins — fix the doc in the same change**.

## What this is

Vue 3 + TypeScript single-page app (Vite) for the IoT-Verify platform: a visual device
canvas, rule/spec builders, verification + counterexample visualization, an AI chat
panel, and bilingual (zh-CN / en) UI. Talks to the Spring Boot backend over HTTP
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
  types/      TypeScript contracts (auth, device, node, edge, rule, spec, verify, fix, …)
  stores/     reactive state (auth, chat)
  router/     routes + auth guard
  views/      Landing / Login / Register / Board / TemplateCreate / NotFound
  components/ CanvasBoard, ChatView, ControlCenter, SystemInspector,
              TraceVisualization, SimulationTimeline, FixResultDialog,
              RuleBuilderDialog, DeviceDialog, …
  assets/     static assets + i18n (zh-CN / en)
```

How the frontend calls the backend (real shapes, unwrapping, SSE):
[../docs/guides/frontend-integration.md](../docs/guides/frontend-integration.md).

## Conventions (hard rules)

- **Keep types aligned with backend DTOs.** Fields are camelCase on both sides
  (`userId`, not `user_id`). When a backend DTO changes, update the matching
  `src/types/*.ts` **and** the owning `docs/api/*.md` in the same change.
- **Two response-unwrapping conventions — do not mix them up:**
  - `board.ts` / `simulation.ts` / `rules.ts` return **already-unwrapped** `T` (a local
    `unpack` returns `response.data.data`).
  - `authApi` returns the **full** `Result<T>` (`response.data`) — read `res.data.token`,
    not `res.token`, and check `res.code`.
- **`verifyAsync(req)` returns the server-generated `taskId`** (`Promise<number>`); the
  client does not pass a taskId in.
- Verification/fix live on `boardApi` (there is **no** `api/verify.ts`); trace types
  live in `types/verify.ts` (there is **no** `types/trace.ts`).
- Bilingual: user-facing strings go through Vue I18n (`assets` i18n, zh-CN + en) — do
  not hardcode display text.

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
- **Rule references are label-first.** `RuleBuilderDialog` stores new rule source/target
  device references as `node.label`; lookup code must continue accepting legacy node ids.
  Never synthesize dummy trigger conditions in `board.ts`; validate and surface an error
  instead.
- **Verification warnings are user-visible.** `disabledRuleCount`,
  `skippedSpecCount`, and `[rule-disabled]` / `[spec-skipped]` entries in `checkLogs`
  must be shown even when `safe === true`.

## Reference (link, don't duplicate)

- Backend API contracts: [../docs/api/rest-endpoints.md](../docs/api/rest-endpoints.md)
  and the domain docs under [../docs/api/](../docs/api/overview.md)
- Config / env vars: [../docs/getting-started/configuration.md](../docs/getting-started/configuration.md)
