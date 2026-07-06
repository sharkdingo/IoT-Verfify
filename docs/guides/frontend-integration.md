# Frontend Integration Guide

How the Vue 3 frontend calls the backend: the HTTP client, the API modules and their
real shapes, SSE streaming, and where the TypeScript types live. This replaces the
old `frontend/API-DOCUMENTATION.md`, which had drifted from the code.

Verified against code on 2026-07-06. Source: `frontend/src/api/`, `frontend/src/types/`.

---

## Directory layout (actual)

```
frontend/src/
├── api/
│   ├── http.ts          # Axios instance (interceptors, unpack lives in board.ts)
│   ├── auth.ts          # authApi — auth calls
│   ├── board.ts         # default-export object: board CRUD + verification + fix
│   ├── chat.ts          # named exports: sessions + SSE streaming
│   ├── rules.ts         # rule recommendation only (persistence lives in board.ts)
│   └── simulation.ts    # default-export object: simulation calls
└── types/
    ├── auth.ts   canvas.ts   chat.ts   device.ts   edge.ts   fix.ts
    ├── node.ts   panel.ts    rule.ts   simulation.ts   spec.ts   verify.ts
```

> There is **no** `api/verify.ts` and **no** `types/trace.ts`. Verification calls live
> in `board.ts`; trace types (`Trace`, `TraceState`, `TraceDevice`, …) live in
> `types/verify.ts`.

---

## HTTP client — `api/http.ts`

Axios instance:

- `baseURL: (import.meta.env.VITE_API_BASE_URL || '') + '/api'`
- `timeout: 100000` (100 s)
- Request interceptor: attaches `Authorization: Bearer <token>` from the auth store.
- Response interceptor: on HTTP `401`, clears auth state and redirects to `/login`
  (skips `/login` and `/register` to avoid a loop).

> **Base URL is uniform and relative by default.** Both `http.ts` (axios, most modules)
> and `chat.ts` (SSE) derive their base URL from `import.meta.env.VITE_API_BASE_URL`.
> When it is empty (the default), requests go to a relative `/api`, which the Vite dev
> server proxies (`vite.config.ts`) and a production reverse proxy (Nginx) forwards —
> so dev and same-origin prod work with no config. Set an absolute
> `VITE_API_BASE_URL` only for cross-origin deployments. See
> [../getting-started/configuration.md](../getting-started/configuration.md#frontend-vite).

---

## Response unwrapping — two conventions

The backend wraps everything (except SSE) in the `Result<T>` envelope (authoritative
definition: [../api/overview.md](../api/overview.md)). What this guide owns is that the
frontend does **not** unwrap it uniformly:

| Module | Returns | Caller must read |
| :--- | :--- | :--- |
| `board.ts`, `simulation.ts`, `rules.ts` (rule recommendation only) | already-unwrapped `T` (via a local `unpack` that returns `response.data.data`); `boardApi.saveRules(...)` is the intentional exception and returns `void` | the value directly, except re-fetch rules after `saveRules` if server-assigned ids are needed |
| `auth.ts` | the full `Result<T>` (returns `response.data`) | `.data` for the payload, `.code` for status |

So `authApi.login(...)` resolves to `Result<LoginResponse>` — read `result.data.token`,
**not** `result.token`. This asymmetry is real; mirror it in components.

---

## Auth — `api/auth.ts`

Exported as an object `authApi` (not named functions):

| Method | HTTP | Endpoint | Returns |
| :--- | :--- | :--- | :--- |
| `authApi.login(data)` | POST | `/auth/login` | `Result<LoginResponse>` |
| `authApi.register(data)` | POST | `/auth/register` | `Result<RegisterResponse>` |
| `authApi.logout()` | POST | `/auth/logout` | `Result<void>` |

`LoginResponse` carries `userId`, `phone`, `username`, `token` (all camelCase). See
[../api/overview.md](../api/overview.md) for the general `Result<T>` envelope,
and the backend `dto/auth/` for request field rules (phone regex, username/password
length).

Example:

```ts
import { authApi } from '@/api/auth';

const res = await authApi.login({ phone: '13800138000', password: '123456' });
if (res.code === 200) {
  const { userId, token } = res.data; // note: res.data, not res
}
```

---

## Board + verification + fix — `api/board.ts`

`board.ts` default-exports one object that covers board CRUD **and** verification/fix.
Its methods return already-unwrapped values. Non-exhaustive:

- Board CRUD: `getNodes`/`saveNodes`, `getSpecs`/`saveSpecs`, `getRules`/`saveRules`,
  `getLayout`/`saveLayout`, `getActive`/`saveActive`. `getEdges`/`saveEdges` remain
  available for optional persisted canvas-geometry edges, but the current Board view
  derives visible rule connections from `rules`.
- Templates: `getDeviceTemplates`, `addDeviceTemplate`, `deleteDeviceTemplate`, `reloadDeviceTemplates`.
- Recommendation: `recommendRelatedDevices`, `recommendSpecifications`.
- Verification: `verify(req)`, `verifyAsync(req): Promise<number>`, `getTasks`,
  `getTask`, `getTaskProgress`, `cancelTask`, and trace list/detail/delete.
- Fix: `getFaultRules(traceId)`, `fixTrace(traceId, request?)`.

> **`verifyAsync` signature**: `verifyAsync(req): Promise<number>` — it takes only the
> request and resolves to the **server-generated** `taskId`. The client does not pass
> a taskId in.
> If this promise rejects with validation (`400` DTO errors or `422` service/runtime
> errors) or service-unavailable errors, no pollable task id exists for the UI flow;
> show the submit error and do not start polling.

Rules sent through `saveRules`, `checkDuplicateRule`, `verify`, or `simulate` must have
at least one concrete trigger source. The frontend stores new rule source/target device
references as device labels (legacy node ids are still resolved for old board data), and
`board.ts` maps them to backend `RuleDto.conditions` / `command`.

`saveRules` deliberately returns `Promise<void>` even though the backend responds with
saved `RuleDto[]`; callers that need persisted ids should call `getRules()` after the
save so the backend shape is mapped back to `RuleForm`.

Async pattern:

```ts
import boardApi from '@/api/board';

const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));

const taskId = await boardApi.verifyAsync(request);   // server returns the id
let task;

while (true) {
  const progress = await boardApi.getTaskProgress(taskId);
  task = await boardApi.getTask(taskId);               // VerificationTask
  if (task.status === 'COMPLETED' || task.status === 'FAILED' || task.status === 'CANCELLED') {
    break;
  }
  await sleep(2000);
}

// cancel: await boardApi.cancelTask(taskId);
```

Use a serial `while`/`await sleep` loop rather than `setInterval(async ...)` so polling
does not re-enter while a previous request is still in flight. Keep any page-level
`isVerifying`/loading state alive until this loop exits, including the cancelled and
failed terminal states.
When a board view unmounts, stop client-side polling and skip any late state writes.
The backend task should keep running unless the user explicitly calls the cancel API.
For a background-task UI, do not trap the user inside the submit panel. Allow the panel
to close, keep a global mini task indicator visible while active tasks exist, and expose
`GET /api/verify/tasks` plus `GET /api/simulate/tasks` through a task inbox so users can
recover in-progress tasks after refreshing the page.
When a task is already being watched through the 1s per-task polling loop, pass
`excludeTaskIds` to the summary-list refresh so the inbox does not fetch and merge the
same task redundantly; keep the locally watched task in the list until the watch loop
ends.

User-facing verification modes should distinguish behavior, not implementation jargon:
synchronous `verify` waits on the current page and returns the result directly;
asynchronous `verifyAsync` creates a pollable task with progress/cancel controls and
task-backed results.

Verification results and completed async verification tasks include `disabledRuleCount`
and `skippedSpecCount`, and generation warnings appear in `checkLogs` with
`[rule-disabled]` / `[spec-skipped]` markers. UI code must surface these warnings even
when `safe === true`, because they mean the generated SMV model omitted or degraded part
of the requested rules/specs.

Completed async verification tasks also expose `specResults` and `nusmvOutput`,
matching synchronous verification results. Completed async simulations expose their raw
NuSMV output through the persisted `SimulationTraceDto` referenced by
`simulationTraceId`.

Verification `specResults` is an array of `{ specId, passed, expression }` objects for
the specifications actually emitted to NuSMV. Frontend code should key rows and maps by
`specId`; the array order is the verifier-emission order, not necessarily the current
canvas display order. A completed verification can be `safe=false` with an empty
`specResults` array when generation emitted no specifications or NuSMV produced no
trustworthy per-spec result; show that as an unreliable/incomplete verification, not as
"all specifications passed".

Verification requests (`verify` and `verifyAsync`) must include at least one specification.
Simulation remains the no-spec workflow.

Contracts for board storage and board recommendation endpoints live in
[../api/board.md](../api/board.md). Contracts for verification, traces, and fix live in
[../api/verification.md](../api/verification.md).

Template manifests submitted through `addDeviceTemplate` must match
`backend/device-template-schema.json` exactly. The frontend may normalize legacy upload
files into the PascalCase schema shape before submission, but it should not send
lower-case aliases or extra fields and should keep `API.Trigger` as `null`; transition
conditions belong in `Transitions[].Trigger`. The backend validates the raw manifest
before DTO mapping, so schema violations return a `400` instead of being silently
ignored.

---

## Simulation — `api/simulation.ts`

Default-export object: `simulate`, `simulateAsync (→ Promise<number>)`, `getTasks`,
`getTask`, `getTaskProgress`, `cancelTask`, `simulateAndSave`, `getUserSimulations`,
`getSimulation`, `deleteSimulation`. Same unwrap convention as `board.ts`.
Like `verifyAsync`, `simulateAsync` resolves to a server-generated task id only after
the backend has accepted the task. If the promise rejects with validation or
service-unavailable errors, do not start polling.
Synchronous `simulate` and `simulateAndSave` also reject invalid requests instead of
returning a success-shaped empty result, so UI error handling should use the same submit
error path as async simulation.
For users, present simulation modes as "preview now" versus "save in background": plain
`simulate` previews immediately and does not persist a trace, `simulateAndSave` previews
and stores the synchronous trace, and `simulateAsync` stores the trace automatically when
the task completes. A background simulation completion should update the task inbox and
saved-run history instead of forcibly opening the timeline over the user's current work.

## Rule recommendation — `api/rules.ts`

This module owns **rule recommendation only**: named exports `recommendRules` and
`cancelRecommendRules` (cancellable via `cancelRecommendRules()`), plus a default-export
object of the same two. **Rule persistence is not here** — `getRules`/`saveRules` live on
`boardApi` (`api/board.ts`), which does the `RuleDto` ↔ `RuleForm` mapping and the
incremental-upsert. (A duplicate `getRules`/`saveRules` previously existed in this module
but was dead and has been removed.)

---

## Chat (SSE) — `api/chat.ts`

Named exports. Session management (`getSessionList`, `createSession`,
`getSessionHistory`, `deleteSession`) uses axios; **streaming does not**.

`sendStreamChat(...)` uses the native `fetch` API against
`${VITE_API_BASE_URL || ''}/api/chat/completions` (relative by default, so it also goes
through the proxy) and reads the response body with `response.body.getReader()` (SSE).
This is the one place the axios
instance and its interceptors are bypassed — the `Authorization` header must be set
manually here. Protocol detail: [../api/chat-sse.md](../api/chat-sse.md).

---

## Types

Backend↔frontend field alignment worth noting:

- `types/spec.ts` `SpecCondition` (`side`, `deviceId`, `deviceLabel`, `targetType`,
  `key`, `relation`, `value`) and `Specification`
  (`aConditions`/`ifConditions`/`thenConditions`) match the backend
  `SpecConditionDto` / `SpecificationDto` shape. For spec conditions the backend
  validates `deviceId` as required; the frontend sends both `deviceId` and
  `deviceLabel`, resolving legacy node ids to labels before request construction.
- `types/verify.ts` holds `VerificationRequest`, `VerificationResult`,
  `VerificationTask`, generation warning counts, and the trace types.
- `types/fix.ts` holds fix-related types.
- **Runtime option lists** (`relationOperators`, `targetTypes`, `specTemplateDetails`)
  live only in `assets/config/specTemplates.ts` — that is the single source components
  import. Do not reintroduce copies in `types/spec.ts`.
- **Known intentional parallelism**: `types/simulation.ts` (`SimulationState` /
  `SimulationDevice` / `SimulationVariable` / `SimulationTrustPrivacy`) and the
  `types/verify.ts` trace types both mirror the backend `TraceStateDto` tree. They are
  kept as two near-identical trees on purpose (verification vs simulation consumers);
  this is deliberate parallelism, not accidental duplication. They are **not fully
  isomorphic** — e.g. `TraceTrustPrivacy.trust` is `boolean | null` and `privacy` is
  required (closely mirroring backend `TraceTrustPrivacyDto`: `Boolean trust`, `String
  privacy`), whereas `SimulationTrustPrivacy` uses the looser `trust?: boolean` /
  `privacy?: string`. When a **backend field** changes, keep the shared shape aligned on
  both sides; but each side may keep its own optionality/nullability to suit its
  consumers.

When a backend DTO changes, update the corresponding `types/*.ts` and this guide in
the same PR (see [../../CONTRIBUTING.md](../../CONTRIBUTING.md)).
