# Architecture Overview

System topology, the front/back boundary, and the backend package layout. Deep dives
link out to the focused architecture documents.

Verified against code on 2026-07-05. Source: `backend/src/main/java/cn/edu/nju/Iot_Verify/`,
`frontend/src/`.

---

## Topology

```
┌─────────────┐   HTTP / SSE    ┌──────────────────────┐   process    ┌─────────┐
│  Vue 3 SPA  │ ──────────────▶ │   Spring Boot API    │ ───────────▶ │  NuSMV  │
│ (Vite:3000) │ ◀────────────── │      (:8080)         │ ◀─────────── │ 2.6–2.7 │
└─────────────┘   Result<T>     └──────────┬───────────┘   stdout      └─────────┘
                                           │
                                  ┌────────┴────────┐
                                  │ MySQL   Redis   │  (Redis fail-open)
                                  │  LLM endpoint   │  (OpenAI-compatible; AI, SSE streaming)
                                  └─────────────────┘
```

- **Frontend**: Vue 3 + TypeScript + Vite SPA. Talks to the backend over HTTP
  (`Result<T>` JSON) and one SSE stream for chat. See
  [../guides/frontend-integration.md](../guides/frontend-integration.md).
- **Backend**: Spring Boot REST API. Owns auth, canvas persistence, NuSMV
  orchestration, auto-fix, and the AI assistant.
- **NuSMV**: external model checker invoked as a subprocess (semaphore-bounded).
- **Stores**: MySQL (persistence), Redis (JWT blacklist, fail-open), and an
  OpenAI-compatible LLM endpoint (AI assistant and recommendations), reached through the
  `LlmProvider` abstraction in `component/ai/`.

---

## Backend package layout

Base package `cn.edu.nju.Iot_Verify`:

```
controller/          REST controllers (Result<T> wrapper)
service/ , service/impl/   business logic
component/
  nusmv/
    generator/       SMV model generation (device modules + main + specs)
    executor/        NusmvExecutor — subprocess exec, semaphore concurrency, timeout
    parser/          SmvTraceParser — counterexample parsing
    fixer/           FaultLocalizer + parameter/condition/disable fix strategies
  aitool/            the 30 AI tools (board/node/rule/spec/template/simulation/verification)
  ai/                LLM abstraction: domain model + LlmProvider (OpenAiLlmProvider adapter)
                     + LlmChatService / PromptCompletionService / LlmMessageCodec facades
dto/                 request/response DTOs
po/                  JPA entities
repository/          Spring Data repositories
security/            JWT + Spring Security (@CurrentUser, JwtAuthenticationFilter)
configure/           config classes, thread pools, ProductionSafetyCheck
exception/           exception hierarchy + GlobalExceptionHandler
util/                utilities
resources/
  application.yaml   main config (env-var overridable)
  deviceTemplate/    default device template JSON (seeded into DB per user)
```

Key service implementations: `AuthServiceImpl`, `BoardStorageServiceImpl`,
`VerificationServiceImpl`, `SimulationServiceImpl`, `FixServiceImpl`, `ChatServiceImpl`,
`NodeServiceImpl`, `DeviceTemplateServiceImpl`, plus `RedisTokenBlacklistService` and
the `AbstractAsyncTaskService` base for async verify/simulate tasks.

---

## Frontend layout

```
frontend/src/
  api/       http.ts (axios) + auth/board/chat/rules/simulation modules
  types/     TypeScript contracts (auth, device, node, edge, rule, spec, verify, …)
  stores/    reactive state (auth, chat)
  router/    routes + auth guard
  views/     Landing / Login / Register / Board / TemplateCreate / NotFound
  components/ CanvasBoard, ChatView, ControlCenter, SystemInspector,
              TraceVisualization, SimulationTimeline, FixResultDialog,
              RuleBuilderDialog, DeviceDialog, …
  assets/    static assets + i18n (zh-CN / en)
```

---

## Cross-cutting concerns

- **Auth & errors**: [../api/overview.md](../api/overview.md).
- **Async tasks**: verify/simulate support sync and async modes with progress and
  cancellation; task-status writes are atomic (see `CHANGELOG.md`, 2026-03-03).
- **Concurrency**: five configurable thread pools; NuSMV runs are bounded by a
  semaphore (`NUSMV_MAX_CONCURRENT`). See
  [../getting-started/configuration.md](../getting-started/configuration.md).

## Where to go next

- Verification request → result pipeline:
  [verification-flow.md](verification-flow.md)
- SMV model generation internals: [nusmv-model.md](nusmv-model.md)
- Spec formulas & P1–P5: [spec-templates.md](spec-templates.md)
- Auto-fix: [auto-fix.md](auto-fix.md)
- Endpoint index: [../api/rest-endpoints.md](../api/rest-endpoints.md)
