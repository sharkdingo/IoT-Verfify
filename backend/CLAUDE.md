# CLAUDE.md — IoT-Verify Backend

Guidance for Claude Code when working in `backend/`. Keep this file short and
rule-focused; detailed reference lives in `../docs/` (start at
[../docs/README.md](../docs/README.md)). When code and docs disagree, **code wins** —
fix the doc in the same change (see [../CONTRIBUTING.md](../CONTRIBUTING.md)).

## What this is

Spring Boot backend for a smart-home IoT formal-verification platform: users define
devices, rules, and specifications; the backend generates an SMV model, runs NuSMV,
parses counterexamples, and suggests automatic fixes. There is also an AI assistant
(any OpenAI-compatible LLM endpoint, SSE streaming) with tool/function-calling.

Stack: Java 17, Spring Boot 3.5.7, Spring Data JPA + MySQL, Redis (JWT blacklist,
fail-open), Spring Security + JWT, NuSMV 2.6–2.7 (**not** nuXmv), OpenAI Java SDK
(`com.openai:openai-java`, any OpenAI-compatible endpoint).

## Commands

```bash
mvn compile            # compile
mvn spring-boot:run    # run (needs MySQL; Redis optional; :8080, auto-creates tables)
mvn test               # unit tests
mvn clean package -DskipTests   # build jar → target/Iot-Verify-0.0.1-SNAPSHOT.jar
```

Required env vars before running: `DB_PASSWORD`, `JWT_SECRET`, `OPENAI_API_KEY`,
`NUSMV_PATH`. Full list and defaults: [../docs/getting-started/configuration.md](../docs/getting-started/configuration.md).

## Codebase map

Base package `cn.edu.nju.Iot_Verify` (entry point `IotVerifyApplication`):

```
controller/        REST controllers — return Result<T> (SSE endpoints return SseEmitter)
service/impl/      business logic
component/
  nusmv/
    generator/     SMV model generation: SmvGenerator + Device/Main/Specification builders + SmvModelValidator
    executor/      NusmvExecutor — subprocess exec, semaphore concurrency, timeout
    parser/        SmvTraceParser — counterexample parsing
    fixer/         FaultLocalizer + parameter/condition/disable fix strategies
  aitool/          30 AI tools (board/node/rule/spec/template/simulation/verification)
  ai/              LLM abstraction — domain model + LlmProvider (OpenAiLlmProvider) + facades
dto/ po/ repository/   DTOs, JPA entities, data access
security/          JWT + Spring Security
configure/         config, thread pools, ProductionSafetyCheck
exception/         exception hierarchy + GlobalExceptionHandler
util/              mappers, JsonUtils, JwtUtil
resources/
  application.yaml     config (env-var overridable)
  deviceTemplate/      default device-template JSON (seeded into DB per user)
```

Deeper architecture: [../docs/architecture/overview.md](../docs/architecture/overview.md).

## Conventions (hard rules)

- Controllers return `Result<T>`; use `Result.success()` for void. SSE endpoints return
  `SseEmitter` directly (not wrapped). The `@CurrentUser` param is always `Long userId`.
- **Never expose PO entities** — always map to DTOs.
- Read methods are `@Transactional(readOnly = true)`.
- Exceptions map via `GlobalExceptionHandler` (masks internal messages). Throw the
  typed exception, don't hand-build error responses. See
  [../docs/api/overview.md](../docs/api/overview.md) for the full status mapping.
- Keep docs in sync in the same change: touching a controller/DTO/config/spec-template/
  AI-tool means updating the owning doc under `docs/` (see CONTRIBUTING.md).

## Gotchas (the "why", not the "what")

- **`saveRules` is incremental, not full-replace** (unlike nodes/edges/specs). It
  upserts by `id` and preserves `createdAt`, because fault localization keys off stable
  rule identity — a delete-and-recreate would churn ids and break fixes. Send existing
  `id`s back. See [../docs/api/board.md](../docs/api/board.md).
- **NuSMV identifiers**: mode/state names are sanitized at generation time
  (`sanitizeSmvToken`), but InternalVariable/ImpactedVariable names are validated (and
  rejected) at persist time — they are cross-referenced by `.equals()`, so sanitizing
  them would break matching. Don't "fix" this by sanitizing them later. See
  [../docs/architecture/nusmv-model.md](../docs/architecture/nusmv-model.md).
- **Async task state** uses atomic conditional UPDATEs (`WHERE status <> CANCELLED`) to
  avoid TOCTOU races — don't replace with read-then-write.
- **NuSMV generation must fail closed and be observable.** Invalid/empty rule
  conditions must not become `TRUE`; route them through the request-scoped
  `SmvGenerationContext` so `checkLogs`, `disabledRuleCount`, and `skippedSpecCount`
  stay accurate without global mutable state.
- **AI rule/spec tools are label-first.** Recommendation prompts and parsed output should
  use board device labels as the public reference; node ids are only a legacy fallback.
  Specification recommendation `templateId` values must stay constrained to `"1"` through
  `"7"`.
- **Redis is fail-open**: logout revocation degrades silently if Redis is down; do not
  make request flow hard-depend on it.
- **Temp files are kept on purpose**: `cleanupTempFile()` is a no-op so `nusmv_*` dirs
  (`model.smv`, `request.json`, `output.txt`, `result.json`) survive for debugging.
- **`ProductionSafetyCheck`** refuses to start under a `prod`/`production` profile if
  `JWT_SECRET` / `DB_PASSWORD` / `OPENAI_API_KEY` hold unsafe defaults.
- Attack-mode transitions take priority over template transitions in `next()` — an
  attacked device can jump to any mode regardless of rules.

## Reference (don't duplicate here — link)

- Endpoint index: [../docs/api/rest-endpoints.md](../docs/api/rest-endpoints.md)
- API contracts: [auth](../docs/api/auth.md) · [board](../docs/api/board.md) ·
  [verification/simulation/fix](../docs/api/verification.md) ·
  [chat SSE](../docs/api/chat-sse.md) · [AI tools](../docs/api/ai-tools.md)
- Verification pipeline & trace format: [../docs/architecture/verification-flow.md](../docs/architecture/verification-flow.md)
- Spec templates & P1–P5 validation: [../docs/architecture/spec-templates.md](../docs/architecture/spec-templates.md)
- Auto-fix (Salus §4–§5): [../docs/architecture/auto-fix.md](../docs/architecture/auto-fix.md)
- Change history: [../CHANGELOG.md](../CHANGELOG.md)

## Data model

14 tables, auto-created by Hibernate (`ddl-auto: update`): `user`, `device_node`,
`device_edge`, `rules`, `specification`, `board_layout`, `board_active`,
`device_templates`, `verification_task`, `simulation_task`, `trace`,
`simulation_trace`, `chat_session`, `chat_message`. Notable: `device_node` has a
composite PK `(id, user_id)` for user isolation; `device_templates` has a unique
constraint on `(user_id, name)`; `specification` carries `formula` (TEXT) and
`devices_json` (JSON) for authored-formula/device-binding persistence; `verification_task`
carries `disabled_rule_count` / `skipped_spec_count` mirroring the generation-warning
counts surfaced in `VerificationResultDto`.
