# CLAUDE.md — IoT-Verify Backend

Guidance for Claude Code when working in `backend/`. Keep this file short and
rule-focused; detailed reference lives in `../docs/` (start at
[../docs/README.md](../docs/README.md)). When code and docs disagree, **code wins** —
fix the doc in the same change (see [../CONTRIBUTING.md](../CONTRIBUTING.md)).

## What this is

Spring Boot backend for a smart-home IoT verification platform: users define devices,
rules, and specifications; the backend performs bounded candidate-path exploration,
generates an SMV model, runs NuSMV, parses formal counterexamples, and suggests
automatic fixes. There is also an AI assistant
(any OpenAI-compatible LLM endpoint, SSE streaming) with tool/function-calling.

Stack: Java 17, Spring Boot 3.5.7, Spring Data JPA + MySQL, Redis (JWT blacklist,
fail-open), Spring Security + JWT, NuSMV 2.6–2.7 (**not** nuXmv), OpenAI Java SDK
(`com.openai:openai-java`, any OpenAI-compatible endpoint).

This project is in active development and has no released compatibility contract.
Unless the user explicitly requests a migration path, reject obsolete persisted shapes
and remove superseded APIs instead of adding fallback readers, deprecated aliases,
dual-write formats, or silent coercion for old development data.

## Commands

```bash
mvn compile            # compile
mvn spring-boot:run    # run (needs MySQL; Redis optional; :8080, auto-creates tables)
mvn test               # unit tests
mvn clean package -DskipTests   # build jar → target/Iot-Verify-0.0.1-SNAPSHOT.jar
```

Required env vars before running: `DB_PASSWORD`, `JWT_SECRET`, `IOT_VERIFY_OPENAI_API_KEY`,
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
  fuzz/            deterministic bounded path search + finite safety monitor
  aitool/          35 AI tools (board/node/rule/scenario/spec/template/simulation/verification)
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

### Backend anti-slop checks

- Do not catch broad exceptions to manufacture an empty, successful, or retryable result.
  Preserve the typed failure, transaction outcome, and whether a mutation may have committed.
- For concurrent or asynchronous work, state the owner, clock, lease/version precondition,
  idempotency rule, and terminal transition explicitly. A JVM lock is not a cross-instance
  guarantee, and request acceptance is not completion.
- Validate DTOs and provider/tool output at the boundary, then keep one canonical internal
  representation. Do not add repair-by-guessing paths that silently coerce malformed data or
  let model prose overrule authoritative state.
- A new service, mapper, projection, or helper must remove concrete duplication or enforce a
  named invariant. Pass-through layers, one-call wrappers, and parallel snapshots require a
  demonstrated reason and focused tests.
- Backend tests must cover rejection, ownership loss, stale writes, cancellation, and partial
  persistence where relevant; a happy-path Mockito interaction alone is not evidence of the
  database or distributed contract.

## Gotchas (the "why", not the "what")

- **Ordinary board mutations are targeted and serialized per user.** Do not expose the
  internal collection rewrite helpers as full-list REST contracts. `/api/board/batch`
  is reserved for explicit scene replacement/clear and commits supplied semantic
  collections plus template dependencies atomically. See
  [../docs/api/board.md](../docs/api/board.md).
- **NuSMV identifiers**: mode/state names are sanitized at generation time
  (`sanitizeSmvToken`), but InternalVariable/ImpactedVariable names are validated (and
  rejected) at persist time — they are cross-referenced by `.equals()`, so sanitizing
  them would break matching. Don't "fix" this by sanitizing them later. See
  [../docs/architecture/nusmv-model.md](../docs/architecture/nusmv-model.md).
- **Environment domains are active-template and same-manifest scoped.** An
  `ImpactedVariables` name is defined by an external `InternalVariable` or
  `EnvironmentDomains` entry in that same manifest. Never scan the user's whole template
  library to fill a missing domain: unused templates must not alter the current board.
- **Async task state** uses atomic status predicates to avoid TOCTOU races. Verification,
  simulation, and fuzz queue/running work also use renewable per-instance database leases;
  start, progress, renewal, worker success, and worker failure require the owning worker
  and an unexpired lease measured by the microsecond database clock. Renewal must lock the
  task row before sampling that clock; a JVM/pre-lock timestamp or statement-start
  `CURRENT_TIMESTAMP` can expire while waiting and must not confirm the local heartbeat.
  Completion/failure transactions lock the task row before sampling their terminal time
  and persisting linked evidence. Cancellation remains user-authoritative. Do not replace
  these transitions with read-then-write, a pre-lock JVM timestamp, or global startup cleanup.
- **Fuzz findings are not formal traces.** The bounded explorer supports only its
  documented finite safety subset, and budget exhaustion is never satisfaction. Keep
  `fuzz_finding` separate from NuSMV `trace`; direct automatic fix remains formal-only.
- **NuSMV generation must fail closed and be observable.** Invalid/empty rule
  conditions must not become `TRUE`; route them through the request-scoped
  `SmvGenerationContext` so `checkLogs`, `disabledRuleCount`, and `skippedSpecCount`
  stay accurate without global mutable state.
- **AI rule/spec tools are node-id authoritative.** Recommendation prompts and parsed
  output must use canonical board device node ids (`deviceId` / `deviceName` DTO fields)
  for identity. Display labels are readability snapshots only. Specification
  recommendation `templateId` values must stay constrained to `"1"` through `"7"`.
- **Redis is fail-open**: logout revocation degrades silently if Redis is down; do not
  make request flow hard-depend on it. A distributed operation lease that is explicitly
  lost or remains unconfirmed for its full TTL must stop its old worker; do not reduce a
  lease heartbeat failure to logging only.
- **NuSMV debug files use bounded retention**: `cleanupTempFile()` leaves a completed
  `nusmv_*` directory available for diagnosis, while the scheduled artifact cleaner caps
  both its age and the total retained directory count. Executors must hold the shared
  artifact-registry lock before the model existence check and from capacity wait through
  output completion. Process output must be drained in bounded byte chunks rather than
  `readLine()`, because NuSMV can emit an unterminated line. Cleanup must hold the same exclusion from inactivity check through
  recursive deletion so active directories are never removed. Do not remove the output
  drain or bypass the limits documented in the
  configuration reference.
- **`ProductionSafetyCheck`** refuses to start under a `prod`/`production` profile if
  `JWT_SECRET` / `DB_PASSWORD` / `IOT_VERIFY_OPENAI_API_KEY` hold unsafe defaults.
- **Attack behavior is capability-scoped.** Compromise may falsify only variables whose
  manifest explicitly sets `FalsifiableWhenCompromised=true`; compromised targets or
  logical automation links drop matching commands. It does not add an arbitrary actuator
  state-transition branch. Attack selection is per-run: simulation requires explicit
  points, while verification may use explicit points or exhaust all combinations up to a
  budget. Persistent trust labels do not select attack points. See
  [../docs/architecture/nusmv-model.md](../docs/architecture/nusmv-model.md).

## Reference (don't duplicate here — link)

- Endpoint index: [../docs/api/rest-endpoints.md](../docs/api/rest-endpoints.md)
- API contracts: [auth](../docs/api/auth.md) · [board](../docs/api/board.md) ·
  [verification/simulation/fix](../docs/api/verification.md) ·
  [counterexample exploration](../docs/api/fuzzing.md) ·
  [chat SSE](../docs/api/chat-sse.md) · [AI tools](../docs/api/ai-tools.md)
- Data authority & identity: [data authority](../docs/architecture/data-authority-model.md) ·
  [device identity](../docs/architecture/device-identity.md)
- Verification pipeline & trace format: [../docs/architecture/verification-flow.md](../docs/architecture/verification-flow.md)
- Bounded exploration: [../docs/architecture/fuzzing-flow.md](../docs/architecture/fuzzing-flow.md)
- Spec templates & P1–P5 validation: [../docs/architecture/spec-templates.md](../docs/architecture/spec-templates.md)
- Auto-fix (Salus §4–§5): [../docs/architecture/auto-fix.md](../docs/architecture/auto-fix.md)
- Change history: [../CHANGELOG.md](../CHANGELOG.md)

## Data model

16 tables, auto-created by Hibernate (`ddl-auto: update`): `app_user`, `device_node`,
`board_environment_variable`, `rules`, `specification`, `board_layout`,
`device_templates`, `verification_task`, `simulation_task`, `fuzz_task`, `trace`,
`simulation_trace`, `fuzz_finding`, `chat_session`, `chat_message`, `ai_session_state`. Notable: `device_node` has a
composite PK `(id, user_id)` for user isolation; `board_environment_variable` has a
composite PK `(name, user_id)` for per-user shared environment state;
`device_templates` has a unique constraint on `(user_id, name)`; `specification` has a
composite PK `(id, user_id)` and carries `formula` (TEXT) and `devices_json` (JSON) for
authored-formula/device-binding persistence; `verification_task` carries
`disabled_rule_count` / `skipped_spec_count`
mirroring the generation-warning counts surfaced in `VerificationResultDto`. Completed
rows also back verification run history for both synchronous and asynchronous checks;
`verification_task`, `simulation_task`, and `fuzz_task` carry internal `worker_id` and
`lease_expires_at` ownership for queued/running work; worker terminal transitions require
that live ownership and clear it, user cancellation clears it independently, and maintenance
recovers only expired active rows. Their lifecycle transitions use the database clock;
`chat_message` stores a per-turn correlation id plus the exact user-visible assistant execution
trace, elapsed time, and terminal status on the final assistant row; absent or malformed trace
evidence is not reconstructed from internal tool blocks. `ai_session_state` durably stores expiring task continuation, scenario draft,
and protected-action confirmation state shared by backend instances;
`chat_session` stores the expiring cross-instance execution lease and stop flags so only one
assistant request can mutate a session at a time;
the task-list endpoint excludes them and `/api/verify/runs` exposes result-oriented DTOs.
Completed `fuzz_task` rows likewise back `/api/fuzz/runs`; their independent
`fuzz_finding` rows are heuristic candidate evidence, not formal traces.
