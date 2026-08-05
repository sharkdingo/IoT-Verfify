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

**Deleting or changing an overloaded method needs `mvn clean`, not `mvn test`.** Maven's incremental
compile recompiles the changed file against the *previous* `target/classes`, so overload resolution can
bind to a signature that no longer exists in the sources. Removing two unused list wrappers from
`FuzzMapper` — the only remaining `this::toFindingSummaryDto` / `this::toFindingDto` method references —
made javac resolve a two-arg call to the stale `FuzzFindingPo` overload instead of the
`FuzzFindingSummaryProjection` one, producing 3 compile errors that cascaded into ~100 test errors, a
`NoClassDefFoundError` sweep, and a bogus "Mockito cannot mock" failure. `mvn clean test-compile` on the
identical sources succeeds. The failure looks exactly like a real overload bug, so the instinct is to
"fix" the overloads and break working code — run `mvn clean` first and re-read the error.

**Anything else writing to `target/classes` corrupts a Maven run, and the failure looks like a code bug.**
Two symptoms, both seen here: a `BUILD FAILURE` whose error list is empty (the tell is *no*
`[ERROR] …java:[line]` entries), and mass `NoClassDefFoundError` / `MockitoException: Could not modify all
classes` / `NoSuchFileException: target\classes\….class` on files javac just wrote.

Two distinct culprits, and the second is the one that bites unattended:
- **A second Maven build** in the same checkout — don't start one while a delegated subagent is running the
  suite, or the result describes neither tree.
- **The VS Code `redhat.java` language server.** Its JDT project for this repo declares
  `kind="output" path="target/classes"` (check the `.classpath` under
  `~/AppData/Roaming/Code/User/workspaceStorage/*/redhat.java/jdt_ws/.metadata/.plugins/org.eclipse.core.resources/.projects/Iot-Verify/`),
  so it auto-builds into the same directory and rewrites class files mid-compile. It is a ~1.3 GB `java.exe`
  that looks like any other JVM in the process list. This is not hypothetical: it produced
  `746 tests, 22 failures, 624 errors` on one attempt and a 21-error `testCompile` failure on the next, on a
  tree whose real result was 2216/2216 green.

So: re-run an unexplained compile or mass-error failure once before believing it, and if it persists, build
in an isolated copy. A backend-only copy is **not** sufficient — several tests read repo-relative paths and
need `../docs/`, the root `README.md`, `CLAUDE.md`, and `backend/device-template-schema.json`; omitting the
schema alone fabricates ~90 failures.

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
    fixer/         FaultLocalizer + parameter/condition/permanent-removal fix strategies
  fuzz/            deterministic bounded path search + finite safety monitor
  aitool/          53 AI tools (board/node/rule/scenario/spec/template/simulation/verification/fuzz)
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
- **Admission and generation must normalize the same string the same way.** Every rule/spec field
  that names something in a device manifest — command `action`, condition `attribute`, `targetType`,
  device refs — is resolved by `equals()` at generation time, so any trim/case difference between the
  validator and the generator is a silent divergence, not a cosmetic one. This has bitten four times:
  the command action passed validation trimmed and then resolved to no API, which dropped the rule
  from state, property, *and* probe assignments while `disabledRuleCount` stayed 0 — a `SATISFIED` +
  `modelComplete=true` verdict for a scene whose automation was never modeled. Normalize once per
  side (trim at the storage boundary, trim at the top of the resolver), pin `Locale.ROOT` on any
  `toLowerCase`, and when a lookup can still fail, record a disabled rule rather than `continue`.
- **Environment domains are active-template and same-manifest scoped.** An
  `ImpactedVariables` name is defined by an external `InternalVariable` or
  shared `InternalVariables` entry in that same manifest. Never scan the user's whole template
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
  **A worker's own registration must be crash-safe.** `registerRunningTask` /
  `updateTaskProgress` belong inside the `try` whose `finally` removes them, and
  `handleCancellation` must not propagate: it runs ahead of that cleanup and touches the database.
  A leaked `runningTasks` entry means a pooled thread stays registered against a finished task, so
  a later cancel interrupts whatever unrelated task that thread moved on to. The database row
  stays authoritative either way: the user's own cancel settles it, or the expired-lease sweep does —
  and that sweep writes FAILED, not CANCELLED, so the residual case shows a cancelled run as failed.
- **Semantic identity counts conditions; duplicate detection does not.** `exactlyMatches` on both
  `RuleSemanticSignature` and `SpecificationSemanticSignature` compares condition *multisets*:
  order carries no meaning in a conjunction, but cardinality does, and these predicates also gate
  "delete only if unchanged" and undo/redo conflict checks. Collapsing conditions into a set let a
  delete land on a record the user never reviewed. `RuleSemanticSignature.Signature` keeps set
  semantics on purpose — `CheckDuplicateRuleTool` reasons about subset and overlap between
  different rules, where dropping duplicates is correct. Derive both views from one canonical key
  list so a normalization change cannot reach only one of them.
- **A cancelled search must stop launching solver runs.** Cancellation reaches a fix/fuzz worker as
  a thread interrupt, so every search loop exits on `FixContext.isExpired()`, which reports both an
  expired deadline **and** an interrupt. A broad `catch (Exception)` in a strategy will swallow the
  `InterruptedException` that `Semaphore.tryAcquire` throws — and clear the flag with it — so such a
  catch must call `FixStrategyUtils.preserveInterrupt(e)`. Otherwise the search keeps running its
  remaining attempts, each holding a NuSMV permit, for a request whose response was already sent.
- **Validation must match what the generated model actually permits — no stricter.** The
  recommendation reachability filter may narrow a variable's domain only for `IsInside=true` locals,
  which the model holds constant (`TRUE: <device>.<var>`) when nothing writes them. Shared
  environment variables get a `TRUE: {<all declared values>}` branch, so their pool value is only
  `init` and every declared value is reachable immediately; narrowing them rejected legitimate
  requests like "alarm when smoke is detected" as provably dead. Before adding a check that calls a
  candidate impossible, confirm the model agrees. Likewise, a constraint's justification must cover
  what it actually rejects: the template-name rule guards Java/MySQL case-folding parity, so it
  restricts *cased* letters, not every non-ASCII character (see `TemplateNameRule`).
- **A tool's schema description is part of its contract.** `requireOnlyFields` rejects unknown keys,
  so a description promising a field is "ignored" for some action makes the model waste a round on a
  guaranteed `VALIDATION_ERROR`. Keep the wording and the allowlist in step.
- **Fuzz findings are not formal traces.** The bounded explorer supports only its
  documented finite safety subset, and budget exhaustion is never satisfaction. Keep
  `fuzz_finding` separate from NuSMV `trace`; direct automatic fix remains formal-only.
- **Use papers as evidence, not as an implicit product override.** The modeling, fix, and exploration
  semantics draw from published algorithms ([../docs/architecture/theory-sources.md](../docs/architecture/theory-sources.md)),
  but deliberate abstractions must follow the documented product contract. Numeric environment
  evolution, for example, exposes MEDIC's per-step `[-1, 1]` disturbance as the required
  `NaturalChangeRate`: `[-1, 1]` is the exact MEDIC rule, `0` explicitly disables independent drift,
  and another interval is a visible project extension. Generation uses that declaration once and
  never layers a second hidden `[-1, 1]` term on top. Read the cited section, name any deviation, and
  keep formal verification, fuzz, DTOs, tests, docs, and UI wording aligned.
- **An interrupt flag is thread state, not request state.** `FixStrategyUtils.preserveInterrupt`
  re-arms `Thread.interrupt()` so a cancelled search stops launching solver runs, and
  `FixContext.isExpired()` reports it. Re-arm freely inside a task — it is the search's only stop
  signal, and `RuleFixer.fix` must never clear it mid-search — because
  `ThreadPoolExecutor.runWorker` clears a worker's interrupt status before each task, so a re-armed
  flag cannot reach the next request on that thread (pinned by `ThreadConfigTest`). What it *can*
  reach is the rest of the current task: `ChatServiceImpl.synchronizeExecutionStop` reads
  `isInterrupted()` and ends the turn as `DISCONNECTED`, so re-arming inside a chat tool aborts that
  turn by design.
- **NuSMV generation must fail closed and be observable.** Invalid/empty rule
  conditions must not become `TRUE`; route them through the request-scoped
  `SmvGenerationContext` so `checkLogs`, `disabledRuleCount`, and `skippedSpecCount`
  stay accurate without global mutable state.
- **Reasoning is a different channel from a tool status line, and must be presented as one.**
  `compactReasoningProgressDetail` deliberately diverges from `compactToolProgressDetail`: it keeps
  line breaks (collapsing them turned a decomposition into one run-on line), cuts on a sentence or
  line boundary, and gets a much larger budget. Its identifier redaction requires a digit in the
  tail — without that it rewrote ordinary English ("rule-based", "device-level") as
  `[internal reference]`, corrupting the very explanation it protected. The planning prompt asks the
  model to *do* the reasoning — decompose, cite observed board state, name a rejected alternative on
  a judgement call, verify its own outcome — not to narrate the calls it is about to make. A round
  that returns no reasoning is reported as returning none; never substitute wording that implies
  reasoning happened.
- **AI rule/spec tools are node-id authoritative.** Recommendation prompts and parsed
  output must use canonical board device node ids (`deviceId` / `deviceName` DTO fields)
  for identity. Display labels are readability snapshots only. Specification
  recommendation `templateId` values must stay constrained to `"1"` through `"7"`.
- **The board edit journal commits with the edit it describes.** `BoardEditJournal.record` must be
  called inside the mutation's own transaction and per-user write lock, or a crash between the two
  leaves an undo that does not match reality. Undo/redo apply the inverse through the same
  validated write path, refuse when the affected record changed after the entry was written (never
  overwrite newer work), discard the abandoned redo branch on a new edit, and treat "nothing to
  apply" as a normal idempotent outcome. Restoring a deleted rule keeps its original id via a
  native insert, because the id is IDENTITY-generated and references depend on it.
  Every entry is validated as an operation-specific, non-no-op transition before any inverse write:
  snapshot identity, payload presence, collection position, and reorder membership must agree with
  its metadata, or the entry returns `409` without being consumed. Collection positions are exact:
  an index that cannot be inserted into the current ordered collection is rejected, never clamped or
  appended into a different rule/specification order.
  Reversibility follows the user's unit of work, not the storage shape: rule reorder changes no
  single record, but one up/down press is one edit, so it records a `RULE_ORDER` entry holding the
  previous ordering (`RuleOrderSnapshot`) and refuses when the current order or rule set no longer
  matches what that edit produced. Device layout/runtime/rename, direct Environment Pool updates,
  and automatic-fix rule-set replacement are likewise one entry per user action; semantic no-ops
  write no history. Reversible mutations return authoritative availability so the client mirrors
  server state instead of guessing. Confirmed scene replacement/clear, template deletion, and
  bundled-template reset are history boundaries because they can remove or replace manifest
  semantics that device snapshots depend on. Their previews report the affected history count and
  bind the impact token to the exact journal; success clears it in the same transaction. Explicit
  history clear uses an impact token over
  the complete journal, so a confirmation cannot delete entries changed by another tab meanwhile.
- **Redis is fail-open**: logout revocation degrades silently if Redis is down; do not
  make request flow hard-depend on it. Interactive recommendation/fix acquisition may use
  process-local tracking only when Redis is known unavailable before any ownership write is
  attempted. An uncertain or late distributed acquisition fails closed and performs
  token-fenced cleanup. A distributed operation lease that is explicitly lost or remains
  unconfirmed for its full TTL must stop its old worker; do not reduce a lease heartbeat
  failure to logging only. Interactive recommendation/fix success must pass the atomic
  ownership-and-stop completion fence before its result is delivered; best-effort cleanup is
  not a successful settlement.
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
- Which paper owns which semantics: [../docs/architecture/theory-sources.md](../docs/architecture/theory-sources.md)
- Change history: [../CHANGELOG.md](../CHANGELOG.md)

## Data model

18 tables, auto-created by Hibernate (`ddl-auto: update`): `app_user`, `device_node`,
`board_environment_variable`, `rules`, `specification`, `board_layout`, `board_edit_journal`,
`device_templates`, `verification_task`, `simulation_task`, `fuzz_task`, `trace`,
`simulation_trace`, `fuzz_finding`, `chat_session`, `chat_session_pre_admission_stop`,
`chat_message`, `ai_session_state`. Notable: `device_node` has a
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
assistant request can mutate a session at a time; `chat_session_pre_admission_stop` stores a
database-clock timestamp for each turn-specific Stop fence, keeps at most 64 live fences, and
expires each one after two minutes before admission; the collection cascades when its owning
session is deleted;
the task-list endpoint excludes them and `/api/verify/runs` exposes result-oriented DTOs.
`board_edit_journal` is a per-user append-only record of reversible Board edits: device
create/update/rename/delete, direct Environment Pool update, rule/specification create/delete, rule
reorder, and automatic-fix ordered rule-set replacement. Device entries hold the affected devices,
cascaded rules/specifications and positions, and exact Environment Pool state; rule/specification
create/delete uses `entity_order` so restore lands at its original position. Entries are written in
the mutating transaction, moved rather than deleted by undo/redo, and cleared wholesale by confirmed
scene replacement/clear or the explicit history-clear command.

Completed `fuzz_task` rows likewise back `/api/fuzz/runs`; their independent
`fuzz_finding` rows are heuristic candidate evidence, not formal traces.
