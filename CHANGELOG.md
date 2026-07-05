# Changelog

All notable changes to IoT-Verify are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/). **Until a formal release/tagging
process exists, changes are recorded under `Unreleased` with dated entries.** When the
first tagged release is cut, the relevant entries will be moved under a version heading
(e.g. `[1.0.0] - 2026-xx-xx`).

These entries were migrated from the "同步更新 (implementation-alignment)" sections
(§13, §14) of the former `backend/NuSMV_Module_Documentation.md`, which mixed change
history into a technical spec. The spec content itself now lives under
`docs/architecture/`.

---

## [Unreleased]

### 2026-07-05

#### Fixed
- **Fix-apply now blocks spec/device-only drift.** Applying a verified fix previously replayed the
  trace's stored context on the server, so editing spec conditions or device instance state
  (variables, privacies, initial state, trust) after verifying — without touching rules or templates —
  was not detected and a stale fix could be persisted onto the current rules. apply now compares a
  canonical **semantic fingerprint** of the trace snapshot against the current board (device names
  canonicalized, empty variable/privacy lists manifest-defaulted, values de-quoted, so an untouched
  board still matches), and rejects with `400` on drift. The check runs **inside the same per-user
  write lock + transaction** as the rule save (read → check → write is one atomic critical section), so
  a concurrent spec/device/node edit cannot slip in between the check and the write. When the current
  board fails to build a device model it fails closed, distinguishing cause: an invalid/changed board
  rejects with `400`, while an unconfirmable infrastructure error (e.g. template repository unavailable)
  rejects with `503` ("retry later") instead of misattributing it to a board change.
- **Device reference resolution unified across spec generation, drift fingerprint, and fix candidates.**
  A single `DeviceReferenceResolver` now owns the `deviceId → deviceLabel → normalized-label` fallback
  order, so the NuSMV generator, semantic fingerprint, and fix-candidate builder no longer each guess
  device names independently (they previously disagreed for AI/historical specs carrying a node-id
  `deviceId` plus a label). condition-fix `add` now maps verification-time names (`d_1Lamp`) back to the
  current board's persisted label (`1Lamp`) before saving, so the frontend can resolve the node.
- **Template-drift check fails closed on apply.** A template-repository error during apply no longer
  proceeds to recompute and persist; it is treated as unverifiable drift and rejected. `/fix` still
  fails open (a repo error only drops the advisory warning).
- **Digit-leading device labels no longer misfire the rule-drift check.** The frontend prefixes such
  labels (`1Lamp` → `d_1Lamp`) in the verification snapshot while rules persist the raw label; the
  apply-time rule fingerprint now canonicalizes both sides, so an untouched board is no longer rejected.
- **Historical trace playback respects the same guards as current-result playback.** Viewing a saved
  verification trace now checks the simulation-timeline / recommendations mutex, takes the animation
  lock, and closes the result dialog; the `View` button is disabled while those panels are open.
- **Trace attack/intensity labels reflect the viewed trace.** `TraceDto` now derives and exposes
  `isAttack` / `intensity` / `enablePrivacy` from its stored request snapshot, and the trace control bar
  reads them instead of the live verification form, so a historical trace is labelled with the
  parameters it was actually run under.
- **Successful-simulation logs are reachable.** A successful simulation opens the timeline directly; its
  execution logs and raw NuSMV output are now retained and openable on demand via a "View logs" action
  (previously the result dialog holding them was only reachable on error).
- **AI board overview now reports the same rule connections as the canvas.** `board_overview` derives
  edge summaries from rule conditions and commands instead of the optional persisted `/board/edges`
  geometry table, matching the frontend's rule-derived canvas connections.
- **Async verification and simulation can be cancelled from the Board UI.** The existing cancel REST
  endpoints are now reachable from the async progress panels, and user-requested cancellation is shown
  as an informational outcome rather than a generic failure.
- **`fix_violation` is discoverable by the AI planner.** The tool was registered and documented, but the
  system prompt and explicit tool-name router omitted it; both now list the tool.

### 2026-07-04

#### Changed
- **Decoupled the LLM backend from Volcengine Ark; the AI assistant now targets any
  OpenAI-compatible endpoint.** Introduced a vendor-neutral LLM layer under
  `component/ai/`: a domain model (`LlmMessage`, `LlmToolCall`, `LlmToolSpec`,
  `LlmChatRequest`/`LlmChatResponse`), a `LlmProvider` strategy interface, and an
  `OpenAiLlmProvider` adapter that is the sole holder of an LLM SDK import. Facades
  `LlmChatService` (tool loop + streaming), `PromptCompletionService` (one-shot
  recommend/duplicate-check completions), and `LlmMessageCodec` (persistence wire-format
  ⇄ domain conversion) sit between the business layer and the provider. `ChatServiceImpl`
  and all AI tools now depend only on the domain model — no SDK type leaks into business
  code. Tool declarations return `LlmToolSpec` instead of the SDK's `ChatTool`.

#### Fixed
- **NuSMV generation warnings are now part of the verification contract.** Rule
  conditions that cannot be generated fail closed to `FALSE`, skipped/invalid specs are
  recorded, and `VerificationResultDto` returns `checkLogs`,
  `disabledRuleCount`, and `skippedSpecCount` so a "safe" result cannot hide that part of
  the requested model was excluded. Warning collection is passed through a request-scoped
  `SmvGenerationContext` instead of global mutable state, and completed async verification
  tasks now persist/return the same two count fields.
- **Rule creation no longer fabricates dummy triggers.** Frontend save, duplicate-check,
  direct verify, and simulation paths validate that every rule has at least one concrete
  trigger condition; the backend also requires non-empty `RuleDto.conditions`.
- **Specification persistence now keeps the authored formula and device bindings.**
  `SpecificationDto`/`SpecificationPo`/`SpecificationMapper` preserve `formula` and
  `devices` metadata across board saves.
- **Board edge storage is geometry-only again.** Frontend API mapping no longer expects
  phantom edge fields such as `fromApi`, `toApi`, `itemType`, `relation`, or `value`.

#### AI Tools
- **AI rule/spec recommendations now use device labels as their primary references.**
  `recommend_rules` emits `deviceName` values that match board labels, and
  `recommend_specifications` requires `templateId` to be one of `"1"` through `"7"`;
  recommendations with illegal template ids or unresolvable devices are filtered out.
  Tool validators, prompt schemas, and backend DTO validation now also converge on
  supported relation operators and non-empty condition values.

#### Configuration (breaking)
- **Config keys renamed `volcengine.ark.*` → `llm.*`.** Env vars: `VOLCENGINE_API_KEY` →
  `OPENAI_API_KEY`, `VOLCENGINE_MODEL_ID` → `OPENAI_MODEL`, `VOLCENGINE_BASE_URL` →
  `OPENAI_BASE_URL`, `ARK_TIMEOUT_MINUTES` → `LLM_TIMEOUT_MINUTES`; new `LLM_PROVIDER`
  (default `openai`). Point `OPENAI_BASE_URL` at the official API or a relay ("中转站").
  `ProductionSafetyCheck` now guards `llm.api-key` (`OPENAI_API_KEY`).

#### Dependencies
- Replaced `com.volcengine:volcengine-java-sdk-ark-runtime` with
  `com.openai:openai-java` (4.41.0). Removed `ArkAiClient` and `ArkAiConfig`.

### 2026-07-03

#### Security
- **Fixed a `UserContextHolder` ThreadLocal cross-request leak in `JwtAuthenticationFilter`.**
  The filter set the per-request `UserContextHolder` (a `ThreadLocal` read by the AI-tool
  path via `AbstractAiTool`) but never cleared it. On a reused Tomcat worker thread, a
  later request arriving without a valid token would neither set nor clear it and would
  observe the previous request's `userId` — a potential cross-user access on the AI-tool
  path. The filter now clears `UserContextHolder` in a `finally` around
  `filterChain.doFilter` (covering the blacklisted-token early path too). The REST path
  was unaffected — `@CurrentUser` reads `SecurityContextHolder`, which Spring clears per
  request.

#### Changed

- **Integrated duplicate-rule checking in rule creation dialog.**
  The `POST /api/board/rules/check-duplicate` endpoint (backend implementation existed
  but was frontend-unintegrated) is now callable via `boardApi.checkDuplicateRule(rule)`.
  `RuleBuilderDialog.vue` adds a "Check Duplicate" button (non-blocking: if AI detects
  duplication, a confirmation dialog offers "Save Anyway" or "Cancel"). This avoids
  forcing users through an AI check that has latency, cost, and potential false positives
  while surfacing the duplicate-detection capability where useful.
- **Frontend API base URL is now relative by default and configurable end-to-end.**
  Both `src/api/http.ts` (axios, `(VITE_API_BASE_URL || '') + '/api'`) and
  `src/api/chat.ts` (SSE) derive their base URL from `import.meta.env.VITE_API_BASE_URL`.
  When it is empty (the default) requests go to a relative `/api`, which the Vite dev
  server and a production reverse proxy (Nginx) forward to the backend — so dev and
  same-origin prod need no config. Previously axios hardcoded `http://localhost:8080/api`,
  which bypassed the Vite dev proxy and, in prod without an override, pointed the
  browser at the user's own machine. Set an absolute `VITE_API_BASE_URL` only for
  cross-origin deployments (resolves former frontend fix item F-11).

#### Fixed
- **Custom-template API editor now emits a backend-valid manifest.** The template
  creator (`CustomTemplateCreator.vue`) previously produced API definitions that the
  NuSMV pre-check rejected:
  - `Trigger` was built from a single pseudo-value (`user`/`auto`/`event`) as
    `{ Attribute: <pseudo>, Relation: 'EQ', Value: '' }` — Attribute wasn't a legal
    mode/internal-variable and `Value` was blank, both failing P1
    (`validateTriggerCompleteness` / `illegalTriggerAttribute`). It is now edited as
    three fields `{ Attribute, Relation, Value }` — Attribute a dropdown of legal
    modes + internal variables, Relation ∈ `= != > >= < <=`, all required when set
    (or omitted entirely for no trigger).
  - API `Assignments` used the wrong field names `{ VariableName, ChangeRate }`; the
    backend DTO is `{ Attribute, Value }`, so assignment data was dropped and validation
    failed. Now emitted as `{ Attribute, Value }`.
- **Spec trust/privacy conditions restrict the relation operator.** For `targetType`
  `trust`/`privacy` (enum-valued), the operator dropdown now offers only `= != in not_in`
  (was also offering `> >= < <=`, which generate meaningless ordering comparisons on
  enum domains).
- **Async verification/simulation polling reworked for correct lifecycle & error
  handling** (`Board.vue`):
  - Verification async polling is now an awaited `pollAsyncVerification(taskId)`
    (a serial `while` + `await sleep` loop, matching `pollAsyncSimulation`) instead of a
    fire-and-forget `setInterval`. Two problems are fixed: (a) the `async` branch used to
    return immediately, so the outer `finally` set `isVerifying=false` while polling was
    still running — the progress bar disappeared at once and the verify button
    re-enabled, letting the user launch duplicate tasks; now `isVerifying` stays true
    until polling truly ends. (b) the old `setInterval(async …)` callback could re-enter
    concurrently when a status request took longer than the 1s tick (duplicate requests,
    duplicate toasts, stale progress overwrites); the serial loop can't re-enter.
  - Both pollers surface terminal states (`FAILED`/`CANCELLED`) immediately with the
    task's `errorMessage` (simulation previously swallowed `FAILED` in its transient
    `catch` and only reported a generic timeout after 2 minutes).
  - Both pollers distinguish **permanent** status-fetch errors (HTTP 4xx — auth,
    forbidden, task-not-found) from **transient** ones (network blips, 5xx): permanent
    errors fail fast; transient errors retry until the poll ceiling.
  - Both are bounded (simulation 2 min, verification 10 min) so a task stuck in
    `RUNNING` (e.g. a hung NuSMV run) surfaces a timeout instead of polling forever.
- **Rule saving now honors the incremental-upsert contract.** `boardApi.getRules` used
  to prefix every existing rule's DB id as `rule_<id>`, and `saveRules` treated any
  `rule_`-prefixed id as new (sent `id: null`) — so every save of an existing rule
  re-inserted it and deleted the old row, churning ids and resetting `createdAt` (against
  the backend design and `docs/api/board.md`). `getRules` now returns the raw numeric id;
  only client-created rules (`rule_<timestamp>`) send `id: null`, so existing rules are
  updated in place.
- **Custom-template JSON import no longer corrupts enum variables.** The importer used to
  inject a default `LowerBound: 0 / UpperBound: 100` even when the source variable had
  `Values` (enum) — producing a manifest the backend rejects (`@AssertTrue
  isValidVariableDefinition`: `Values` XOR range, never both). It now emits `Values`
  as-is and only writes bounds when the source actually had them.
- **Custom-template API editor validates Trigger/Assignment completeness.** `confirmSaveApi`
  now blocks a Trigger with an Attribute but no Relation/Value, and any half-filled
  assignment, matching backend P1 (`validateTriggerCompleteness`) / assignment validation.
- **Custom-template manual-build path applies the same `Values` XOR range rule.** The
  form's build-manifest step used to always emit `LowerBound`, `UpperBound`, and filtered
  `Values` together; it now emits enum `Values` when present, otherwise the range —
  matching the JSON-import path (the UI currently exposes only range inputs, so this is a
  robustness/consistency fix rather than a live UI bug).
- **`boardApi.saveRules` return type corrected to `Promise<void>`.** It previously claimed
  to return `RuleForm[]` but actually unpacked the backend `RuleDto[]` shape; no caller
  consumed it. Callers needing the persisted rules (e.g. server-assigned ids) should
  re-fetch via `getRules()`.

#### Types (frontend contracts aligned to backend DTOs)
- `DeviceManifest` gained `Contents` (`DeviceContent { Name, Privacy, IsChangeable }`);
  `Dynamic` gained the optional `Value` (backend allows `Value` XOR `ChangeRate`);
  `DeviceAPI.Assignments` is now `DeviceAssignment[]` (`{ Attribute, Value }`) instead of
  `any[]`.
- `SimulationState` gained `rules?` and `trustPrivacies?` (backend `TraceStateDto`).
- `DeviceNode` gained `currentStateTrust?`, `variables?`, `privacies?` (backend
  `DeviceNodeDto`), removing the need for `(node as any)` casts.
- `PanelActive` gained the required `input` field to match backend `BoardActiveDto`
  (`{ input, status }`, both `@NotNull`).

#### Removed (dead / duplicate frontend types)
- `types/panel.ts` no longer exports `DockSide`, `DockState`, `PanelPosition` — leftovers
  from the removed panel/dock system with zero references. The layout DTO types
  (`PanelPosition`, `DockState`, `DockStateWrapper`) live in `types/canvas.ts`, used by
  `BoardLayoutDto`. This also removes the duplicate `DockState`/`PanelPosition`
  definitions that previously existed in both files.
- `types/spec.ts` no longer exports `relationOperators`, `RelationOperator`,
  `targetTypes`, `TargetType` — unused duplicates of the live versions in
  `assets/config/specTemplates.ts` (which is what components import). Prevents the two
  copies from drifting.
- `api/rules.ts` no longer exports `getRules`, `saveRules`, or the `Rule` interface —
  a dead second rule-persistence surface. Rule persistence lives only on `boardApi`
  (`api/board.ts`); `api/rules.ts` now owns rule *recommendation* only.
- `assets/config/specTemplates.ts` no longer redefines `SpecTemplateType` /
  `SpecTemplateDetail`; it imports them from `types/spec.ts` (and re-exports for existing
  importers), leaving `types/spec.ts` as the single source.
- `types/spec.ts` dropped the unused `SpecForm` interface; `types/rule.ts` dropped the
  unused `GLOBAL_VARIABLES` const and `GlobalVariableName` type (a runtime list that did
  not belong in a types file and had no references).

#### Documentation
- Clarified architecture documentation ownership and kept durable backend design notes
  in the owning API / architecture overview documents rather than a dated audit report.
- **`POST /api/board/rules/check-duplicate` integrated in frontend** as an optional
  manual pre-save check in `RuleBuilderDialog` (non-blocking: AI duplicate detection
  prompts confirmation, user can "Save Anyway").
- Aligned `ChatSession`/`ChatMessage` frontend types to backend DTOs (`userId: number`,
  added missing `createdAt`/`sessionId` fields).
- Updated `docs/guides/frontend-integration.md` to clarify `Trace*` / `Simulation*` type
  trees are intentionally parallel but NOT fully isomorphic (e.g., `TraceTrustPrivacy.trust`
  is `boolean | null` mirroring backend `TraceTrustPrivacyDto`, whereas
  `SimulationTrustPrivacy` uses looser `boolean` / optional `privacy`).

### 2026-03-04

#### Fixed
- **Blank `InitState` on modeless sensors**: 16 modeless sensor templates (Weather,
  Clock, Temperature Sensor, Humidity Sensor, …) had an empty-string `InitState`,
  which the AI device-creation path passed through verbatim, persisting `state=""`;
  a later `POST /api/board/nodes` was then rejected (400) by `DeviceNodeDto.state`'s
  `@NotBlank`. Fixes:
  - `NodeServiceImpl.getInitStateFromTemplate()` now `isBlank()`-checks `InitState`
    and falls back to `HARD_FALLBACK_STATE` (`"Working"`); log message corrected to
    "has missing or blank InitState".
  - `DeviceNodeMapper.toDto()` now backfills a null/blank `state` with `"Working"`
    (`FALLBACK_STATE`), preventing legacy dirty data from failing `@NotBlank` on a
    GET → POST round-trip.
  - Added 3 unit tests (`NodeServiceImplMutationTest`): empty, normal, and missing
    `InitState`.
- **Sprinkler Controller.json**: corrected an API-definition key from the erroneous
  `"s"` to `"Assignments"` (two occurrences).

### 2026-03-03

#### Changed — NuSMV generation pipeline
- **Identifier safety** (`DeviceSmvDataFactory`, `BoardStorageServiceImpl`):
  `sanitizeSmvToken()` now escapes NuSMV reserved words case-insensitively (including
  `W`), on top of space stripping, illegal-character replacement, and digit-prefix
  handling, for generation-time cleaning of mode/state names. `toVarName()` gained the
  same digit-prefix and reserved-word defenses. `computeIdentifiers()` guards
  `result` (varName), `base` (module-name prefix), and `suffix`. InternalVariable /
  ImpactedVariable names are validated at persistence time by
  `validateTemplateManifestForNuSmv()` (regex + reserved words + collision) and are
  **not** run through generation-time sanitization.
- **trust/privacy three-layer defense**: entry normalization
  (`normalizeTrustPrivacy()` = trim + lowercase); validation
  (`SmvModelValidator.validatePropertyValues()`); output-layer re-normalization in
  `SmvDeviceModuleBuilder`, defaulting null content privacy to `public`.
- **Numeric-bound clamping** (`SmvBoundsUtils`, `SmvMainModuleBuilder`): attack-mode
  upper-bound expansion centralized in `SmvBoundsUtils.resolveEffectiveUpperBound()`;
  `next()` candidate expressions clamp via `max(lower, min(upper, expr))`.
- **Defensive intensity handling**: `SmvGenerator` clamps `intensity` to `0..50`;
  `SmvBoundsUtils` additionally zeroes negative intensities.
- **`SmvSpecificationBuilder.build()`** gained a 5th parameter `enablePrivacy`; with
  privacy off, a privacy spec is skipped and emitted as
  `CTLSPEC FALSE -- privacy spec skipped: enablePrivacy=false` (defense-in-depth;
  `validateNoPrivacySpecs` upstream is the primary guard).
- **Regression coverage** (`SmvGeneratorFixesTest`): WITH-rate extreme NCR, internal
  variable boundary branches, `range=0` and negative-intensity cases.

#### Added / Changed — backend hardening
- **Production safety guard**: new `ProductionSafetyCheck` (`@PostConstruct`) refuses
  startup under a `prod`/`production` profile if `jwt.secret`,
  `spring.datasource.password` (`DB_PASSWORD`), or `volcengine.ark.api-key`
  (`VOLCENGINE_API_KEY`) still hold unsafe defaults. `PRODUCTION_MODE` removed; profile
  matching is case-insensitive. `JwtUtil.@PostConstruct` also WARN-logs a default key
  under prod.
- **Exception handling**: `IllegalArgumentException` → masked generic 400,
  `IllegalStateException` → 500, new `DataIntegrityViolationException` → 409 CONFLICT.
- **Thread-pool context propagation**: `ThreadConfig.TaskDecorator` deep-copies
  `Authentication`, `UserContextHolder.userId`, and MDC into child threads.
- **Async-task TOCTOU elimination**: `completeTask`/`failTask` became atomic
  conditional UPDATEs (`WHERE status <> CANCELLED`, `@Modifying(clearAutomatically =
  true)`); `handleCancellation` → `cancelTaskIfStillActive`
  (`WHERE status IN (PENDING, RUNNING)`). `TransactionTemplate` used for
  `VerificationServiceImpl.saveTraces()` and `ChatServiceImpl.processStreamChat()`.
- **Redis resilience**: `RedisTokenBlacklistService` counts consecutive failures
  (`AtomicInteger`), ERROR-alerting every 10th (`% ALERT_THRESHOLD`).
- **Request validation**: `@NotEmpty` devices, `@Size(max=10000)` chat content,
  `@NotNull @RequestBody` coverage (`BoardStorageController` via class-level
  `@Validated`).
- **Read-only transactions**: `@Transactional(readOnly = true)` on all read methods of
  `BoardStorageServiceImpl`, `VerificationServiceImpl`, `SimulationServiceImpl`,
  `ChatServiceImpl`.
- **Entity indexes/constraints**: indexes on `device_edge(user_id)`,
  `verification_task(user_id)`, `simulation_task(user_id)`; unique constraint on
  `device_templates(user_id, name)`.
- **DTO `progress` field**: exposed on `VerificationTaskDto` / `SimulationTaskDto`.
- **`VerificationTaskDto` consistency**: added `@NoArgsConstructor`,
  `@AllArgsConstructor`, `@JsonInclude(NON_NULL)` to align with `SimulationTaskDto`.
- **AI-tool safety**: `AiToolManager.execute()` catch-all returns a generic
  "Tool execution failed due to an internal error" (no `e.getMessage()` leak);
  `AddTemplateTool` pre-builds a `tolerantMapper`; `AddNodeTool` uses
  `parseDoubleOrNull()` / `parseIntOrNull()` to handle JSON null, non-numeric, and
  empty strings (all passed as `null` to trigger default layout values).
- **`ArkAiClient` configurable timeout**: `volcengine.ark.timeout-minutes` (default 5).
- **`JsonUtils`**: registered `JavaTimeModule`; added `fromJsonToStringList()` /
  `fromJsonList()`.
- **DELETE trace 404**: a missing trace now throws `ResourceNotFoundException`
  (previously a silent 200).
- **`JwtAuthenticationFilter`**: `getUserIdFromToken()` wrapped in try-catch —
  malformed tokens treated as unauthenticated.
- **Async controller pattern**: `verifyAsync` / `simulateAsync` return `Result<Long>`
  (no longer `ResponseEntity`); `TaskRejectedException` → `ServiceUnavailableException`.
- **Temp-file retention**: `cleanupTempFile()` is a no-op — `nusmv_*` temp directories
  are kept for post-mortem debugging.
- **Surefire JVM config**: `maven-surefire-plugin` adds
  `-Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading`, fixing
  Mockito/ByteBuddy `MockMaker` init on JDK 17.
- **Error-message suppression**: `application.yaml` sets
  `server.error.include-message: never` and `include-binding-errors: never`.
- **`SecurityConfig` ObjectMapper**: `SecurityFilterChain` uses the Spring-managed
  `ObjectMapper` (inherits `JavaTimeModule` etc.).
- **`ArkAiClient` ObjectMapper**: injected via constructor (Spring-managed) instead of
  a field-initialized `new ObjectMapper()`.
- **`ArkAiClient` parse pre-check**: `parseToolMessage()` / `parseAssistantToolCalls()`
  fast-check `content.stripLeading().startsWith("{")` before `readTree()`, keeping
  plain-text messages off the JSON path; fallback path logs at DEBUG.
