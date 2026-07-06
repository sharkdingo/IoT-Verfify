# Verification, Simulation & Fix API

Field-level contract for the verification, simulation, and auto-fix endpoints. This
document owns the DTO detail for these endpoints; the endpoint list itself lives in
[rest-endpoints.md](rest-endpoints.md).

Responses are wrapped in the standard `Result<T>` envelope (authoritative definition:
[overview.md](overview.md)). The `data` shapes below are what appears under that
envelope's `data` field.

Verified against code on 2026-07-06. Source:
`controller/VerificationController.java`, `controller/SimulationController.java`,
and the DTOs under `dto/verification/`, `dto/simulation/`, `dto/device/`,
`dto/rule/`, `dto/spec/`, `dto/trace/`, `dto/fix/`.

---

## 1. Verification

### `POST /api/verify` — synchronous

**Request body**: `VerificationRequestDto`

| Field | Type | Required | Default | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `devices` | `DeviceVerificationDto[]` | yes (`@NotEmpty`) | — | Device instances |
| `rules` | `RuleDto[]` | no | `[]` | Automation rules |
| `specs` | `SpecificationDto[]` | yes (`@NotEmpty`) | — | Specifications to check |
| `isAttack` | `boolean` | no | `false` | Serialized as `isAttack` (`@JsonProperty`) |
| `intensity` | `int` (0–50) | no | `3` | Attack budget; `0` forces all `is_attack` to FALSE |
| `enablePrivacy` | `boolean` | no | `false` | Adds `privacy_*` variables; enlarges state space |

> Note: there is **no** `saveTrace` field. Traces are saved automatically when a
> violation is detected.
> Verification requires at least one specification for both synchronous and asynchronous
> requests. Use the simulation endpoint for no-spec state exploration.

**Response**: `VerificationResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `safe` | `boolean` | `true` = at least one emitted spec was checked and all emitted specs satisfied |
| `traces` | `TraceDto[]` | Counterexample traces (present when `safe = false`) |
| `specResults` | `SpecResultDto[]` | Per-emitted-spec result objects; specs skipped before SMV emission are counted/logged separately |
| `checkLogs` | `String[]` | Human-readable check log |
| `nusmvOutput` | `String` | Raw NuSMV output |
| `disabledRuleCount` | `Integer` | Count of rules whose generated guard failed closed to `FALSE` |
| `skippedSpecCount` | `Integer` | Count of specs skipped/degraded during SMV generation |

Generation warnings are also appended to `checkLogs` with `[rule-disabled]` and
`[spec-skipped]` markers. A response can be `safe=true` and still have non-zero counts;
that means the emitted SMV model was safe, but some requested rules/specs did not enter
the model as intended. If no specification is emitted to NuSMV, the backend returns
`safe=false` with empty `specResults` and a check log explaining that nothing was
verified.

`specResults` contains only specifications actually emitted to NuSMV, in emitted order.
Each item carries its own `specId`, so clients must not infer identity from array index
alone. When NuSMV output parsing is incomplete, the backend fails closed: missing emitted
specs still appear with `passed=false` and their generated expression when available.

### `POST /api/verify/async` — asynchronous

Same request body, including the non-empty `specs` constraint. **Response `data`**:
`Long` — the `taskId` (the **server** generates and returns it; the client does not
supply it).

Async submission snapshots the request and validates it before creating a task. REST
calls first run full DTO Bean Validation (HTTP 400 for malformed request shapes);
service and AI-tool callers run the NuSMV runtime validation needed for execution
(`devices`/`specs` present, null list items rejected, device identity, specification id
and template id, specification conditions, `intensity`, etc.). Validation failures are
returned before task creation (`ValidationException`, HTTP/tool status 422), so no
`taskId` is returned and clients must not start polling. If the task queue is saturated
after task creation, the backend marks that task `FAILED` internally and returns
`503 ServiceUnavailableException`; from the client perspective, a failed submit is
still "no pollable task".

### `GET /api/verify/tasks` — verification task inbox

Optional query parameter: `excludeTaskIds=1,2,3`. Use it when the frontend is already
polling specific task ids through `GET /api/verify/tasks/{id}` and wants the inbox
summary refresh to skip those same tasks.

**Response**: `VerificationTaskSummaryDto[]`, ordered by `createdAt` descending.

This is a lightweight list for task inbox UIs. It includes lifecycle/status fields,
`progress`, result summary fields (`isSafe`, `violatedSpecCount`,
`disabledRuleCount`, `skippedSpecCount`), and `errorMessage`, but intentionally omits
heavy completed-task details such as `specResults`, `checkLogs`, and `nusmvOutput`.
Fetch `GET /api/verify/tasks/{id}` when the user opens a specific task.

### `GET /api/verify/tasks/{id}` — task status

**Response**: `VerificationTaskDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `Long` | Task id |
| `status` | `String` | `PENDING` / `RUNNING` / `COMPLETED` / `FAILED` / `CANCELLED` |
| `createdAt` / `startedAt` / `completedAt` | `LocalDateTime` | Lifecycle timestamps |
| `processingTimeMs` | `Long` | |
| `isSafe` | `Boolean` | Result once completed |
| `violatedSpecCount` | `Integer` | Number of failed structured `specResults` once completed; falls back to trace count when no per-spec results are available |
| `disabledRuleCount` | `Integer` | Completed-task copy of generation-disabled rule count |
| `skippedSpecCount` | `Integer` | Completed-task copy of skipped/degraded spec count |
| `specResults` | `SpecResultDto[]` | Per-emitted-spec result objects once completed |
| `checkLogs` | `String[]` | Generation warnings and NuSMV execution/check logs when available (`COMPLETED` or `FAILED`) |
| `nusmvOutput` | `String` | Raw NuSMV output once completed |
| `errorMessage` | `String` | Present on `FAILED` |
| `progress` | `Integer` | 0–100 |

`@JsonInclude(NON_NULL)` — null fields are omitted. Completed async verification
tasks carry the same per-spec result and raw-output fields as synchronous verification:
`specResults`, `checkLogs`, `nusmvOutput`, `disabledRuleCount`, and `skippedSpecCount`.
Failed async tasks may still carry `checkLogs` for the steps reached before failure.

### `SpecResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `specId` | `String` | Stable `SpecificationDto.id` for the emitted specification |
| `passed` | `boolean` | `true` when NuSMV reported the emitted specification as satisfied |
| `expression` | `String` | NuSMV CTL/LTL expression checked for this emitted specification |

### Other verification endpoints

- `GET /api/verify/tasks/{id}/progress` → `Integer` (0–100)
- `POST /api/verify/tasks/{id}/cancel` → `Boolean` (whether it was cancelled)
- `GET /api/verify/traces` → `TraceDto[]`
- `GET /api/verify/traces/{id}` → `TraceDto`
- `DELETE /api/verify/traces/{id}` → `null` (404 `ResourceNotFoundException` if absent)

---

## 2. Nested request DTOs

### `DeviceVerificationDto`

| Field | Type | Required | Notes |
| :--- | :--- | :--- | :--- |
| `varName` | `String` | yes | Instance identifier used as the SMV variable name |
| `templateName` | `String` | yes | Resolved from the user's template table by `userId + templateName` |
| `state` | `String` | no | Current state |
| `currentStateTrust` | `String` | no | Device-level trust override (`trusted` / `untrusted`) |
| `variables` | `VariableStateDto[]` | no | `{ name, value, trust }` |
| `privacies` | `PrivacyStateDto[]` | no | `{ name, privacy }` |

### `RuleDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `Long` | Null for unsaved rules |
| `userId` | `Long` | |
| `conditions` | `Condition[]` | `@NotEmpty` |
| `command` | `Command` | `@NotNull` |
| `ruleString` | `String` | Human-readable form |
| `createdAt` | `LocalDateTime` | |

`Condition`: `{ deviceName (req), attribute (req), relation?, value? }` — `relation`
must be one of `=`, `!=`, `>`, `>=`, `<`, `<=`, `in`, `not_in`, or `not in` when present;
`value` is required whenever `relation` is present.
`Command`: `{ deviceName (req), action (req), contentDevice?, content? }` — the last
two carry privacy-rule content.

### `SpecificationDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `String` | `@NotBlank`, ≤100 chars |
| `templateId` | `String` | `@NotBlank`, `@Pattern("^[1-7]$")`; `"6"` → LTLSPEC, `"1"`–`"5"`/`"7"` → CTLSPEC. Unknown ids are rejected at the DTO boundary and fail closed during generation |
| `templateLabel` | `String` | `@NotBlank`, ≤255 chars |
| `formula` | `String` | Optional authored/display formula persisted with board specs |
| `devices` | `DeviceRefDto[]` | Selected-device metadata persisted as JSON; `@NotNull`, max 50 |
| `aConditions` | `SpecConditionDto[]` | `@NotNull`; serialized as `aConditions` |
| `ifConditions` | `SpecConditionDto[]` | `@NotNull` |
| `thenConditions` | `SpecConditionDto[]` | `@NotNull` |

`SpecConditionDto`:

| Field | Rules |
| :--- | :--- |
| `id` | Optional client-side identifier |
| `side` | Optional; when present must be `a`, `if`, or `then` and match the containing collection |
| `deviceId` | **Required** (`@NotBlank`). This is the primary device reference for spec conditions |
| `deviceLabel` | Optional display/secondary reference. It does **not** replace `deviceId` for request validation |
| `targetType` | **Required**; `state`, `variable`, `api`, `trust`, or `privacy` |
| `key` | **Required** |
| `relation` | **Required**; same enum as rule conditions |
| `value` | **Required** |

`side` is derived from the containing collection on save/read and, when supplied by a
client, must match that collection.
`DeviceRefDto`: `{ deviceId, deviceLabel, selectedApis: String[] }`; at least one of
`deviceId` / `deviceLabel` is required and `selectedApis` is non-null.

- `targetType` ∈ `state | variable | api | trust | privacy` (backend `@Pattern`,
  case-insensitive). For `trust`/`privacy`, `value` must be a legal enum —
  `trusted|untrusted` and `public|private` respectively (the SMV variable domains); an
  arbitrary string will not match at generation time.
- Device references are resolved by `DeviceReferenceResolver` using `deviceId` as the
  primary reference and `deviceLabel` as the secondary reference. For each reference it
  tries the raw value, then its digit-leading-normalized form (`normalizeDeviceName` /
  `DeviceNameNormalizer`), first as an exact device-map hit and then as a unique
  `templateName` fallback (ambiguous templateName → `AMBIGUOUS_DEVICE_REFERENCE`). This
  lets current-label references, normalized digit-leading labels, and legacy labels
  resolve through the same path. See
  [../architecture/nusmv-model.md](../architecture/nusmv-model.md#template-resolution-important)
  and [../guides/frontend-integration.md](../guides/frontend-integration.md).

See [../architecture/spec-templates.md](../architecture/spec-templates.md) for the
template ↔ CTL/LTL semantics and how each `targetType` maps to an SMV expression.
Only template ids `"1"` through `"7"` are supported and enforced by
`SpecificationDto.@Pattern("^[1-7]$")`; invalid ids are rejected at the DTO boundary or
recorded as skipped generation warnings rather than being silently accepted.

---

## 3. Trace structure

`TraceDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` / `userId` / `verificationTaskId` | `Long` | |
| `violatedSpecId` | `String` | |
| `violatedSpecJson` | `String` | Serialized spec |
| `states` | `TraceStateDto[]` | Ordered counterexample states |
| `isAttack` | `Boolean` | Attack mode this trace was verified under (derived from the stored request snapshot; null for legacy traces) |
| `intensity` | `Integer` | Attack intensity this trace was verified under (derived; null for legacy traces) |
| `enablePrivacy` | `Boolean` | Privacy-modeling flag this trace was verified under (derived; null for legacy traces) |
| `createdAt` | `LocalDateTime` | |

> The `TraceDto` entity also carries a `requestJson` field (the request snapshot), but
> it is `@JsonIgnore` — **not serialized to clients**. It exists only to restore
> context for the internal `FixService` and never appears in an API response. The
> `isAttack` / `intensity` / `enablePrivacy` fields above are **derived** from that
> snapshot by `TraceMapper` so a historical trace can be labelled with the parameters it
> was run under, without exposing the full request.

`TraceStateDto`: `{ stateIndex, devices: TraceDeviceDto[], rules: Integer[],
trustPrivacies: TraceTrustPrivacyDto[], envVariables: TraceVariableDto[] }`.

`TraceDeviceDto`: `{ deviceId, deviceLabel, templateName, state, mode,
variables: TraceVariableDto[], trustPrivacy[], privacies[] }`.
`TraceVariableDto`: `{ name, value, trust }`.
`TraceTrustPrivacyDto`: `{ name, trust (Boolean), privacy ('private'|'public') }`.

---

## 4. Simulation

### `POST /api/simulate` — synchronous (not persisted)

**Request body**: `SimulationRequestDto` — same as `VerificationRequestDto` but with
**no `specs`** field and an added `steps`:

| Field | Type | Required | Default | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `devices` | `DeviceVerificationDto[]` | yes (`@NotEmpty`) | — | |
| `rules` | `RuleDto[]` | no | `[]` | |
| `steps` | `int` (1–100) | no | `10` | Number of simulation steps |
| `isAttack` | `boolean` | no | `false` | |
| `intensity` | `int` (0–50) | no | `3` | |
| `enablePrivacy` | `boolean` | no | `false` | |

**Response**: `SimulationResultDto` — `{ states: TraceStateDto[], steps,
requestedSteps, nusmvOutput, logs: String[] }`.

Synchronous simulation uses the same request snapshot and runtime validation as async
simulation. Validation failures are returned as errors (REST 400 for DTO Bean Validation
or 422 for service `ValidationException`), not as a success-shaped empty simulation
result.

### `POST /api/simulate/async`

**Response `data`**: `Long` — `taskId` (server-generated).

Async simulation submission follows the same lifecycle contract as async verification:
the backend snapshots and validates the request before task creation. REST calls first
run full DTO Bean Validation; service and AI-tool callers run NuSMV runtime validation
for required devices, null list items, device identity, `steps`, and `intensity`.
Structurally invalid rules are rejected at the boundary: null rule elements, null
commands, and blank `command.deviceName` / `command.action` all return validation
errors instead of silently disappearing from the model. Rules that are structurally
present but cannot be emitted semantically (for example, references that cannot be
resolved during SMV generation) may still be disabled fail-closed with warnings in
`checkLogs`. Validation failure returns no `taskId`, and queue saturation marks the
created task `FAILED` before returning `503`. Clients should start polling only after
this endpoint successfully returns a task id.

### `GET /api/simulate/tasks` — simulation task inbox

Optional query parameter: `excludeTaskIds=1,2,3`. Use it when the frontend is already
polling specific task ids through `GET /api/simulate/tasks/{id}` and wants the inbox
summary refresh to skip those same tasks.

**Response**: `SimulationTaskSummaryDto[]`, ordered by `createdAt` descending.

This lightweight list includes lifecycle/status fields, `progress`, requested/completed
step counts, `simulationTraceId`, and `errorMessage`. It omits logs and raw NuSMV
output; completed async simulations should be inspected through the referenced
`SimulationTraceDto` when `simulationTraceId` is present.

### `GET /api/simulate/tasks/{id}` — `SimulationTaskDto`

`{ id, status, createdAt, startedAt, completedAt, processingTimeMs, requestedSteps,
steps, simulationTraceId, checkLogs: String[], errorMessage, progress }`.

Completed async simulations store the full states, execution logs, request JSON, and
raw NuSMV output in the referenced `SimulationTraceDto`; the task DTO stays a polling
summary.

### Persisted simulations

- `POST /api/simulate/traces` → `SimulationTraceDto` `{ id, userId, requestedSteps,
  steps, states, logs, nusmvOutput, requestJson, createdAt }`
- `GET /api/simulate/traces` → `SimulationTraceSummaryDto[]` `{ id, requestedSteps,
  steps, createdAt }` (summary, no states)
- `GET /api/simulate/traces/{id}` → `SimulationTraceDto` (full states)
- `DELETE /api/simulate/traces/{id}` → `null`
- `GET /api/simulate/tasks/{id}/progress` → `Integer`
- `POST /api/simulate/tasks/{id}/cancel` → `Boolean`

Persisted simulation `requestJson` is the validated execution snapshot used for the
NuSMV run, not a later serialization of the caller's mutable request object.

---

## 5. Auto-fix

For the algorithm (strategies, forward verification), see
[../architecture/auto-fix.md](../architecture/auto-fix.md). This
section is the API contract only.

### `GET /api/verify/traces/{id}/fault-rules` — fault localization

Fast, no NuSMV invocation. **Response**: `FaultRuleDto[]`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `ruleIndex` | `int` | Index in the request's rule list (stable key) |
| `ruleId` | `Long` | DB id, null for unsaved rules |
| `ruleString` | `String` | |
| `triggerStep` | `int` | Counterexample step where the rule fired |
| `targetDevice` | `String` | |
| `targetAction` | `String` | |
| `conflicting` | `boolean` | |
| `conflictWithRuleIndex` | `Integer` | |
| `reason` | `String` | |

### `POST /api/verify/traces/{id}/fix` — fix suggestions

May invoke NuSMV multiple times (bounded by `FIX_TIMEOUT_MS`, see
[configuration.md](../getting-started/configuration.md)).

**Request body**: `FixRequestDto` — optional; omit or send `null` for defaults.

| Field | Type | Default | Notes |
| :--- | :--- | :--- | :--- |
| `strategies` | `String[]` | `["parameter","condition","disable"]` | Strategies to try, in order |
| `preferredRanges` | `Map<String, PreferredRange>` | `null` | Keys like `r{ruleIdx}_c{condIdx}` (e.g. `r0_c1`); value `PreferredRange { lower, upper }` (both `@NotNull`, inclusive) |

**Response**: `FixResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `traceId` | `Long` | |
| `violatedSpecId` | `String` | |
| `faultRules` | `FaultRuleDto[]` | Same schema as fault localization |
| `suggestions` | `FixSuggestionDto[]` | Verified fix proposals |
| `fixable` | `boolean` | Whether ≥1 suggestion was found |
| `summary` | `String` | Includes timeout/drift warnings if applicable |
| `unusedPreferredRangeKeys` | `String[]` | `preferredRanges` keys that matched nothing |

`FixSuggestionDto`: `{ strategy, description, parameterAdjustments[],
conditionAdjustments[], disabledRuleIndices: Integer[], verified }`.
`ParameterAdjustment`: `{ ruleIndex, conditionIndex, attribute, relation,
originalValue, newValue, lowerBound, upperBound }`.
`ConditionAdjustment`: `{ ruleIndex, conditionIndex, action, attribute, description,
deviceName, relation, value }`.

### `POST /api/verify/traces/{id}/fix/apply` — apply a fix suggestion

Applies a fix suggestion (as returned by `/fix`) to the user's persisted board rules and
saves them. The frontend sends back the exact suggestion the user saw (WYSIWYG).

**Request body**: `FixApplyRequestDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `strategy` | `String` | `parameter` / `condition` / `disable`; must match `suggestion.strategy` |
| `suggestion` | `FixSuggestionDto` | The suggestion the user acted on |
| `preferredRanges` | `Map<String, PreferredRange>` | Optional. The same ranges `/fix` used to produce the suggestion; the server replays them in its recompute so the same search space (and result) is reproduced. Omit if `/fix` was called without ranges |

**Safety** — the server does **not** trust the client:

- **Server re-verification.** The client's `suggestion.verified` flag is ignored. On apply the
  server recomputes the fix for the requested strategy against the trace's own context (a fresh
  NuSMV-verified run, replaying `preferredRanges`) and requires the submitted suggestion to match
  that recomputed, verified suggestion (by the operations it encodes). If the server cannot reproduce
  a verified suggestion, or the submitted one differs, it **rejects with `400`**. This makes "only
  verified fixes apply" independent of any client-supplied boolean.
- **Board-drift guard (rules).** The suggestion's `ruleIndex`/`conditionIndex` are relative to the
  trace's verification-time rule snapshot. The server aligns that snapshot with the current board
  rules by index + **order-preserving** fingerprint (device varName, attribute, relation, value, plus
  command device/action and `contentDevice`/`content`) and rejects with `400` if the board drifted
  (rules added/removed/edited/reordered since verification), so a stale index never edits the wrong
  rule or condition. This check runs **inside the same per-user write lock + transaction** as the save
  (read → check → apply → write are one atomic critical section), so a concurrent save cannot slip in
  between the check and the write.
- **Template-drift guard.** apply rebuilds the NuSMV device model from the **current** device templates,
  so if a template used by the trace was modified after the trace was recorded, the recompute would prove
  (and persist) a fix against a different model than the one that produced the counterexample. This is
  **rejected with `400`**. (`/fix` only *warns* about template drift in its summary; apply blocks.) The
  template check **fails closed on apply**: if the template repository errors so drift cannot be
  confirmed, apply is rejected rather than proceeding. (`/fix` fails open — a repo error only drops the
  advisory warning.)
- **Strategy mismatch** (`strategy` ≠ `suggestion.strategy`) is rejected with `400`.
- **Spec/device-drift guard.** apply also rejects with `400` when the current board's specifications or
  device instance state (variables, privacies, initial state, trust) changed after the trace was
  recorded. The server recompute replays the trace's *stored* context, so on its own it would re-prove
  the same fix and never notice a spec/device-only edit (edits that touch neither rules nor templates).
  apply therefore compares a canonical **semantic fingerprint** of the trace snapshot against the current
  board. It is *not* a raw-JSON equality check: both sides run through the same normalization (device
  names canonicalized, empty variable/privacy lists manifest-defaulted, values de-quoted), so an
  untouched board matches its frontend-transformed snapshot instead of misfiring. This check runs
  **inside the same per-user write lock + transaction** as the save, so a concurrent spec/device edit
  cannot slip in between the check and the write. If the current board no longer builds a valid device
  model, the check **fails closed**, distinguishing the cause: a genuinely invalid/changed board
  (device removed, template deleted, manifest unparseable) rejects with `400` ("re-run verification"),
  while an infrastructure error that leaves drift *unconfirmable* (e.g. template repository unavailable)
  rejects with `503` ("retry later") rather than misattributing it to a board change.
  Verification flags (`isAttack`/`intensity`/`enablePrivacy`) are per-request and not persisted for
  re-proving, so re-run verification after changing them.

The server then applies its own recomputed suggestion (not the client's) to a deep copy of the
persisted rules, so what is saved is exactly what NuSMV just verified.

**Response**: `FixApplyResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `applied` | `boolean` | `true` on success |
| `strategy` | `String` | The applied strategy |
| `message` | `String` | Human-readable summary |
| `rules` | `RuleDto[]` | The full persisted rule list after applying; current frontend shows the response message, then re-fetches rules via `getRules()` |

Effect per strategy: `parameter` overwrites the target condition's value (and relation);
`condition` adds/removes conditions; `disable` deletes the flagged rules. A condition fix
that would leave a rule with no trigger conditions is rejected.

### `GET /api/verify/tasks/{id}/traces` — traces for an async task

Returns the `TraceDto[]` produced by a specific async verification task, scoped to the
current user. Used by the frontend to display counterexamples for the task that just
finished, rather than mixing in traces from earlier/concurrent runs.
