# Verification, Simulation & Fix API

Field-level contract for the verification, simulation, and auto-fix endpoints. This
document owns the DTO detail for these endpoints; the endpoint list itself lives in
[rest-endpoints.md](rest-endpoints.md).

Responses are wrapped in the standard `Result<T>` envelope (authoritative definition:
[overview.md](overview.md)). The `data` shapes below are what appears under that
envelope's `data` field.

Verified against code on 2026-07-03. Source:
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
| `specs` | `SpecificationDto[]` | yes (`@NotNull`) | — | Specifications to check |
| `isAttack` | `boolean` | no | `false` | Serialized as `isAttack` (`@JsonProperty`) |
| `intensity` | `int` (0–50) | no | `3` | Attack budget; `0` forces all `is_attack` to FALSE |
| `enablePrivacy` | `boolean` | no | `false` | Adds `privacy_*` variables; enlarges state space |

> Note: there is **no** `saveTrace` field. Traces are saved automatically when a
> violation is detected.

**Response**: `VerificationResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `safe` | `boolean` | `true` = all specs satisfied |
| `traces` | `TraceDto[]` | Counterexample traces (present when `safe = false`) |
| `specResults` | `Boolean[]` | Per-spec result, index-aligned to `specs` |
| `checkLogs` | `String[]` | Human-readable check log |
| `nusmvOutput` | `String` | Raw NuSMV output |

### `POST /api/verify/async` — asynchronous

Same request body. **Response `data`**: `Long` — the `taskId` (the **server**
generates and returns it; the client does not supply it).

### `GET /api/verify/tasks/{id}` — task status

**Response**: `VerificationTaskDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `Long` | Task id |
| `status` | `String` | `PENDING` / `RUNNING` / `COMPLETED` / `FAILED` / `CANCELLED` |
| `createdAt` / `startedAt` / `completedAt` | `LocalDateTime` | Lifecycle timestamps |
| `processingTimeMs` | `Long` | |
| `isSafe` | `Boolean` | Result once completed |
| `violatedSpecCount` | `Integer` | |
| `checkLogs` | `String[]` | |
| `errorMessage` | `String` | Present on `FAILED` |
| `progress` | `Integer` | 0–100 |

`@JsonInclude(NON_NULL)` — null fields are omitted.

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
| `conditions` | `Condition[]` | `@NotNull` |
| `command` | `Command` | `@NotNull` |
| `ruleString` | `String` | Human-readable form |
| `createdAt` | `LocalDateTime` | |

`Condition`: `{ deviceName (req), attribute (req), relation?, value? }` — `relation`
and `value` may be null for API-signal conditions.
`Command`: `{ deviceName (req), action (req), contentDevice?, content? }` — the last
two carry privacy-rule content.

### `SpecificationDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `String` | `@NotBlank`, ≤100 chars |
| `templateId` | `String` | `@NotBlank`, ≤10 chars; `"6"` → LTLSPEC, otherwise CTLSPEC |
| `templateLabel` | `String` | `@NotBlank`, ≤255 chars |
| `aConditions` | `SpecConditionDto[]` | `@NotNull`; serialized as `aConditions` |
| `ifConditions` | `SpecConditionDto[]` | `@NotNull` |
| `thenConditions` | `SpecConditionDto[]` | `@NotNull` |

`SpecConditionDto`: `{ id, side ('a'|'if'|'then'), deviceId, deviceLabel, targetType,
key, relation, value }`.

- `targetType` ∈ `state | variable | api | trust | privacy` (backend `@Pattern`,
  case-insensitive). For `trust`/`privacy`, `value` must be a legal enum —
  `trusted|untrusted` and `public|private` respectively (the SMV variable domains); an
  arbitrary string will not match at generation time.
- `deviceId` is resolved against the generated device set by **`varName` first, then a
  unique `templateName`** (ambiguous templateName → `AMBIGUOUS_DEVICE_REFERENCE`); it is
  **not** matched by label. The frontend therefore normalizes both a device's `varName`
  and each condition's `deviceId` with the same rule (`normalizeDeviceName`) before
  sending, so they line up. See
  [../guides/frontend-integration.md](../guides/frontend-integration.md).

See [../architecture/spec-templates.md](../architecture/spec-templates.md) for the
template ↔ CTL/LTL semantics and how each `targetType` maps to an SMV expression.

---

## 3. Trace structure

`TraceDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` / `userId` / `verificationTaskId` | `Long` | |
| `violatedSpecId` | `String` | |
| `violatedSpecJson` | `String` | Serialized spec |
| `states` | `TraceStateDto[]` | Ordered counterexample states |
| `createdAt` | `LocalDateTime` | |

> The `TraceDto` entity also carries a `requestJson` field (the request snapshot), but
> it is `@JsonIgnore` — **not serialized to clients**. It exists only to restore
> context for the internal `FixService` and never appears in an API response.

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

### `POST /api/simulate/async`

**Response `data`**: `Long` — `taskId` (server-generated).

### `GET /api/simulate/tasks/{id}` — `SimulationTaskDto`

`{ id, status, createdAt, startedAt, completedAt, processingTimeMs, requestedSteps,
steps, simulationTraceId, checkLogs: String[], errorMessage, progress }`.

### Persisted simulations

- `POST /api/simulate/traces` → `SimulationTraceDto` `{ id, userId, requestedSteps,
  steps, states, logs, nusmvOutput, requestJson, createdAt }`
- `GET /api/simulate/traces` → `SimulationTraceSummaryDto[]` `{ id, requestedSteps,
  steps, createdAt }` (summary, no states)
- `GET /api/simulate/traces/{id}` → `SimulationTraceDto` (full states)
- `DELETE /api/simulate/traces/{id}` → `null`
- `GET /api/simulate/tasks/{id}/progress` → `Integer`
- `POST /api/simulate/tasks/{id}/cancel` → `Boolean`

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
