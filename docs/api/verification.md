# Verification, Simulation & Fix API

Field-level contract for the verification, simulation, and auto-fix endpoints. This
document owns the DTO detail for these endpoints; the endpoint list itself lives in
[rest-endpoints.md](rest-endpoints.md).

Responses are wrapped in the standard `Result<T>` envelope (authoritative definition:
[overview.md](overview.md)). The `data` shapes below are what appears under that
envelope's `data` field.

Verified against code on 2026-07-16. Source:
`controller/VerificationController.java`, `controller/SimulationController.java`,
and the DTOs under `dto/verification/`, `dto/simulation/`, `dto/device/`,
`dto/rule/`, `dto/spec/`, `dto/trace/`, `dto/fix/`.

---

## 1. Verification

### `POST /api/verify` — synchronous

**Request body**: `VerificationRequestDto`

This endpoint consumes the **model-boundary** shape. Device references inside
`RuleDto` and `SpecificationDto` must already match `devices[].varName` (the
NuSMV-safe normalized form of the board `DeviceNode.id`). Board storage endpoints use
raw board node ids for the same DTO fields; the frontend `modelRequest.ts` builder and
backend `BoardDataConverter` perform the boundary conversion before verification or
simulation.

The request is strict at every nesting level. Unknown fields and scalar type coercions
return HTTP `400`; a misspelled `isAttack`, `enablePrivacy`, device label, rule field, or
environment override is never ignored and cannot silently weaken the model. DTO shape
constraints (for example empty `devices`/`specs`) also return structured HTTP `400`
errors; model/template semantic mismatches discovered after parsing return `422`.

| Field | Type | Required | Default | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `devices` | `DeviceVerificationDto[]` | yes (`@NotEmpty`) | — | Device instances |
| `environmentVariables` | `BoardEnvironmentVariableDto[]` | no | `[]` | Board-level environment pool overrides. Names must be unique. A missing item or a `null` value/trust/privacy field uses the referenced template default; an explicit blank or invalid field is rejected before defaults are merged |
| `rules` | `RuleDto[]` | no | `[]` | Automation rules. A persisted positive `id` is optional correlation identity for user-facing triggered-rule/link snapshots; it does not change model behavior |
| `specs` | `SpecificationDto[]` | yes (`@NotEmpty`) | — | Specifications to check |
| `isAttack` | `boolean` | no | `false` | Serialized as `isAttack` (`@JsonProperty`). `true` is rejected when the scene has neither an automation command-delivery link nor a template reading marked `FalsifiableWhenCompromised=true`, because attack selection would not change model behavior |
| `attackBudget` | `int` | no | `0` | Maximum compromised points in one model branch, not an exact count. It must be exactly `0` when `isAttack=false`; a positive value is rejected rather than silently discarded. When attack modeling is enabled the caller must explicitly provide `1..50`, no greater than the behavior-changing attack surface: one point for each device with a declared falsifiable reading or at least one incoming rule command, plus one logical command-delivery point per submitted rule. That rule-derived point is counted once regardless of how many source/trigger edges the canvas renders for the rule; it is not a discovered physical network segment. Inert device instances are excluded. `50` is the current per-run input cap, not the scene's attack-surface size: if `modelSemantics.modeledAttackPointCount > 50`, one run does not cover branches with more than 50 simultaneous compromises. The budget never widens a variable domain, and one call does not compute the minimum violating budget. |
| `enablePrivacy` | `boolean` | no | `false` | Adds privacy-label variables and enlarges state space. Any privacy condition in a submitted specification makes the effective value `true`, even if the caller omitted or set this field to `false`; responses return the effective value |

> Note: there is **no** `saveTrace` field. Traces are saved automatically when a
> violation is detected.
> Verification requires at least one specification for both synchronous and asynchronous
> requests. Use the simulation endpoint for no-spec state exploration.

**Response**: `VerificationResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `isAttack` | `Boolean` | Whether compromised device-instance and automation-link behavior was included |
| `attackBudget` | `int` | Maximum compromised points allowed in any checked branch; a branch may contain any count from zero through this value |
| `enablePrivacy` | `boolean` | Whether privacy-label propagation was modeled |
| `modelSemantics` | `ModelSemanticsDto` | Machine-readable environment-evolution, local-variable, attack, trust, and privacy assumptions required to interpret the conclusion |
| `modelSnapshot` | `ModelRunSnapshotDto` | User-facing scope captured at the model boundary, including item counts and confirmation that referenced template manifests were frozen for this run |
| `outcome` | `SATISFIED \| VIOLATED \| INCONCLUSIVE` | User-facing conclusion. `INCONCLUSIVE` means no reliable property conclusion was produced; it is not a violation. |
| `modelComplete` | `boolean` | Whether every submitted rule/spec entered the generated model and the emitted result set was parsed reliably |
| `traces` | `TraceDto[]` | Counterexample traces for parsed property violations; an inconclusive result can have no trace |
| `specResults` | `SpecResultDto[]` | Per-emitted-spec result objects; specs skipped before SMV emission are counted/logged separately |
| `checkLogs` | `String[]` | Human-readable check log |
| `nusmvOutput` | `String` | Raw NuSMV output |
| `disabledRuleCount` | `Integer` | Count of rules whose generated guard failed closed to `FALSE` |
| `skippedSpecCount` | `Integer` | Count of specs omitted because no valid NuSMV property could be generated |
| `generationIssues` | `ModelGenerationIssueDto[]` | Item-level name and reason for every disabled rule or omitted specification |
| `historyPersistence` | `RunPersistenceDto` | Separate status for adding this completed result to run history; it does not change the formal outcome |

Every synchronous verification attempts to persist its completed result as one run.
The response keeps the model-checking conclusion even when that separate persistence
step fails. `historyPersistence.status=SAVED` includes the authoritative `runId`.
`OUTCOME_UNKNOWN` with `reasonCode=RUN_HISTORY_SAVE_OUTCOME_UNKNOWN` means the formal
result is still usable, but the client must refresh history before deciding whether a
row exists; it must not retry the verification automatically or claim that the result
was saved. Counterexamples and the completed run are written in one transaction, so a
confirmed saved run cannot contain only part of its counterexamples. Requests rejected
before a result exists do not create a history row.

`RunPersistenceDto` is `{ status, runId?, reasonCode? }`. `status` is `SAVED`,
`NOT_REQUESTED`, `FAILED`, or `OUTCOME_UNKNOWN`. `NOT_REQUESTED` is used by preview-only
simulation; `FAILED` means the server knows no history row was created; and
`OUTCOME_UNKNOWN` means the write outcome could not be confirmed after an exception.

`ModelSemanticsDto` also carries the immutable run-snapshot counts
`modeledDeviceAttackPointCount`, `modeledFalsifiableReadingDeviceCount`,
`modeledAutomationLinkAttackPointCount`, and `modeledAttackPointCount` (the device/link
sum). The falsifiable-reading count is a subset of the device count; the device count
includes only instances whose
compromise can change behavior: a declared falsifiable reading and/or an incoming rule
command. Clients must use these values when explaining an
attack budget or historical trace; recomputing the denominator from the current board can
misdescribe an older run after devices or rules change.

To estimate the minimum number of compromise points needed for a violation, callers
must run complete verification repeatedly with different `attackBudget` upper bounds.
The API does not present the selected upper bound or a counterexample's runtime count as
the minimum attack intensity.

Generation warnings are also appended to `checkLogs` with `[rule-disabled]` and
`[spec-skipped]` markers for technical diagnostics. `generationIssues` is the
user-facing explanation source; clients must render each `itemLabel` and localize its
stable `reasonCode`. The English `reason` is a technical diagnostic and must not be used
as ordinary localized UI copy.
`SATISFIED` with `modelComplete=false` means the emitted properties were satisfied on
a reduced generated model; clients must present it as "checked properties satisfied,
but model incomplete". If no specification is emitted, or the emitted result set
cannot be mapped reliably, the backend returns `outcome=INCONCLUSIVE`,
`modelComplete=false`, and a `[verification-inconclusive]` log. Only a reliable false
property result produces `outcome=VIOLATED`.

The frontend treats this response as an authoritative conclusion contract rather than a
best-effort payload. Before showing a successful, violated, or inconclusive result it
requires explicit `outcome` and `modelComplete`, consistent run-context
`modelSemantics`, a frozen `modelSnapshot`, all result/log/trace arrays, and itemized `generationIssues` matching
the omission counts. A successful HTTP response missing those fields is shown as an
uninterpretable run error; the client does not infer completeness from absent warnings.
The same check is applied to persisted counterexamples. A completed async task must
contain the complete result fields before the Board reconstructs its result; it is not
allowed to infer the task outcome from traces or logs.

`specResults` contains only specifications actually emitted to NuSMV, in emitted order.
Each item carries its own `specId`, so clients must not infer identity from array index
alone. When output parsing is incomplete, missing emitted specs may still appear with
`outcome=INCONCLUSIVE` for diagnostic alignment. They must not be presented as proven
violations. A specification that generation cannot translate is omitted rather than
replaced by an always-false property, so it cannot create an artificial violation or
counterexample.

### `POST /api/verify/async` — asynchronous

Same request body, including the non-empty `specs` constraint. **Response `data`** is
the newly created `VerificationTaskDto`, not a bare id. Its `id` is the server-generated
polling identity; `status`, `progress`, `modelSemantics`, and `modelSnapshot` are the
authoritative values already persisted for the accepted task. A successful submission
means only that the task was accepted. It does not mean verification completed, and
active tasks do not contain a property `outcome`.

Async submission snapshots the request and validates it before creating a task. It also
captures every referenced device-template manifest once. Validation and later worker
generation reuse that exact captured set; editing a template while the task is queued
cannot change the model behind the accepted task. REST
calls first run full DTO Bean Validation (HTTP 400 for malformed request shapes);
service and AI-tool callers run the NuSMV runtime validation needed for execution
(`devices`/`specs` present, null list items rejected, device identity, specification id
and template id, specification conditions, `attackBudget`, etc.). After structural
validation, the backend loads the current user's device templates and rejects
template-semantic mismatches before NuSMV generation: non-signal APIs cannot be used
as rule/spec conditions, command actions must exist on the target template, and
state/mode/trust/privacy condition keys and enum values must be legal. Variable
conditions are also checked against template domains: declared enum `Values` and
numeric `LowerBound..UpperBound`. Validation failures are
returned before task creation (`ValidationException`, HTTP/tool status 422), so no
`taskId` is returned and clients must not start polling. If the task queue is saturated
after task creation, the backend marks that task `FAILED` internally and returns
`503 ServiceUnavailableException`; from the client perspective, a failed submit is
still "no pollable task".

An async task reaches `progress=100` only in the same atomic completion operation that
stores its final result and counterexamples. If that completion write does not commit,
the task is marked `FAILED` when possible; clients must never interpret an earlier 100%
progress update as a completed result.

### `GET /api/verify/tasks` — verification task status layer

Optional query parameter: `excludeTaskIds=1,2,3`. Use it when the frontend is already
polling specific task ids through `GET /api/verify/tasks/{id}` and wants the inbox
summary refresh to skip those same tasks.

**Response**: `VerificationTaskSummaryDto[]`, ordered by `createdAt` descending.

This list contains only background work that still needs task-level attention:
`PENDING`, `RUNNING`, `FAILED`, or `CANCELLED`. `COMPLETED` tasks are deliberately
excluded because they are user results, not pending work; retrieve them through
`GET /api/verify/runs`. Active rows expose progress and frozen run context. Failed and
cancelled rows explain why no result exists. Heavy result details remain available from
the per-id polling endpoint while a client finishes its own accepted task.

`DELETE /api/verify/tasks/{id}` dismisses a `FAILED` or `CANCELLED` task that produced
no result. Active tasks must be cancelled first. Completed rows must be deleted through
the run-history endpoint so their counterexamples are removed atomically.

### Completed verification runs

- `GET /api/verify/runs` returns `VerificationRunSummaryDto[]`, ordered by completion
  time descending. It includes run scope/context, `outcome`, `modelComplete`, omission
  counts and itemized `generationIssues`, `violatedSpecCount`, `counterexampleCount`,
  and lightweight nested `counterexamples` summaries. It does not return trace states.
- `GET /api/verify/runs/{id}` returns `VerificationRunDto`, adding `specResults`,
  `checkLogs`, and `nusmvOutput` without task lifecycle fields such as status/progress.
- `GET /api/verify/runs/{id}/traces` returns the run's replayable `TraceDto[]`.
- `DELETE /api/verify/runs/{id}` deletes the complete result and all linked
  counterexamples in one transaction.

`VerificationRunSummaryDto` fields:

| Field | Type | Meaning |
| :--- | :--- | :--- |
| `id` | `Long` | Stable run identity used only for result actions/API correlation |
| `createdAt` / `startedAt` / `completedAt` | `LocalDateTime` | Run timestamps; there is no task status in this completed-result DTO |
| `processingTimeMs` | `Long` | Elapsed processing time when available |
| `isAttack` / `attackBudget` / `enablePrivacy` | `Boolean` / `Integer` / `Boolean` | Frozen verification assumptions |
| `modelSemantics` / `modelSnapshot` | DTOs | Structured model meaning and submitted scope |
| `outcome` / `modelComplete` | enum / `Boolean` | Verification conclusion and completeness qualifier |
| `violatedSpecCount` | `Integer` | Reliably false emitted specifications |
| `counterexampleCount` | `Integer` | Persisted traces that can be opened/replayed; may be lower than `violatedSpecCount` |
| `disabledRuleCount` / `skippedSpecCount` | `Integer` | Model omissions |
| `generationIssues` | `ModelGenerationIssueDto[]` | Itemized omission explanations |
| `counterexamples` | `TraceSummaryDto[]` | Lightweight nested evidence with id, violated-specification snapshot, state count, and timestamp; full states are loaded only when replay/fix is opened |
| `dataAvailable` | `Boolean` | `true` when persisted semantic fields decoded successfully; `false` keeps a damaged row visible without treating it as usable |
| `unavailableReasonCode` | `String` | Present for an unavailable row; currently `PERSISTED_SEMANTIC_DATA_INVALID` |

`VerificationRunDto` contains the run metadata and semantic result fields plus
`specResults`, `checkLogs`, and `nusmvOutput`. It reports `counterexampleCount` but does
not embed counterexample summaries or full trace states; load those from
`GET /api/verify/runs/{id}/traces`.

`violatedSpecCount` and `counterexampleCount` are intentionally separate. NuSMV can
report a property as false without returning a trace that the parser can reconstruct;
clients must say how many violations were concluded and how many counterexamples can
actually be replayed. A verification run is the top-level history item. Its
counterexamples are evidence/actions nested under that result, not independent runs.
One malformed run or trace summary does not fail the whole history list. The backend
returns an unavailable placeholder with its stable id/timestamp where possible. Clients
may offer deletion, but must disable open, replay, and repair actions for that item.

### `GET /api/verify/tasks/{id}` — task status

**Response**: `VerificationTaskDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `Long` | Task id |
| `status` | `String` | `PENDING` / `RUNNING` / `COMPLETED` / `FAILED` / `CANCELLED` |
| `createdAt` / `startedAt` / `completedAt` | `LocalDateTime` | Lifecycle timestamps |
| `processingTimeMs` | `Long` | |
| `isAttack` / `attackBudget` / `enablePrivacy` | `Boolean` / `Integer` / `Boolean` | Stored run context, not the current frontend form |
| `modelSemantics` | `ModelSemanticsDto` | Structured assumptions for this task's model |
| `modelSnapshot` | `ModelRunSnapshotDto` | Frozen submission scope, available from task creation onward rather than only after completion |
| `outcome` | `VerificationOutcome` | `SATISFIED`, `VIOLATED`, or `INCONCLUSIVE` once completed |
| `modelComplete` | `Boolean` | Whether the completed task checked the complete generated model reliably |
| `violatedSpecCount` | `Integer` | Number of explicit `VIOLATED` structured `specResults` once completed; falls back to trace count when no per-spec results are available |
| `disabledRuleCount` | `Integer` | Completed-task copy of generation-disabled rule count |
| `skippedSpecCount` | `Integer` | Completed-task copy of omitted specification count |
| `generationIssues` | `ModelGenerationIssueDto[]` | Item-level omitted-rule/specification explanations |
| `specResults` | `SpecResultDto[]` | Per-emitted-spec result objects once completed |
| `checkLogs` | `String[]` | Generation warnings and NuSMV execution/check logs when available (`COMPLETED` or `FAILED`) |
| `nusmvOutput` | `String` | Raw NuSMV output once completed |
| `errorMessage` | `String` | Technical failure diagnostic present on `FAILED`; clients show a localized no-result state first and place this text in an advanced/technical disclosure |
| `progress` | `Integer` | 0–100 |

`@JsonInclude(NON_NULL)` — null fields are omitted. Completed async verification
tasks carry the same conclusion and per-spec fields as synchronous verification:
`outcome`, `modelComplete`, `specResults`, `checkLogs`, `nusmvOutput`,
`disabledRuleCount`, `skippedSpecCount`, and `generationIssues`.
Failed async tasks may still carry `checkLogs` for the steps reached before failure.
Task fields are status-dependent: active tasks do not publish `outcome` or
`modelComplete`; terminal tasks have `completedAt` and `progress=100`; `FAILED` has a
non-blank `errorMessage`; and `COMPLETED` has the complete conclusion fields above.
The frontend validates these invariants before it renders an inbox row or reconstructs
a result. A malformed HTTP 200 is an uninterpretable task response, not a poll timeout
or evidence that the run completed.

### `SpecResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `specId` | `String` | Stable technical `SpecificationDto.id` for correlation; ordinary result UI keeps it in technical details |
| `templateId` | `String` | Submitted specification-template semantics captured for this run |
| `specificationLabel` | `String` | User-facing template label captured for self-contained result interpretation |
| `formulaPreview` | `String` | Descriptive formula rebuilt from the submitted structured conditions, submitted device labels, and frozen template semantics; contains user concepts rather than generated NuSMV identifiers |
| `formulaKind` | `CTL \| LTL` | Language of the emitted property, derived from the actual emitted expression/template |
| `outcome` | `SATISFIED \| VIOLATED \| INCONCLUSIVE` | Per-property conclusion. Missing or unreliable parser output is `INCONCLUSIVE`, never a synthetic violation. |
| `expression` | `String` | Actual NuSMV CTL/LTL expression checked for this emitted specification; technical detail that may contain generated identifiers |

### `ModelGenerationIssueDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `issueType` | `RULE_DISABLED \| SPECIFICATION_SKIPPED` | Kind of model omission |
| `itemLabel` | `String` | User-readable automation or specification label; not a database/NuSMV id |
| `reasonCode` | `ModelGenerationIssueReasonCode` | Stable localization key describing why the item did not enter the generated model |
| `reason` | `String` | English technical diagnostic for logs/advanced details; clients localize ordinary UI from `reasonCode` |

`ModelGenerationIssueReasonCode` is one of
`RULE_NO_TRIGGER_CONDITIONS`, `RULE_NULL_TRIGGER_CONDITION`,
`RULE_UNRESOLVABLE_TRIGGER_CONDITION`, `RULE_NO_RESOLVABLE_TRIGGER_CONDITIONS`,
`RULE_PROPERTY_PROPAGATION_UNAVAILABLE`, `SPEC_NO_CHECKABLE_CONDITIONS`,
`SPEC_PRIVACY_MODELING_DISABLED`, `SPEC_UNSUPPORTED_RELATION`,
`SPEC_AMBIGUOUS_STATE`, `SPEC_UNDECLARED_SECURITY_PROPERTY`,
`SPEC_UNKNOWN_DEVICE`, `SPEC_TEMPLATE_SHAPE_MISMATCH`, `SPEC_INVALID_VALUE`,
`SPEC_UNSUPPORTED_CONDITION`, or `UNCLASSIFIED_GENERATION_ISSUE`.

### `ModelSemanticsDto`

| Field | Values / meaning |
| :--- | :--- |
| `attackPointUnit` | `BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK`; a device contributes a point only when it has a declared falsifiable reading or is a rule-command target, and each submitted rule contributes one logical command-delivery link point |
| `attackSelectionPolicy` | `NOT_MODELED` or `UP_TO_ATTACK_BUDGET_NONDETERMINISTIC`; an enabled budget is an upper bound and NuSMV explores every modeled selection within it |
| `attackEffects` | Empty when attack modeling is off. When enabled, contains only effects that this scene can exercise: `DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN` when at least one device has such a declaration, and the two deterministic command-drop effects when at least one submitted automation link/target exists. It is not a fixed capability list. |
| `modeledDeviceAttackPointCount` | Distinct device instances whose compromise can change this model: the union of devices with a falsifiable reading and devices that receive a rule command |
| `modeledFalsifiableReadingDeviceCount` | Subset of the preceding count whose declared readings may be replaced nondeterministically within their domains; this is not added again to the total |
| `modeledAutomationLinkAttackPointCount` | Logical rule command-delivery points in the submitted model: one per submitted rule, not one per canvas trigger edge or physical network segment |
| `modeledAttackPointCount` | `modeledDeviceAttackPointCount + modeledAutomationLinkAttackPointCount` |
| `trustPropagationPolicy` | `TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED`; under MEDIC's retained-control interpretation, one trusted contributing trigger source keeps the target event trusted, and the target becomes untrusted only when all contributing trigger sources are untrusted |
| `privacyPropagationPolicy` | `TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE` or `NOT_MODELED`; the optional content item selected on a rule command contributes its template sensitivity label in addition to trigger sources |
| `labelPropagationScope` | `AUTOMATION_RULE_COMMANDS_ONLY`; trust/privacy reset assignments are attached to synchronized automation-rule commands. Template-internal Transitions, WorkingState Dynamics, and natural evolution change modeled values/states without copying a trigger label into the result. Attack falsification may still force a declared reading's trust to `untrusted`. |
| `environmentEvolutionEffects` | Always contains `DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN` and `DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN`; shared numeric values use declared natural rates and device effects, while shared enum/boolean values may otherwise choose any value in their declared domain on each model step |
| `localVariableFallbackPolicy` | `STUTTER_WHEN_NO_DECLARED_EVOLUTION`; a device-local value retains its current value unless a declared Transition assignment, WorkingState Dynamic, natural rate, or enabled attack effect changes it |

`DECLARED_FALSIFIABLE...` applies only to template variables whose required
`FalsifiableWhenCompromised` flag is `true`, whether shared or device-local. The model
does not infer sensor behavior from API presence and does not widen declared domains.
An attack-enabled request with no applicable reading or automation link is rejected with
`422` instead of returning a run indistinguishable from attack mode off. Behaviorally
inert device instances are not generated as compromise choices and do not consume the
budget; the returned point counts therefore describe the effective attack surface, not
the raw number of canvas devices.

### `ModelRunSnapshotDto`

This object identifies the model population actually accepted for a verification or
simulation run. It is returned by synchronous results, newly submitted and queried
tasks, task summaries, and persisted trace detail/summary DTOs.

| Field | Type | Meaning |
| :--- | :--- | :--- |
| `capturedAt` | `LocalDateTime` | Time the referenced manifests were resolved at the model boundary |
| `deviceCount` | `int` | Device instances in the normalized model input |
| `ruleCount` | `int` | Submitted automation rules, including any later reported as generation-disabled |
| `specificationCount` | `int` | Submitted specifications; always `0` for simulation |
| `environmentVariableCount` | `int` | Effective board environment entries after required defaults were merged |
| `deviceTemplateCount` | `int` | Distinct referenced template manifests captured for the run |
| `templatesFrozen` | `boolean` | Always `true`; generation reused the captured manifests and did not reload mutable definitions |

`modelSnapshot` is scope metadata, not a claim that the current Board still matches.
The Board compares current modelable input with an in-memory submission signature only
for runs submitted in the same browser tab. It labels changed input explicitly; after a
reload or when opening historical results, it says the current Board was not compared
and limits the conclusion to this snapshot.

### Other verification endpoints

- `GET /api/verify/tasks/{id}/progress` → `Integer` (0–100)
- `POST /api/verify/tasks/{id}/cancel` → `TaskCancellationResultDto`
- `DELETE /api/verify/tasks/{id}` → dismiss a failed/cancelled task with no result
- `GET /api/verify/runs` → `VerificationRunSummaryDto[]`
- `GET /api/verify/runs/{id}` → `VerificationRunDto`
- `GET /api/verify/runs/{id}/traces` → `TraceDto[]`
- `DELETE /api/verify/runs/{id}` → atomically delete the run and its counterexamples
- `GET /api/verify/traces` → `TraceDto[]`
- `GET /api/verify/traces/{id}` → `TraceDto`
- `DELETE /api/verify/traces/{id}` → `null` (404 `ResourceNotFoundException` if absent)

### `TaskCancellationResultDto`

Used by both verification and simulation cancellation endpoints. An HTTP 200 means the
request was evaluated, not that cancellation won the race.

| Field | Type | Notes |
| :--- | :--- | :--- |
| `taskId` | `Long` | The task named in the request |
| `cancellationAccepted` | `Boolean` | `true` only when an active task was atomically changed to `CANCELLED` |
| `cancellationOutcome` | `ACCEPTED \| ALREADY_CANCELLED \| ALREADY_COMPLETED \| ALREADY_FAILED \| NO_LONGER_CANCELLABLE` | User-facing result of the attempt |
| `taskStatus` | `PENDING \| RUNNING \| COMPLETED \| FAILED \| CANCELLED` | Authoritative status after the attempt |
| `executionMayStillBeStopping` | `Boolean` | The persisted status is already `CANCELLED`, but queued or running work may still exist locally or on another backend instance; `false` is returned only when this instance definitively removed the queued execution before it started |

Clients must branch on `cancellationOutcome`; they must not turn every HTTP 200 into
"cancelled successfully". The frontend also verifies that the returned `taskId`,
outcome, accepted flag, and status agree before updating the task UI.

---

## 2. Nested request DTOs

### `DeviceVerificationDto`

| Field | Type | Required | Notes |
| :--- | :--- | :--- | :--- |
| `varName` | `String` | yes | Instance identifier used as the SMV variable name |
| `templateName` | `String` | yes | Resolved from the user's template table by `userId + templateName` |
| `state` | `String` | no | Current state |
| `currentStateTrust` | `String` | no | Device-level trust override (`trusted` / `untrusted`) |
| `variables` | `VariableStateDto[]` | no | `{ name, value, trust }`; `name` must be a template `InternalVariable.Name` |
| `privacies` | `PrivacyStateDto[]` | no | Device-local variable sensitivity overrides as `{ name, privacy }` |

For templates with `Modes`, `state` initializes the mode state machine and
`currentStateTrust` is an explicit trust override for the current state. If it is omitted,
the model uses the selected `WorkingStates.Trust`. No-mode devices should omit both
fields; their model behavior comes from device-local `variables` and `privacies`.

`DeviceVerificationDto.variables` and `.privacies` may contain only device-local
template variables (`InternalVariables[].IsInside=true`). Current-state sensitivity is
expressed by `currentStatePrivacy`; clients never author generated state-property keys.
Environment variables (`IsInside=false`) are rejected in these fields; they
are supplied through the top-level `environmentVariables` pool.

### `BoardEnvironmentVariableDto`

| Field | Type | Required | Notes |
| :--- | :--- | :--- | :--- |
| `name` | `String` | yes | Shared environment variable name exactly as declared in the template. Do not add or strip NuSMV's generated `a_` prefix; a real variable named `a_temperature` is valid and generates `a_a_temperature` in SMV |
| `value` | `String` | yes when the template declares enum/range | Initial value for NuSMV `a_<name>` |
| `trust` | `String` | no | `trusted` / `untrusted`; omission inherits the template's required explicit shared-environment `Trust`; an explicit blank/invalid value is rejected before merging |
| `privacy` | `String` | no | `public` / `private`; omission inherits the template's required explicit shared-environment `Privacy`; an explicit blank/invalid value is rejected before merging |

Before verification, simulation, or fix generation, the backend collects environment
variables required by the submitted devices' templates, merges missing values from
defaults (`Values[0]` for enums, `LowerBound` for bounded numeric variables), validates
the pool, and passes that shared pool to NuSMV generation as the authoritative source for
`init(a_<name>)`, where `<name>` is the literal template variable name. Devices whose templates declare an environment `InternalVariable`
receive a read mirror such as
`sensor_1.temperature := a_temperature`; devices that only list the name in
`ImpactedVariables` can change `a_temperature` but cannot be used as the rule/spec
source for that variable. Rules/specs still use a device prefix such as
`sensor_1.temperature`; the prefix is a permission check and identity anchor, while the
actual value comes from this pool.

An impact-only template must carry its own `EnvironmentDomains` entry; another installed
or submitted device template cannot silently supply it. Only submitted device instances
contribute semantics. Declarations of the same shared name must agree on literal casing,
domain/enum order, natural change rate, default trust, and default privacy or the request
is rejected before NuSMV execution.

When these fields originate from the saved board, `POST /api/board/nodes` has already
validated the same runtime semantics against the selected template: legal current
state, legal device-local variable override names and values, `trusted|untrusted`
trust values, and `public|private` privacy values. `/api/board/environment` has already
validated the environment pool. Verification/simulation still revalidate the
model-boundary request because AI tools, scripts, and service callers can construct
requests without passing through board storage.

### `RuleDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `Long` | Null for unsaved rules |
| `conditions` | `Condition[]` | `@NotEmpty` |
| `command` | `Command` | `@NotNull` |
| `ruleString` | `String` | Human-readable form |
| `createdAt` | `LocalDateTime` | |

Rule ownership is derived from authentication. The internal `userId` field is
`@JsonIgnore` and is neither accepted as caller authority nor serialized to clients.

`Condition`: `{ deviceName (req), attribute (req), targetType (req), relation?, value? }`.
`deviceName` carries the canonical device id / NuSMV varName, not a display label.
`targetType` is required (`api | variable | mode | state`) and drives NuSMV condition
generation; the backend does not infer semantics from `attribute`. `relation` must be
one of `=`, `!=`, `>`, `>=`, `<`, `<=`, `in`, `not_in`, or `not in` when present;
aliases `EQ`, `NEQ`, `GT`, `GTE`, `LT`, `LTE`, `IN`, `NOT_IN`, and `NOT IN` are accepted
and normalized before storage/model generation. `value` is required whenever `relation`
is present.
For rule conditions, `targetType=api` is a boolean event-signal source: `attribute`
must name a template API with `Signal=true`, and both `relation` and `value` must be
omitted. Value-based conditions (`variable`, `mode`, `state`) require both
`relation` and `value`. `targetType=mode` and `targetType=state` are enum conditions,
so they support only `=`, `!=`, `in`, and `not in`; numeric `targetType=variable`
conditions support those operators and additionally support ordering comparisons.
Rules use current-step IF semantics: conditions are evaluated against the source
device values visible in the current NuSMV state, and the command changes the target
device in the next state. Verification specs and parsed traces use that same
current-step condition model.
`Command`: `{ deviceName (req), action (req), contentDevice?, content? }` — the last
two carry privacy-rule content. `action` names a template API command; commands may use
any API, not only signal APIs.

### `SpecificationDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `id` | `String` | `@NotBlank`, ≤100 chars |
| `templateId` | `String` | `@NotBlank`, `@Pattern("^[1-7]$")`; `"6"` → LTLSPEC, `"1"`–`"5"`/`"7"` → CTLSPEC. Unknown ids are rejected at the DTO boundary and fail closed during generation |
| `templateLabel` | `String` | `@NotBlank`, ≤255 chars |
| `formula` | `String` | Optional display formula preview/cache persisted with board specs; ignored for verification semantics |
| `devices` | `DeviceRefDto[]` | Selected-device metadata (`@NotNull`, max 50); persisted as JSON only when saved through board storage |
| `aConditions` | `SpecConditionDto[]` | `@NotNull`; serialized as `aConditions` |
| `ifConditions` | `SpecConditionDto[]` | `@NotNull` |
| `thenConditions` | `SpecConditionDto[]` | `@NotNull` |

`SpecConditionDto`:

| Field | Rules |
| :--- | :--- |
| `id` | Optional client-side identifier |
| `side` | Optional; when present must be `a`, `if`, or `then` and match the containing collection |
| `deviceId` | **Required** model device varName, matching one `devices[].varName` |
| `deviceLabel` | Optional display snapshot. Ignored for validation/resolution |
| `targetType` | **Required**; `state`, `mode`, `variable`, `api`, `trust`, or `privacy` |
| `key` | **Required** |
| `propertyScope` | Required only for `trust`/`privacy`: `state` means the active state in the mode named by `key`; `variable` means the literal template variable named by `key`. Generated `Mode_state` names are invalid |
| `relation` | **Required**; same enum as rule conditions |
| `value` | **Required**; API conditions may be authored without a value in UI/AI helpers and are normalized to `TRUE` before this API boundary |

`side` is derived from the containing collection on save/read and, when supplied by a
client, must match that collection.
`formula` is never parsed by verification. The backend rebuilds every CTL/LTL property
from `templateId` and the structured condition arrays, so clients must keep
`aConditions`, `ifConditions`, and `thenConditions` complete even when a preview string
is present. Controlled UI/AI/scene-import paths regenerate `formula` and `devices[]`
from those conditions instead of trusting imported/generated cache text.
User-facing UI should label `formula` as a formula preview/cache. Verification result
UIs use the run-captured `SpecResultDto.formulaPreview` in the ordinary result row and
label `SpecResultDto.expression` as the actual checked expression in technical details.
They must not resolve `specId` against the current Board to reconstruct a historical or
asynchronous result: the current specification may have changed while the run was active.
Template shape is strict: `templateId` `1`, `2`, `3`, and `7` require non-empty
`aConditions` and empty `ifConditions`/`thenConditions`; `templateId` `4`, `5`, and
`6` require non-empty `ifConditions` and `thenConditions` and empty `aConditions`.
`DeviceRefDto`: `{ deviceId, deviceLabel, selectedApis: String[] }`; `deviceId` is
required and is also the model device varName at this API boundary. `deviceLabel` is
display-only. The `devices` collection is recursively validated: null device entries,
missing ids, a null `selectedApis` collection, and null API-name entries are rejected
instead of being accepted as incomplete display bindings.

- `targetType` ∈ `state | mode | variable | api | trust | privacy` (backend `@Pattern`,
  case-insensitive). For `trust`/`privacy`, `value` must be a legal enum —
  `trusted|untrusted` and `public|private` respectively (the SMV variable domains); an
  arbitrary string is rejected before generation.
- For specification conditions, `targetType=api` checks a generated boolean API signal
  variable. `key` must name a template API with `Signal=true`; relation is limited to
  `=`, `!=`, `IN`, or `NOT_IN`; values must be `TRUE`/`FALSE` (or a boolean list for
  `IN`/`NOT_IN`). Frontend and AI authoring helpers may omit relation/value for an API
  condition; they normalize the model request to `= TRUE`.
- `targetType=state` checks the full device state tuple. `targetType=mode` checks one
  concrete mode variable named by `key` (for example `ThermostatMode`) against a legal
  value from that mode. With `IN`/`NOT_IN`, ordinary enum-like values may be separated
  by comma, semicolon, or pipe; multi-mode `state` tuples reserve semicolon for the tuple
  itself, so tuple sets must use comma or pipe (`home;idle,sleep;idle`).
- `targetType=variable` checks a template device-local or environment variable declared
  by the referenced device. `key` is the literal template variable name; it is not a
  shorthand for the generated SMV name. For example, a template variable named
  `temperature` uses `key: "temperature"` and generates `a_temperature`, while a real
  template variable named `a_temperature` uses `key: "a_temperature"` and generates
  `a_a_temperature`. For environment variables, the device prefix authorizes the read,
  and the value/trust/privacy come from the top-level environment pool. Enum variable
  values must be one of the template `Values`; numeric variables with bounds must
  receive integer values inside `LowerBound..UpperBound`.
- `targetType=trust` and `targetType=privacy` also use literal property keys. Do not
  submit generated names as aliases: `key: "trust_temperature"` means the real property
  key is `trust_temperature`, so the generated SMV variable is
  `device.trust_trust_temperature`. If the template only declares `temperature`, use
  `key: "temperature"`.
- Device references are resolved from canonical ids only. Labels and template names are
  display metadata, not fallback identity. See
  [../architecture/device-identity.md](../architecture/device-identity.md) and
  [../architecture/nusmv-model.md](../architecture/nusmv-model.md#template-resolution-important).

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
| `id` / `verificationTaskId` | `Long` | Trace identity and owning completed verification-run identity; only pre-refactor orphan traces may lack the latter. Ownership is enforced server-side and `userId` is not serialized |
| `violatedSpecId` | `String` | |
| `violatedSpec` | `SpecificationDto` | Structured verification-time specification snapshot used for user-facing labels and conditions |
| `checkedExpression` | `String` | Exact generated CTL/LTL expression checked by NuSMV; distinct from `violatedSpec.formula`, which is only a preview/cache |
| `states` | `TraceStateDto[]` | Ordered counterexample states |
| `modelComplete` | `Boolean` | Whether the verification that produced this trace used the complete generated model |
| `disabledRuleCount` / `skippedSpecCount` | `Integer` | Generation omissions inherited from the source verification |
| `generationIssues` | `ModelGenerationIssueDto[]` | Item-level names and reasons for those inherited omissions |
| `isAttack` | `Boolean` | Attack mode persisted with this trace |
| `attackBudget` | `Integer` | Maximum compromised behavior-changing device-instance or automation-link point count persisted with this trace |
| `enablePrivacy` | `Boolean` | Privacy-modeling flag persisted with this trace |
| `modelSemantics` | `ModelSemanticsDto` | Structured assumptions rebuilt from the persisted effective attack-surface counts and run flags, not from raw request collection lengths |
| `modelSnapshot` | `ModelRunSnapshotDto` | Frozen verification-time item/template counts; this does not assert equality with the current Board |
| `createdAt` | `LocalDateTime` | |

> The internal trace DTO also carries `requestJson`, exact `templateSnapshotsJson`,
> `violatedSpecJson`, and `userId`,
> but they are `@JsonIgnore` — **not serialized to clients**. The raw fields restore
> server-side fix context. Automatic fix replays the exact saved manifests rather than
> whichever template versions happen to be current. `TraceMapper` instead returns structured `violatedSpec` and
> `isAttack` / `attackBudget` / `enablePrivacy` / `modelSemantics`, so clients do not parse persistence JSON.
> A non-attack request and historical snapshot use `attackBudget=0`. A positive budget
> with `isAttack=false` is rejected before model generation rather than normalized away.
> Records without all dedicated run-context columns, including the falsifiable-reading
> subset count, return no `modelSemantics`; the mapper
> does not guess a denominator from `devices.length`, which could reintroduce inert points.

`TraceStateDto`: `{ stateIndex, devices: TraceDeviceDto[],
triggeredRules: TraceTriggeredRuleDto[], compromisedAutomationLinks: TraceTriggeredRuleDto[],
trustPrivacies: TraceTrustPrivacyDto[], envVariables: TraceVariableDto[],
globalVariables: TraceVariableDto[] }`.
`envVariables[].name` uses the literal board/template name. Generated NuSMV aliases are
not part of this API boundary: `a_temperature` in SMV is serialized as `temperature`,
while a real variable named `a_temperature` is serialized as `a_temperature`.
`globalVariables[]` contains runtime model values that are not part of the user's
environment pool. The internal attack counter is exposed as the user-facing
`compromisedPointCount`; its generated NuSMV name is not serialized. A user environment
variable cannot overwrite this separate namespace.

`TraceTriggeredRuleDto` is `{ ruleId, ruleLabel }`; internal generated probe indexes are
resolved by the parser and are not serialized. A triggered rule is a selected model
branch whose command-delivery guards passed and whose command produced the transition
into this state; it is not merely a condition that looked true in the frontend.
`compromisedAutomationLinks` uses the
same stable rule snapshot shape, so users see the affected automation rather than an
internal link index.

`TraceDeviceDto`: `{ deviceId, deviceLabel, templateName, state, mode, compromised,
variables: TraceVariableDto[], trustPrivacy[], privacies[] }`. `deviceId` is the
model-boundary identity; user-facing trace and simulation UIs should display
`deviceLabel` when it is present and keep `deviceId` in technical/debug details.
`compromised` is the user-facing boolean translated from NuSMV's internal attack flag;
the internal `is_attack` variable is not mixed into `variables[]`.
`TraceVariableDto`: `{ name, value, trust }`.
`TraceTrustPrivacyDto`: `{ name, propertyScope ('state'|'variable'|'content'),
mode?, trust? (Boolean), privacy? ('private'|'public') }`. For a state property, `name`
is the literal state and `mode` is its literal mode. Generated `Mode_state`, `trust_*`,
and `privacy_*` identifiers are parser-only details and are never serialized.

---

## 4. Simulation

### `POST /api/simulate` — synchronous (not persisted)

**Request body**: `SimulationRequestDto` — same as `VerificationRequestDto` but with
**no `specs`** field and an added `steps`:

The same strict unknown-field, scalar-type, duplicate-environment, and explicit-blank
validation applies. A misspelled attack/privacy option is an HTTP `400`, not a simulation
with that option silently disabled.

| Field | Type | Required | Default | Notes |
| :--- | :--- | :--- | :--- | :--- |
| `devices` | `DeviceVerificationDto[]` | yes (`@NotEmpty`) | — | |
| `environmentVariables` | `BoardEnvironmentVariableDto[]` | no | `[]` | Same unique-name, omitted/null-default, and explicit-blank rejection contract as verification |
| `rules` | `RuleDto[]` | no | `[]` | |
| `steps` | `int` (1–100) | no | `10` | Number of simulation steps |
| `isAttack` | `boolean` | no | `false` | Same no-applicable-attack-surface rejection as verification |
| `attackBudget` | `int` | no | `0` | Maximum compromised behavior-changing device-instance or automation-link points in the generated trajectory branch. It must be `0` when disabled; a positive disabled value is rejected. When enabled it must be explicitly supplied as `1..50` and no greater than the effective attack-surface count described above. |
| `enablePrivacy` | `boolean` | no | `false` | |

**Response**: `SimulationResultDto` — `{ isAttack, attackBudget, enablePrivacy,
modelSemantics, modelSnapshot, modelComplete, disabledRuleCount,
generationIssues: ModelGenerationIssueDto[], states: TraceStateDto[], steps,
requestedSteps, nusmvOutput, logs: String[], historyPersistence }`.

Plain `POST /api/simulate` is a preview and returns
`historyPersistence.status=NOT_REQUESTED`; no history row is expected.

`modelComplete=false` means one or more submitted rules were disabled fail-closed while
generating the model. The returned states are still model states, but they do not
represent the complete submitted board. Simulation is model exploration, not a
prediction of physical-home behavior.

The frontend validates synchronous, saved, and asynchronously loaded simulation
responses before opening the timeline. `modelComplete`, omission counts and itemized
issues, run-context `modelSemantics`, non-empty states, and `steps = states.length - 1`
are required. Persisted summaries also require explicit attack/privacy context. Missing
fields therefore cannot be interpreted as a complete model or a playable successful
trajectory.

Synchronous simulation uses the same request snapshot and runtime validation as async
simulation. Validation failures are returned as errors (REST 400 for DTO Bean Validation
or 422 for service `ValidationException`), not as a success-shaped empty simulation
result. Timeout, interruption, execution failure, or a run with no parsed states also
returns an error rather than an empty success DTO. `SimulationExecutionException` uses
HTTP 504/503/500 and error `data` shaped as `{ reasonCode, logs }`, where `reasonCode`
is `TIMED_OUT`, `INTERRUPTED`, `NO_TRACE_STATES`, or `EXECUTION_FAILED`.

### `POST /api/simulate/async`

**Response `data`**: the newly created `SimulationTaskDto`. Its server-generated `id`
is used for polling, while `status`, `progress`, `requestedSteps`, `modelSemantics`, and
`modelSnapshot` are the authoritative accepted-task context. HTTP success means the task
was accepted, not that a trajectory already exists.

Async simulation submission follows the same lifecycle contract as async verification:
the backend snapshots and validates the request and captures referenced template
manifests before task creation. The queued worker reuses those manifests rather than
reloading mutable templates. REST calls first
run full DTO Bean Validation; service and AI-tool callers run NuSMV runtime validation
for required devices, null list items, device identity, `steps`, `attackBudget`, and
current-template rule semantics.
Structurally invalid rules are rejected at the boundary: null rule elements, null
commands, and blank `command.deviceName` / `command.action` all return validation
errors instead of silently disappearing from the model. Known semantic mismatches
such as non-signal API conditions, unknown target actions, unknown content keys, and
illegal state/mode values return `ValidationException` (422) before task creation.
Rules that pass request validation but still cannot be emitted by NuSMV generation may
be disabled fail-closed with warnings in `checkLogs`. Validation failure returns no
`taskId`, and queue saturation marks the
created task `FAILED` before returning `503`. Clients should start polling only after
this endpoint successfully returns a task id.

As with verification, `progress=100` is written only together with the completed task
and its saved simulation trace. A failed completion write is not exposed as a completed
100% task.

### `GET /api/simulate/tasks` — simulation task status layer

Optional query parameter: `excludeTaskIds=1,2,3`. Use it when the frontend is already
polling specific task ids through `GET /api/simulate/tasks/{id}` and wants the inbox
summary refresh to skip those same tasks.

**Response**: `SimulationTaskSummaryDto[]`, ordered by `createdAt` descending.

This list excludes `COMPLETED` tasks. It contains active work plus failed/cancelled
tasks that produced no saved result. Active rows expose progress and frozen run
context; unsuccessful terminal rows expose a technical `errorMessage`, which clients
place behind an advanced disclosure rather than using as the primary localized status.
Completed simulations are
listed once through `GET /api/simulate/traces`, where the persisted trajectory is the
user-facing run result.

`DELETE /api/simulate/tasks/{id}` dismisses a failed or cancelled task. Active tasks
must be cancelled first. Completed simulation results must be deleted through their
persisted-run endpoint.

### `GET /api/simulate/tasks/{id}` — `SimulationTaskDto`

`{ id, status, createdAt, startedAt, completedAt, processingTimeMs, isAttack,
attackBudget, enablePrivacy, modelSemantics, modelSnapshot, requestedSteps, steps, modelComplete,
disabledRuleCount, generationIssues, simulationTraceId, checkLogs: String[],
errorMessage, progress }`.

Completed async simulations store the full states, execution logs, request JSON, and
raw NuSMV output in the referenced `SimulationTraceDto`; the task DTO stays a polling
summary.

### Persisted simulations

- `POST /api/simulate/traces` → `SimulationTraceDto` `{ id?, requestedSteps, steps,
  modelComplete, disabledRuleCount, generationIssues, states, logs, nusmvOutput,
  isAttack, attackBudget, enablePrivacy, modelSemantics, modelSnapshot, createdAt,
  historyPersistence }`
- `GET /api/simulate/traces` → `SimulationTraceSummaryDto[]` `{ id, requestedSteps,
  steps, modelComplete, disabledRuleCount, generationIssues, isAttack, attackBudget,
  enablePrivacy, modelSnapshot, createdAt, dataAvailable,
  unavailableReasonCode? }` (summary, no states)
- `GET /api/simulate/traces/{id}` → `SimulationTraceDto` (full states)
- `DELETE /api/simulate/traces/{id}` → `null`; also removes any completed background
  task row that only referenced this persisted result, preventing a stale task pointer
- `GET /api/simulate/tasks/{id}/progress` → `Integer`
- `POST /api/simulate/tasks/{id}/cancel` → `TaskCancellationResultDto` (same
  evaluated-attempt semantics documented above)
- `DELETE /api/simulate/tasks/{id}` → dismiss a failed/cancelled task with no result

Persisted simulation `requestJson` is the validated execution snapshot used for the
NuSMV run, not a later serialization of the caller's mutable request object. Exact
`templateSnapshotsJson`, `requestJson`, and `userId` remain server-internal; REST clients receive structured execution-context
fields instead. Effective device/link attack-point counts are persisted in dedicated
columns, so reopening a trace does not recount raw devices and change the budget meaning.

The save endpoint returns the generated trajectory even if history persistence fails.
`historyPersistence.status=SAVED` supplies its id. `OUTCOME_UNKNOWN` omits the id and
requires a history refresh before the UI says whether the trace was saved; the states
remain valid for immediate animation. A known `FAILED` status means no row was created.
History list conversion isolates malformed rows as `dataAvailable=false`; it never
silently replaces malformed semantic JSON with empty states/logs/default context.

---

## 5. Auto-fix

For the algorithm (strategies, forward verification), see
[../architecture/auto-fix.md](../architecture/auto-fix.md). This
section is the API contract only.

### `GET /api/verify/traces/{id}/fault-rules` — fault localization

Fast, no NuSMV invocation. **Response**: `FaultLocalizationResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `traceId` | `Long` | Trace being analyzed |
| `violatedSpecId` | `String` | User-facing specification reference from the trace |
| `sourceModelComplete` | `boolean` | `true` only when the saved source verification explicitly recorded a complete generated model; missing metadata fails closed as `false` |
| `sourceDisabledRuleCount` / `sourceSkippedSpecCount` | `int` | Source-verification omission counts |
| `sourceGenerationIssues` | `ModelGenerationIssueDto[]` | Itemized `{ issueType, itemLabel, reasonCode, reason }` explanations copied from the source verification |
| `faultRules` | `FaultRuleDto[]` | Automation rules observed in counterexample transitions |
| `summary` | `String` | Interpretation that distinguishes transition involvement from proven independent causation |
| `warnings` | `String[]` | Source-completeness limitations that the UI must present |

`FaultRuleDto` entries have the following user-facing fields:

| Field | Type | Notes |
| :--- | :--- | :--- |
| `ruleString` | `String` | |
| `transitionNumber` | `int` | One-based counterexample transition where the rule fired |
| `targetDeviceLabel` | `String` | User-facing target device label |
| `targetActionLabel` | `String` | User-facing target action label |
| `conflicting` | `boolean` | |
| `conflictingRuleString` | `String` | Readable conflicting rule when `conflicting=true` |
| `targetEndState` / `conflictingEndState` | `String` | Conflicting target outcomes when available |
| `reasonCode` | `String` | `TRIGGERED` or `CONFLICTING_END_STATES`; clients localize from this code |
| `reason` | `String` | Backend-readable fallback explanation |

Trace-snapshot rule positions and database ids stay server-internal. Clients identify a
localized rule through its readable `ruleString`, target, and trigger context; they do
not submit or operate on zero-based indices.

Fault localization is evidence for review, not a causal proof: a listed automation was
involved in a counterexample transition, but may not independently cause the violation.
An empty list can mean the violating path arose from device or environment evolution.
Clients must show `summary`, `warnings`, and `sourceGenerationIssues`; they must not turn
the endpoint name or a non-empty list into a claim that the root cause was proven.

`TraceStateDto.triggeredRules[]` and `compromisedAutomationLinks[]` contain readable
`{ ruleId, ruleLabel }` snapshots. `ruleId` is present only when the submitted model rule
carried a persisted id; clients use it to correlate a saved run with the current canvas
without exposing rule-list indexes. `ruleLabel` remains available when the current rule
was later removed.

### `POST /api/verify/traces/{id}/fix` — fix suggestions

May invoke NuSMV multiple times (bounded by `FIX_TIMEOUT_MS`, see
[configuration.md](../getting-started/configuration.md)). A URL-safe `requestId` query parameter
is required so the client can cancel this exact search through
`DELETE /api/verify/fix-requests/{requestId}`.

**Request body**: `FixRequestDto` — optional; omit or send `null` for defaults.

| Field | Type | Default | Notes |
| :--- | :--- | :--- | :--- |
| `strategies` | `String[]` | `["parameter","condition","remove"]` when omitted | Exact, non-empty, duplicate-free strategy order when supplied. Values are limited to `parameter`, `condition`, and `remove`. An explicit empty/invalid list is rejected rather than replaced by defaults. `remove` permanently deletes suggested automation rules; it is not a reversible enable/disable toggle |
| `preferredRangeSelections` | `PreferredRangeSelection[]` | `null` | Optional ranges selected from concrete parameter-adjustment targets returned in `ParameterAdjustment.targetId`. Each item is `{ targetId, lower, upper }`; all fields are required, `targetId` is an opaque trace-scoped selector copied from a returned adjustment, `lower`/`upper` are integers, and `lower <= upper` |

Clients should build `preferredRangeSelections` from selectable `ParameterAdjustment`
targets and display the fault rule text, condition context, attribute, and relation.
No rule/condition locator map is part of either public request DTO. As with other REST
requests, any extra field is rejected by strict JSON parsing instead of being silently
ignored. Defaults apply only when `strategies` is omitted (or the optional request body is
omitted), never when the caller explicitly supplies an empty or malformed selection.

**Response**: `FixResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `traceId` | `Long` | |
| `violatedSpecId` | `String` | |
| `faultRules` | `FaultRuleDto[]` | Same schema as fault localization |
| `suggestions` | `FixSuggestionDto[]` | Advisory proposals that passed every submitted specification in the complete formal model used for the fix attempt. Each verified suggestion includes a short-lived `suggestionToken` binding the exact visible proposal to this user, trace, strategy, and preferred ranges |
| `strategyAttempts` | `FixStrategyAttemptDto[]` | One entry per requested strategy, including skipped/failed attempts and a user-readable reason |
| `fixable` | `boolean` | Whether at least one complete-model, forward-verified suggestion was found; not whether repair was merely attempted |
| `sourceModelComplete` | `Boolean` | Whether the counterexample source verification used a complete model |
| `sourceDisabledRuleCount` / `sourceSkippedSpecCount` | `Integer` | Source-verification generation omissions |
| `sourceGenerationIssues` | `ModelGenerationIssueDto[]` | Itemized `{ issueType, itemLabel, reasonCode, reason }` explanations from the source verification |
| `templateSnapshotComparison` | `NOT_CHECKED \| UNCHANGED \| CHANGED \| UNAVAILABLE` | Structured comparison between current device templates and the frozen run snapshot; clients localize drift/unavailable limitations from this field |
| `summary` | `String` | Overall result summary |
| `warnings` | `String[]` | English technical diagnostics for logs/advanced details; ordinary UI derives localized limitations from source-completeness fields, `templateSnapshotComparison`, generation issues, and strategy-attempt statuses |
| `unusedPreferredRangeSelections` | `PreferredRangeSelection[]` | Preferred range selections that matched no parameter-adjustment target |

`FixStrategyAttemptDto` is `{ strategy, status, reason }`. Status is one of
`VERIFIED`, `NOT_VERIFIED`, `NO_VERIFIED_SUGGESTION`, `TIMED_OUT`, `SKIPPED_TIMEOUT`,
`SKIPPED_NO_SPEC`, `SKIPPED_NO_FAULT_RULES`, `SKIPPED_UNSUPPORTED`, or
`SKIPPED_INCOMPLETE_SOURCE_MODEL`. This distinguishes "no verified repair was found"
from "the strategy started but did not finish" (`TIMED_OUT`) and "the strategy was
not run" (`SKIPPED_*`).

`FixSuggestionDto`: `{ suggestionToken, strategy, description, parameterAdjustments[],
conditionAdjustments[], removedRuleDescriptions: String[], verified }`.
All collection fields in `FixResultDto` and `FixSuggestionDto` are always serialized as
JSON arrays. A collection that does not apply to the selected strategy is `[]`, never
`null`, so clients can distinguish "no such changes" from a malformed response.
`ParameterAdjustment`: `{ targetId, attribute, relation, originalValue, newValue,
lowerBound, upperBound, description }`.
`ConditionAdjustment`: `{ action, attribute, targetType, description, deviceName,
relation, value }`.
`targetId` is the opaque API-facing selector for preferred ranges within the same
trace/fix context. Clients should copy it from a returned `ParameterAdjustment`, not generate it.
If a copied target is not available during generation, the response reports it in
`unusedPreferredRangeSelections`. Rule/condition positions remain server-side
trace-snapshot locators for verification, drift checks, and patching; they are not part of
the REST or AI response contract.

### `POST /api/verify/traces/{id}/fix/apply` — apply a fix suggestion

Applies the exact signed repair suggestion the user is viewing. The server verifies its
short-lived signature and saves that same proposal only when the complete current model snapshot
still matches the verification context.

**Request body**: `FixApplyRequestDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `strategy` | `String` | `parameter` / `condition` / `remove` |
| `suggestion` | `FixSuggestionDto` | Required exact suggestion returned by `/fix` |
| `suggestionToken` | `String` | Required opaque token copied from that suggestion |
| `preferredRangeSelections` | `PreferredRangeSelection[]` | Optional exact selections used for the preceding `/fix`; they are covered by the signature. Omit when generation used no selections |

**Safety** — the server does **not** trust the client:

- **Exact-suggestion signature.** The client submits the displayed proposal, but cannot alter it:
  the HMAC-protected token binds the user, trace, strategy, complete visible suggestion,
  preferred ranges, expiry, and hidden remove-rule positions. Tampering, expiry, or mixing a token
  with another trace/range rejects with `400`. Apply therefore cannot silently substitute a
  different newly searched proposal.
- **Complete-source-model guard.** A trace produced while any rule/specification was
  omitted cannot be used for automatic fix generation or apply. Suggestion generation
  returns explicit skipped strategy attempts; apply rejects with `400` and requires the
  user to resolve generation warnings and verify again. A saved trace with missing
  `modelComplete` metadata also fails closed: zero omission counts alone are not evidence
  that the source model was complete. Apply checks this before template reads or persistence.
- **Board-drift guard (rules).** The server's internal rule/condition positions are relative to the
  trace's verification-time rule snapshot. The server aligns that snapshot with the current board
  rules by index + **order-preserving** fingerprint (device varName, attribute, relation, value, plus
  command device/action and `contentDevice`/`content`) and rejects with `400` if the board drifted
  (rules added/removed/edited/reordered since verification), so a stale index never edits the wrong
  rule or condition. This check runs **inside the same per-user write lock + transaction** as the save
  (read → check → apply → write are one atomic critical section), so a concurrent save cannot slip in
  between the check and the write.
- **Frozen-template replay and drift guard.** Verification traces persist the exact
  referenced manifests internally. `/fix` builds its NuSMV model from that frozen set. Before
  apply, the server compares the current manifests'
  persisted JSON projection with the saved set and requires the same referenced-template
  keys. This avoids false drift from deserialization-only compatibility fields such as an
  omitted versus empty legacy API `Assignments` list, while a real modeled-field or
  template-set difference is **rejected with `400`** and requires re-verification. If the
  current repository cannot be read, equality is unknown rather than false: `/fix`
  returns an explicit warning and apply blocks with retryable `503`. It never reports an
  unavailable comparison as proven drift or silently omits the degradation.
- **Spec/device/environment-drift guard.** apply also rejects with `400` when the current board's
  specifications, environment pool, or device instance state (variables, privacies, initial state,
  trust) changed after the trace was recorded. Apply compares a canonical **semantic fingerprint**
  of the trace snapshot against the current
  board. It is *not* a raw-JSON equality check: both sides run through the same normalization (device
  names canonicalized, effective device-local variable/trust/privacy values and the board
  environment pool derived from the same manifests NuSMV uses, values de-quoted), so an
  untouched board matches its model-boundary normalized snapshot instead of misfiring.
  Environment variables participate as top-level pool values, including variables that
  are only affected by devices; missing required pool values are normalized to the same
  defaults used at verification time. Omitted internal
  enum/numeric variables use the generator's effective defaults. This check runs
  **inside the same per-user write lock + transaction** as the save, so a concurrent spec/device edit
  cannot slip in between the check and the write. If the current board no longer builds a valid device
  model, the check **fails closed**, distinguishing the cause: a genuinely invalid/changed board
  (device removed, template deleted, manifest unparseable) rejects with `400` ("re-run verification"),
  while an infrastructure error that leaves drift *unconfirmable* (e.g. template repository unavailable)
  rejects with `503` ("retry later") rather than misattributing it to a board change.
  Verification flags (`isAttack`/`attackBudget`/`enablePrivacy`) are per-request and not persisted for
  re-proving, so re-run verification after changing them.

The server then applies the token-verified suggestion to a deep copy of the persisted rules. The
unchanged complete snapshot means the earlier NuSMV evidence still describes the model being
changed; apply does not repeat the expensive strategy search.

**Response**: `FixApplyResultDto`

| Field | Type | Notes |
| :--- | :--- | :--- |
| `applied` | `boolean` | `true` on success |
| `strategy` | `String` | The applied strategy |
| `verificationRechecked` | `boolean` | `false` for the public signed-suggestion flow because apply does not repeat the search; retained for internal compatibility paths that do recompute |
| `verificationEvidenceReused` | `boolean` | `true` for the public signed-suggestion flow: existing verification evidence was reused only after all rule/template/spec/device/environment drift checks passed atomically |
| `appliedSuggestion` | `FixSuggestionDto` | Server-trusted suggestion actually applied; user-facing descriptions are included while internal rule/condition positions remain hidden |
| `previousRuleCount` / `currentRuleCount` | `int` | Rule-set size before/after the atomic write; particularly important for the destructive `remove` strategy |
| `message` | `String` | English API summary for logs and non-localized callers; the frontend uses the structured fields above to render a localized, scope-qualified result instead of treating this text as an unconditional guarantee |
| `rules` | `RuleDto[]` | The full persisted rule list after applying. The frontend validates its count and directly replaces the Board rule collection from this authoritative snapshot; it refreshes separately only when the apply response itself is unconfirmed. |

Effect per strategy: `parameter` overwrites the target condition's value (and relation);
`condition` adds/removes conditions; `remove` permanently deletes the flagged rules. A condition fix
that would leave a rule with no trigger conditions is rejected. Positive condition candidates that
merely repeat the command target's declared API `EndState` are also rejected as postconditions: they
can make the original automation unreachable while producing a vacuous property pass. A candidate
that is provably false under the command API's concrete `StartState` is rejected for the same reason;
wildcard start-state segments are not treated as contradictions. During apply, NuSMV-normalized
device references are mapped back to the current raw board node ids; an unmappable reference fails
the transaction without writing a rule.

`/fix` is a synchronous, server-bounded operation. Every NuSMV call
inside the fix pipeline is capped by the smaller of `NUSMV_TIMEOUT_MS` and the remaining
`FIX_TIMEOUT_MS` budget, including the wait for NuSMV execution capacity. The Board shows the
selected strategy, validation phase, and elapsed time. Closing the suggestion view calls the
request-specific cancellation endpoint before aborting transport; the backend interrupts the
tracked search and purges cancelled queued work. `/fix/apply` performs no strategy search and
keeps the dialog open until a definitive write response; transport uncertainty still triggers
authoritative rule reconciliation.

### `GET /api/verify/tasks/{id}/traces` — traces for an accepted background run

Returns the `TraceDto[]` produced by a specific async verification task, scoped to the
current user. Used by the frontend to display counterexamples for the task that just
finished, rather than mixing in traces from earlier/concurrent runs.

History UIs use the equivalent run-oriented path
`GET /api/verify/runs/{id}/traces`; the task-oriented path exists for the polling flow
that already holds an accepted background task id.
