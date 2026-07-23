# Board Storage & Recommendation API

Field-level contract for `/api/board` — the persisted canvas (nodes, rules, specs,
layout), device templates, and AI-backed recommendation endpoints.

`GET /api/board/snapshot` returns `BoardSemanticSnapshotDto` with `nodes`,
`environmentVariables`, `rules`, `specifications`, and `deviceTemplates` captured under one
user/database lock and transaction. The frontend uses it for initial Board hydration so an
unloaded collection is never presented as an authoritative zero count. Layout remains separate
because it does not affect formal-model semantics.
The `Result<T>` envelope, auth, and error codes are defined in
[overview.md](overview.md).

All endpoints are authenticated and scoped to the current user (`@CurrentUser`).
Verified against code on 2026-07-23. Source:
`service/impl/BoardStorageServiceImpl.java`, `controller/BoardStorageController.java`,
`dto/device/`, `dto/board/`, `dto/rule/`, `dto/spec/`.

**Mutation semantics matter:** ordinary device, rule, and specification operations are
targeted commands. A client sends only the item it intends to create/update/delete; an
omitted item is not deleted. Each mutation is serialized under the user's board write
lock and returns both the affected item(s) and the authoritative post-mutation snapshot,
so a stale client can replace its local collection without issuing a hidden full-list save.

`POST /api/board/batch` is the only external full-scene replacement command. The Board
uses it only after an authoritative `GET /api/board/replacement-preview` and explicit
user confirmation for scene import or scene clear. All four semantic collections and the
exact template-snapshot dependency set are required complete desired collections; omitted
or `null` collections are rejected rather than interpreted as hidden partial preservation.
The replacement commits or rolls back as one transaction.

---

## Canvas storage

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/nodes` | → `DeviceNodeDto[]` | List device instances |
| POST | `/api/board/nodes` | `DeviceBatchCreateRequestDto` → `DeviceMutationResultDto` | Atomically append one or more device instances; every `templateName` must exist. Optional environment patches commit with the devices. |
| PUT | `/api/board/nodes/{nodeId}/layout` | `DeviceLayoutDto` → `DeviceUpdateResultDto` | Replace only the complete canvas layout subresource (`position`, `width`, `height`); device identity and modeled runtime are preserved |
| PUT | `/api/board/nodes/{nodeId}/runtime` | `DeviceRuntimeUpdateDto` → `DeviceUpdateResultDto` | Replace only the complete device-local modeled runtime subresource; identity, type, display name, and canvas layout are preserved |
| PATCH | `/api/board/nodes/{nodeId}/label` | `{ label, expectedLabel }` → `DeviceMutationResultDto` | Rename one instance and update specification display labels atomically; stable references remain `nodeId`. `expectedLabel` must equal the label originally edited or stale submission returns `409` without writing. |
| GET | `/api/board/nodes/{nodeId}/deletion-preview` | → `DeviceDeletionResultDto` | Read-only authoritative preview of the device, every referencing rule/spec, and each Environment Pool item that would be removed |
| POST | `/api/board/nodes/{nodeId}/delete` | `DeviceDeleteRequestDto` → `DeviceDeletionResultDto` | Delete one instance plus every previewed consequence atomically. The opaque `impactToken` from the latest preview must still match the complete server-calculated impact or the server returns `409` before writing. |
| GET | `/api/board/environment` | → `BoardEnvironmentVariableDto[]` | Board-level environment pool; self-heals from current nodes/templates |
| POST | `/api/board/environment` | `BoardEnvironmentVariableDto[]` → `EnvironmentMutationResultDto` | Atomically apply at most 200 non-null, name-keyed field patches to values/trust/privacy required by current devices; omitted/null fields retain their current values |
| GET | `/api/board/rules` | → `RuleDto[]` | List rules in effective execution order |
| POST | `/api/board/rules` | `RuleDto` → `CollectionMutationResultDto<RuleDto>` | Create exactly one validated rule; request `id` is ignored and the server assigns identity |
| PUT | `/api/board/rules/order` | `{ ruleIds: Long[] }` → `RuleDto[]` | Atomically replace execution order only. The request accepts at most 100 ids and must contain every current rule id exactly once; stale or partial lists return `409` without writing. |
| DELETE | `/api/board/rules/{ruleId}` | → `CollectionMutationResultDto<RuleDto>` | Delete exactly one rule or return `404` |
| GET | `/api/board/specs` | → `SpecificationDto[]` | List specs in stable authored order |
| POST | `/api/board/specs` | `SpecificationDto` → `CollectionMutationResultDto<SpecificationDto>` | Create exactly one validated specification |
| DELETE | `/api/board/specs/{specId}` | → `CollectionMutationResultDto<SpecificationDto>` | Delete exactly one specification or return `404` |
| GET | `/api/board/replacement-preview` | → `BoardReplacementPreviewDto` | Return the opaque impact token and authoritative current counts that must be shown before a full scene replacement/clear |
| POST | `/api/board/batch` | `BoardBatchDto` → `BoardBatchDto` | **Explicit atomic full-scene replacement** of complete `nodes` + `environmentVariables` + `rules` + `specs` plus exact `templateSnapshots`; requires the still-current preview `impactToken` |
| GET | `/api/board/layout` | → `BoardLayoutDto` | Panel/canvas layout |
| POST | `/api/board/layout` | `BoardLayoutDto` → `BoardLayoutDto` | |

The persisted Board has hard totals of 100 devices, 100 rules, 100 specifications, and
200 derived Environment Pool variables. Targeted creation locks the user row and checks
the authoritative current total plus the proposed addition in the same transaction; it
does not treat the per-request device limit as a reusable way around the Board total.
A device addition that would derive more than 200 Environment Pool variables also rolls
back. The Board UI blocks known over-capacity additions across dialogs, template drag/drop,
recommendation application, and scene import before sending them. It also enforces the
per-device override and per-rule/per-specification-group condition limits while authoring;
the backend remains authoritative for stale or concurrent clients. Legacy data
already above a limit is never truncated automatically: deletion remains available so the
user can reduce it to the supported range before creating more items, reordering rules,
running a complete model, or round-tripping a scene.

Initial layout hydration never overwrites zoom, pan, or panel changes made while the layout
request was in flight. If an early interaction occurred on a wide viewport, the client
persists the resulting current layout after hydration, then clears the one-shot protection
flags so later narrow/wide viewport restoration still works.

### `DeviceNodeDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `id` | `String` | Required |
| `templateName` | `String` | Required; must match an existing template name for the current user |
| `label` | `String` | Required |
| `position` | `{ x: Double, y: Double }` | Required |
| `state` | `String` | Required only when the selected template has a state machine (`Modes` plus non-empty `WorkingStates`); stateless/no-mode devices may omit it and are stored with the UI placeholder `Working` |
| `width` / `height` | `Integer` | Required; width is `80..2000`, height is `60..2000`; UI and AI creation paths default to `176` / `128` when the creator omits explicit dimensions |
| `currentStateTrust` | `String` | Optional only for templates with a state machine (`Modes` plus non-empty `WorkingStates`); `trusted` / `untrusted` |
| `currentStatePrivacy` | `String` | Optional only for templates with a state machine; `public` / `private`. This is the selected initial state's data-sensitivity label, not access control |
| `variables` | `VariableStateDto[]` | Optional; `{ name, value, trust? }` for device-local template variables (`InternalVariables[].IsInside=true`) only. `value` is the instance's initial value; omitted `trust` inherits the active template default and is omitted from responses rather than serialized as `null`, while an explicit value is an advanced instance override |
| `privacies` | `PrivacyStateDto[]` | Optional; `{ name, privacy }` for device-local variables or generated state privacy keys only |

> `DeviceNodeDto` is the canvas-CRUD shape (includes UI layout). The verification path
> uses the leaner `DeviceVerificationDto` — see
> [verification.md](verification.md).

Targeted device creation returns `initialStateSource`. Its values are `requested` for an
explicit runtime state, `templateDefault` for a state-machine `InitState`,
`statelessPlaceholder` for the non-semantic `Working` canvas placeholder on a no-mode
template, and `systemFallback` only for invalid legacy stateful data with no usable initial
state. Only the last case produces a warning; a valid stateless device is not presented as
an initialization failure.

`DeviceBatchCreateRequestDto` is `{ devices, environmentVariablePatches }`; `devices`
must contain 1–100 items, must keep the resulting Board at no more than 100 devices, and
`environmentVariablePatches` may contain at most 200.
`DeviceMutationResultDto` returns `operation`, `affectedDevices`,
`currentNodes`, `environmentVariables`, `environmentChanges`, `currentSpecifications`,
`previousLabel`, `updatedSpecificationCount`, and `currentCount`. Callers should use the
returned current collections rather than assuming their local optimistic state won.
`environmentChanges[]` is structured as `{ changeType: ADDED|UPDATED|REMOVED, name,
previousValue, currentValue, previousModelTokenSource, currentModelTokenSource }` and
explains automatic Environment Pool synchronization caused by the device operation,
including explicit create-time environment patches. Token sources are
`BUNDLED|CUSTOM|UNKNOWN`; only `BUNDLED` authorizes display-time localization of the
corresponding machine-facing name/value, and missing or `UNKNOWN` provenance stays raw.
The frontend treats these mutation snapshots as required authority, not optional legacy
metadata. A successful HTTP response with a missing collection, wrong `operation`,
missing affected item, or inconsistent `currentCount` is an unconfirmed outcome: the
Board refreshes the affected collections and never substitutes its local draft or an
empty array before displaying success.
Create-time `environmentVariablePatches` have the same field-level semantics as
`POST /api/board/environment`: each non-null field overrides that shared value, while
an omitted or null field retains the existing value (or the newly materialized template
default when the row did not exist). Device creation and these patches commit in one
transaction.

Device update ownership is deliberately split by user intent. There is no public
whole-`DeviceNodeDto` update endpoint: moving a node must not overwrite a runtime edit,
and saving runtime values must not move, rename, or retarget the device. `DeviceLayoutDto`
is the complete `{ position: { x, y }, width, height }` layout representation. Coordinates
must be finite and within `-1000000..1000000`; dimensions use the bounds in the table
above. The canvas rounds dimensions while resizing, so it never displays a shape the
integer storage contract cannot save.

`DeviceRenameRequestDto` is `{ label, expectedLabel }`. Both values are required strings
of at most 255 characters. The service compares `expectedLabel` with the current persisted
label while holding the Board write lock; a second dialog opened before another rename
therefore receives `409 Conflict` instead of silently overwriting the newer label. The same
locked check rejects a case-insensitive collision with any other current device as `409`,
including when another browser tab claimed the requested name after the dialog opened.

`DeviceRuntimeUpdateDto` is the complete device-local runtime representation:
`{ state, currentStateTrust, currentStatePrivacy, variables, privacies }`. It is a `PUT`,
not a field patch. Omitting/nulling optional source/sensitivity overrides means use the
selected template state's labels; omitting/nulling `variables` or `privacies` means no
explicit local overrides. Each collection accepts at most 100 items. Stateful devices
still require a legal `state`; no-mode
devices use no modeled state and may be stored with the canvas-only `Working` placeholder.
Shared environment values are not part of this subresource.

Both update commands return `DeviceUpdateResultDto`: `{ operation: updated|unchanged,
mutationType: layout|runtime, changedFields, previousDevice, currentDevice, currentNodes,
currentCount }`. `changedFields` is restricted to the selected subresource and is derived
from the before/after snapshots. The frontend rejects a response that changes a preserved
field, disagrees with the request, omits the updated device, or contradicts its own
`changedFields`/`currentCount`; it then reconciles from the server instead of announcing
success. All ordinary Board writes, device-type mutations, and their post-error refreshes
are applied through one client-side queue; assistant-triggered refreshes join the same
queue after the server tool completes. This prevents an older response snapshot from
rolling back a newer local action but does not make separate REST calls transactional.

The Board does not silently rename a device during final batch submission. Imported-list
name adjustments are shown item by item in the preview; if the current board would require
another adjustment by submit time, the complete batch is blocked before the request and
the proposed name changes are shown for review.

`DeviceDeleteRequestDto` is `{ impactToken }`, copied opaquely from the latest server
deletion preview. `DeviceDeletionResultDto` uses `operation=preview` for the read-only preview and
`operation=deleted` after commit; it returns the deleted device, exact `removedRules` /
`removedSpecifications`, itemized `environmentChanges`, and authoritative
`currentNodes` / `environmentVariables` / `currentRules` / `currentSpecifications`.
The preview's opaque `impactToken` binds the complete server-calculated device, rule,
specification, and Environment Pool effect; it intentionally does not require clients to
submit internal rule/spec ids. If any actual impact set differs from the preview, the endpoint returns
`409 Conflict` and writes nothing; the UI refreshes all affected collections and opens a
fresh preview. Environment changes are calculated by the same backend merge/prune logic
used for the commit, not inferred from frontend template caches. A shared Environment
Pool value is removed only when no remaining canvas device template requires it; deleting
one of several devices that depend on the same value keeps the value and its current
trust/privacy labels unchanged.

Rule/spec create/delete returns `CollectionMutationResultDto<T>`:
`{ operation, affectedItem, currentItems, currentCount }`. This is deliberately richer
than success/id/count so clients can explain exactly what changed and reconcile stale
local state.

Board node mutations validate more than shape. Device ids must be unique and must not
collide after NuSMV normalization (`AC 1` and `ac_1` are the same model id). For every
node, `templateName` must exist. Internal template variables are not canvas nodes; they
live in the template manifest and optional `variables` runtime overrides. Devices with a complete state machine (`Modes` plus `WorkingStates`) must provide
a legal state value for that template; no-mode devices do not send `state` or
`currentStateTrust` / `currentStatePrivacy` to NuSMV and may use/omit the canvas placeholder.
For mode devices, both overrides are optional. If omitted, the model uses the selected
`WorkingStates.Trust` / `WorkingStates.Privacy`; provided values must be
`trusted|untrusted` and `public|private`, respectively. These are source and sensitivity
labels used by propagation checks, not authentication, probability, encryption, or
access-control settings. Variable trust follows the same trust domain.
Variable runtime overrides must name declared device-local `InternalVariables` and stay
in their enum/range domains, and privacy overrides must name generated state/local-variable
privacy keys with values `public|private`. Template variables with `IsInside=false`
are not saved on a device instance; they are board-level environment variables
stored through `/api/board/environment`.

All ordinary creation paths materialize the same device-local starting values: the
template initial state and each local enum's first value or bounded number's lower bound.
Trust/privacy labels remain template-owned fallbacks unless the user or AI explicitly
supplies an advanced instance override. A device-list JSON field that is omitted or
`null` means "use the template default"; an explicit blank scalar or invalid value is
rejected. Standard scene JSON persists explicit overrides only, so export then import is
lossless without freezing template labels into every device.

### `BoardEnvironmentVariableDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `name` | `String` | Required; must be read by at least one current device template (`InternalVariables[].IsInside=false`) or affected by at least one current device through `ImpactedVariables`; affected-only devices do not gain rule/spec read permission |
| `value` | `String` | A non-null Environment Pool patch value must be non-blank and legal for the template domain; omitted/null preserves the current field. Complete scene replacement requires an explicit non-blank value |
| `trust` | `String` | A non-null Environment Pool patch value must normalize to `trusted` / `untrusted`; omitted/null preserves the current field. Complete scene replacement requires the field explicitly |
| `privacy` | `String` | A non-null Environment Pool patch value must normalize to `public` / `private`; omitted/null preserves the current field. Complete scene replacement requires the field explicitly |

The environment pool is persisted in `board_environment_variable` and scoped to the
current user's single development board. `GET /api/board/environment` is intentionally
self-healing: it reads current nodes/templates, inserts missing required variables with
the default value above, preserves existing values, and prunes variables no current
device can read or affect. `POST /api/board/environment` accepts only names required by
the current board and performs the same merge/prune validation before replacing the pool.
Each submitted item must provide at least one non-null `value`, `trust`, or `privacy`
field. It is a true field-level patch: omitted items and omitted/null fields preserve
their materialized current values. Explicit blanks, duplicate submitted names, unknown
names, and out-of-domain values are rejected before any write. Restoring template
defaults is an explicit product action implemented through the locked complete
read-modify-write service; REST callers do not encode that action as an ambiguous null.

`EnvironmentMutationResultDto` contains `{ operation: updated|unchanged, patchResults,
environmentVariables, environmentChanges, currentCount }`. Each `patchResults[]` row is
`{ name, suppliedFields, changedFields, preservedFields, previousValue, currentValue }`;
field names are `value`, `trust`, or `privacy`. It explains every submitted item,
including a valid no-change selection. `environmentVariables` is the authoritative full
pool, `environmentChanges` also reports any self-heal side effects, and `currentCount`
must match that pool. The frontend rejects an HTTP 200 response if an omitted field
changed despite being reported as preserved.
If the environment update response is lost or incomplete, the frontend reloads the
authoritative Environment Pool and tells the user to review those current values; it
does not claim that the requested patch was applied.
Ordinary device create/update/delete responses report every resulting pool addition,
update, or removal in `environmentChanges`; device deletion previews expose removals
before confirmation. These pool effects commit in the same transaction as the device
mutation and are never presented as a separate successful step.
`POST /api/board/batch` evaluates `environmentVariables` against the batch's resulting
`nodes`. Strict scene-replacement semantics always apply: all required variables and their
`trust`/`privacy` labels must be submitted explicitly.

All typed board mutation bodies reject unknown JSON fields. The standard scene batch
parser reports exact nested paths and validates template snapshots as raw schema objects,
so a misspelled field cannot be discarded and then reported as a successful import.

### `BoardBatchDto` scene-import fields

First call `GET /api/board/replacement-preview`. `BoardReplacementPreviewDto` is
`{ impactToken, deviceCount, environmentVariableCount, ruleCount, specificationCount }`.
The counts describe the authoritative server scene the user is about to replace, not a
possibly stale local canvas.

The subsequent batch requires non-null complete `nodes`, `environmentVariables`, `rules`,
`specs`, and `templateSnapshots` arrays. `nodes`, `rules`, `specs`, and
`templateSnapshots` each accept at most 100 items; `environmentVariables` accepts at most
200. The service repeats these limits for internal/AI callers rather than relying only on
HTTP DTO validation. There is no partial-update form of this endpoint; ordinary targeted
endpoints own partial intent.

| Field | Direction | Meaning |
| :--- | :--- | :--- |
| `impactToken` | Request | Opaque token copied from the exact preview the user confirmed. It is request-only and never becomes portable scene semantics. |
| `templateSnapshots` | Request | Exact self-contained `DeviceTemplateDto[]` dependency set for submitted `nodes`: every snapshot must contain equal, case-sensitive `name` and `manifest.Name` values; every referenced template must have one matching snapshot; no unreferenced snapshot is accepted; an existing template must have the same manifest; and a missing template is created in the transaction. Import never renames a template implicitly. Submit `[]` when the replacement scene contains no devices, including Clear Scene. |
| `createdTemplates` | Response | `DeviceTemplateDto[]` created during this request. It is empty when every referenced template already existed. |

Under the same user row lock used by board writes, the server recomputes the complete
current-board impact before resolving a template or changing a collection. If any device
layout/runtime/identity, Environment Pool value/label, rule/order, or specification/order
changed after preview, the token no longer matches and the server returns `409` before
writing. Its error `data` is `{ reasonCode: "BOARD_REPLACEMENT_STALE", currentPreview }`,
where `currentPreview` is a fresh `BoardReplacementPreviewDto`. The client must say that
nothing was replaced, refresh the Board, and require another explicit confirmation; it
must not retry automatically.

Template resolution, node/template capability validation, environment-pool validation,
and all board writes share the same user lock and transaction. A template mismatch,
missing snapshot, invalid template, invalid environment value, or invalid rule/spec
rolls back the whole request: the server does not leave a newly created template beside
a partially applied scene. An unreferenced snapshot is rejected rather than silently
ignored, and a referenced
template still requires its snapshot even when that template already exists in the
target account. This makes scene validity independent of target-account state. Missing,
duplicate, or unknown environment names and omitted environment `trust`/`privacy` labels
reject the whole scene; the server never fills or inherits a value behind a successful
scene-import result.

The batch request boundary is strict. Unknown fields anywhere in nodes, environment
values, rules, specifications, or their nested request objects are rejected before the
transaction instead of being discarded by DTO deserialization. Template manifests are
validated from the raw JSON against the canonical schema before conversion, so a typo or
new unsupported behavior field cannot produce a successful but lossy import. The
response-only `createdTemplates` field and template-catalog fields such as snapshot `id`
or `defaultTemplate` are also rejected in requests.

Portable scene scalar types are strict before the batch request is built. Fields defined
as strings remain JSON strings: the frontend does not coerce numbers or booleans into
device ids, labels, runtime values, rule/specification operands, or template names.
Export likewise rejects an incomplete current semantic item instead of dropping an
unnamed environment value/rule source or inventing a missing relation. A completed
import/export therefore never means that malformed input was silently repaired into a
different scene.

The standard portable JSON shape is `{ schema: "iot-verify.board-scene", version: 4,
templates, devices, environmentVariables, rules, specs }`. It contains stable device
references and authored semantics, but excludes database rule/spec/template ids and
derived caches (`templateLabel`, `formula`, `devices[]`, condition ids/sides/display
labels). Every shared environment variable required by a referenced template appears
exactly once with explicit `value`, `trust`, and `privacy`. Export
canonicalizes ordering and relations; import rejects unsupported versions, unknown
device references, incomplete environment/template snapshots, and internal/derived fields before
calling the atomic batch endpoint. Consequently a valid exported file can be imported
and exported byte-identically, while the reconstructed canvas may use new database ids
for rules/specs without changing its semantic model. Portable device geometry uses the
same domain as targeted canvas writes and AI scene drafts: coordinates are finite within
`-1000000..1000000`, width is `80..2000`, and height is `60..2000`. An exported boundary
value is therefore a valid import value; no narrower file-import range may crop or reject
a valid saved canvas.

The browser rejects portable scene files larger than 64 MiB before reading or exporting
them, rejects targeted device-list imports larger than 4 MiB, and rejects device-template
imports larger than 512 KiB. The backend uses the matching dedicated 64 MiB boundary only
for authenticated `POST /api/board/batch`; every other JSON request retains the 4 MiB
pre-binding limit. This lets a valid scene carry its referenced self-contained template
snapshots and embedded icons without widening unrelated endpoints.

Rule and specification array order is persisted explicitly. The database-only
`rules.execution_order` and `specification.list_order` columns are written from the
submitted array positions and never appear in portable JSON. Repository reads order by
those columns, so database iteration order cannot silently reorder a scene before its
next export. `specification.list_order` is review/round-trip order only; unlike rule
execution order, it does not assign verification priority or short-circuit checks.

Portable device-local `variables[]` entries contain a unique non-blank `name` and an
explicit non-blank `value`; `privacies[]` names are also unique. Every shared
`environmentVariables[]` entry likewise has a unique non-blank `name` and an explicit
non-blank `value`. Duplicate names fail before the replacement preview or batch request.
An omitted or empty runtime value would mean "use a default" in targeted creation/update semantics,
which is not lossless scene semantics, so v4 import rejects it. A rule's human-readable
`name` is optional; rule array order and its structured trigger/action fields carry the
model semantics.

Version 4 removes the canvas-only `Working` placeholder from portable semantics. A device
whose template has both `Modes` and non-empty `WorkingStates` must include `state` and may
include `currentStateTrust` / `currentStatePrivacy`. A no-state-machine device must omit all
three fields and express readings through local variables or the shared environment pool.
Import materializes `Working` only inside the canvas DTO when needed for rendering, and
export removes it again, so the placeholder never becomes a user-authored state.

Ordinary UI creation and the AI `add_device` command generate a stable device reference
independently of the user-facing device name. Renaming therefore changes only `label`;
it never rewrites rule/specification references. Standard scene JSON is the technical
portability layer and preserves its submitted `devices[].id` values exactly. Before any
scene collection is written, the backend checks those ids (after model normalization)
against the shared-environment variables, rule playback markers, attack-analysis
bookkeeping, and stored-condition fix variables that the scene can generate. A collision
returns `422` with every field reason under `data.errors` and rolls back the complete
replacement. The error may require changing `devices[].id` and its matching references;
the display `label` can remain unchanged.

Across manual creation, standalone AI recommendation apply, and assistant `add_device`,
an explicitly chosen display name has exact semantics: a case-insensitive conflict causes
no write and the user must confirm a different available name. Automatic suffixing is
limited to system-generated names and the JSON import preview, where every deterministic
rename is shown before the atomic append/replacement is confirmed.

Manual creation, AI recommendation apply, and standard scene import converge on the same
stored DTO semantics: device references are canonical node ids, rule trigger types are
explicit, specification conditions are authoritative, and formula/device lists are
rebuilt display caches. Device-list JSON/CSV import is intentionally a targeted append,
not a scene replacement; its preview reports validation errors and deterministic
duplicate-name renames before the atomic create request. JSON values for template/name
aliases and runtime fields must have the documented string types, and only one alias from
each template/name group may be supplied; the importer never chooses between conflicting
aliases or converts numbers/booleans silently. The scrollable preview keeps every row,
including errors and planned renames beyond the first screen, inspectable before the
all-or-nothing create action is enabled.

After a scene-replacement `200` response, the Board canonicalizes the returned nodes,
environment pool, rules, and specifications and compares them with the requested v4
semantics before showing a completed replacement. A missing or non-equivalent response
enters the same authoritative reload/reconciliation path as a lost response; it is not
presented as a successful full import merely because HTTP status was successful.

Rules and specifications still reference environment variables through a device prefix
(for example `sensor_1.temperature`). That prefix means "this device's template declares
permission to read `temperature`"; the actual initial value, trust, and privacy come
from `BoardEnvironmentVariableDto`. NuSMV generation initializes one shared
`a_<name>` variable from that pool and mirrors it only into devices with read permission.

### Rule-derived canvas connections

There is no persisted `/api/board/edges` endpoint. The Board UI derives visible rule
connections from `RuleDto.conditions` and `RuleDto.command`, and the `board_overview`
AI tool uses the same rule-derived topology. Frontend `DeviceEdge` is only a canvas
display shape, not a backend DTO.

### `RuleDto` / `SpecificationDto`

The Java DTO classes are shared with [verification.md](verification.md), but device
reference **values** are boundary-specific. Board storage endpoints persist raw
`DeviceNode.id` values. Verification/simulation endpoints consume model `varName`
values after `frontend/src/utils/modelRequest.ts` or backend `BoardDataConverter`
normalizes those ids.

The authoritative specification write shape is `{ id, templateId, aConditions,
ifConditions, thenConditions }`. Each condition write contains only `deviceId`,
`targetType`, `key`, optional `propertyScope`, `relation`, and `value`. The shared Java
response DTO also contains `templateLabel`, `formula`, `devices[]`, condition `id`,
`side`, and `deviceLabel`; callers must not treat those fields as writable semantics.
Board storage ignores contradictory supplied display values and rebuilds them from the
accepted template id, containing condition collection, current node labels, and
structured conditions. Frontend targeted and batch writers omit those caches entirely.

Rule sources and targets created by the frontend use canonical board node ids as their
stored references. Before creating a rule, duplicate-check,
verification, or simulation, the frontend must ensure each rule has at least one trigger
source and each source has `itemType` so the backend receives `targetType`. The backend
enforces non-empty conditions with `@NotEmpty`.

Rule source `targetType=api` means "this device emitted an API signal". It may use only
template APIs whose `Signal` flag is `true`, and it must not carry `relation` or
`value`. Rule commands may target any template API action; commands are not restricted
to signal APIs. The signal is a one-step event pulse derived from an actual
`StartState -> EndState` change. Remaining in `EndState` does not keep the condition
true. Multi-mode events require the complete start/end tuple, and a template cannot
declare two signal APIs with the same modeled transition because the model could not
distinguish them.

The Board labels this source kind **Action Event**, not merely "API": it is an
observable one-step event produced by a state-changing action, whereas the THEN side
labels an **Action** because it requests a device command. A command-only API can be a
THEN action but cannot be selected as an IF event.
Optional `command.contentDevice` and `command.content` are a pair: they select one
template-authored `Content` sensitivity label to propagate with the action. They do not
represent payload bytes or successful transmission. The pair is legal only when the
target action declares `AcceptsContent=true`; neither field may appear alone.
Rule source `targetType=mode` and `targetType=state` are enum conditions and support
only `=`, `!=`, `in`, and `not in`. Numeric `targetType=variable` conditions support
those set/equality operators and additionally support ordering comparisons. Enum
variables declared with `Values` follow the enum-operator rule.
Rule sources are current-step guards: IF evaluates the source value/signal currently
visible on the board and in traces, while THEN writes the target device's next state.
This is the shared semantic contract used by saved boards, AI recommendations,
NuSMV generation, simulation, verification, history replay, and fix suggestions.

Rule array order is also model behavior. If several enabled rules command the same
device mode in one model step, the first matching rule in the saved order wins. An API
that affects several modes is one action: if an earlier matching action overlaps any of
those modes, the later action is blocked as a whole rather than partly applied. Rules
whose API effects are disjoint can still take effect together. The
Board inspector displays this order and changes it through `PUT /rules/order`. A newly
created manual or AI-recommended rule is appended last. The endpoint is a targeted,
identity-preserving reorder, not a scene replacement, and returns the authoritative
ordered collection. Changing order can change verification/simulation results, so the
client asks the user to run them again.

The database-only `rules.execution_order` column stores this behavior but is not a
portable identifier or an authored DTO field. Standard scene files carry the same
semantics solely through `rules[]` array order, so export/import remains lossless without
exposing a storage index.

Board saves perform lightweight template-semantic validation before persistence. Rules
are rejected with `422 ValidationException` when a source variable/mode/state/API key is
not defined by the referenced device template, a command action is not a template API,
a content key is unknown on `contentDevice`, content is attached to an action whose API
does not declare `AcceptsContent=true`, or a state/mode/variable value is not legal.
Specifications are likewise checked against the current template manifest: API
conditions require `Signal=true` APIs and boolean values; trust/privacy values must be
`trusted|untrusted` and `public|private`; trust/privacy keys must resolve to a variable
or state property key. Variable conditions must match declared enum `Values` or numeric
`LowerBound..UpperBound` ranges when the template defines them; enum variables cannot
use ordering comparisons.

### `BoardLayoutDto`

`{ canvasPan: {x,y}, canvasZoom: Double, panels: { control: PanelLayout,
inspector: PanelLayout } }`.

`PanelLayout` is `{ collapsed: Boolean, width: Double, activeSection: String }`.
`panels.control.activeSection` is one of `devices`, `templates`, `rules`, `specs`;
`panels.inspector.activeSection` is one of `devices`, `rules`, `specs`. The board
stores panel collapsed state, width, active section, and canvas pan/zoom in this one
layout document. Panel widths are normalized to `240..520`, and `canvasZoom` is
normalized to `0.4..2.0`. There is no separate active-tabs endpoint.

### Schema cleanup note

The project currently uses Hibernate `ddl-auto: update`, without Flyway/Liquibase.
Removing entities or fields from Java code will not drop old MySQL schema objects.
The deliberate compatibility exception is the specification identity guard: after
Hibernate initializes the schema and before the application becomes ready,
`SpecificationPrimaryKeyMigration` accepts either the legacy primary key `(id)` or the
current user-scoped key `(id, user_id)`. It atomically upgrades the legacy MySQL key,
preserves existing rows, is a no-op after migration, and refuses startup for any unknown
primary-key shape rather than serving with ambiguous cross-user ownership.
After deploying code that removes persisted edges, old floating/dock layout fields, or
pre-authority internal variable canvas nodes, clean an existing database manually if you
want the physical schema/data to match:

```sql
DROP TABLE IF EXISTS device_edge;

ALTER TABLE board_layout
  DROP COLUMN input_x,
  DROP COLUMN input_y,
  DROP COLUMN status_x,
  DROP COLUMN status_y,
  DROP COLUMN input_is_docked,
  DROP COLUMN input_dock_side,
  DROP COLUMN input_last_pos_x,
  DROP COLUMN input_last_pos_y,
  DROP COLUMN status_is_docked,
  DROP COLUMN status_dock_side,
  DROP COLUMN status_last_pos_x,
  DROP COLUMN status_last_pos_y;
```

Do not delete current devices by a `template_name` prefix. `variable_` is no longer a
reserved template-name prefix; a custom template such as `variable_sensor` is an ordinary
device template. If an old database contains historical pseudo variable rows, identify
them from a pre-migration backup or explicit legacy metadata before deleting them.

---

## Device templates

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/templates` | → `DeviceTemplateDto[]` | Side-effect-free read of the current user's type catalog; an empty catalog stays empty |
| GET | `/api/board/templates/schema` | → JSON Schema | Returns the authoritative `backend/device-template-schema.json` for UI download/inspection |
| POST | `/api/board/templates` | `DeviceTemplateDto` → `DeviceTemplateDto` | Create a custom template (validates `manifest` against `backend/device-template-schema.json`, then runs NuSMV-specific validation and a probe pre-check) |
| GET | `/api/board/templates/{id}/deletion-preview` | → `DeviceTemplateDeletionResultDto` (`operation=preview`) | No-write preview with exact device-instance blockers and an opaque impact token |
| POST | `/api/board/templates/{id}/delete` | `DeviceTemplateDeletionRequestDto { impactToken }` → `DeviceTemplateDeletionResultDto` (`operation=deleted`) | Deletes only if the preview is still current and has no blockers |
| GET | `/api/board/templates/defaults/reset-preview` | → `DefaultTemplateResetResultDto` (`operation=preview`) | Computes exact type, device, and Environment Pool effects without writing |
| POST | `/api/board/templates/defaults/reset` | `DefaultTemplateResetRequestDto { impactToken }` → `DefaultTemplateResetResultDto` (`operation=reset`) | Atomically applies the unchanged preview and returns authoritative final snapshots |

### `DeviceTemplateDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `id` | `Long` | Null on create; assigned by DB |
| `name` | `String` | Required |
| `manifest` | `DeviceManifest` | Required |
| `defaultTemplate` | `Boolean` | `true` for system-imported defaults, `false` for user-created/custom uploads; used by the UI for grouping and default-template reset |

Each user may store at most 100 device types. The canonical manifest schema also bounds
collection cardinality before semantic or NuSMV validation: 20 modes and 100 each for
working states, per-state dynamics, internal variables, values, environment domains,
impacted variables, transitions, APIs, and content items. Default reset performs the same
projected-catalog check and reports a no-write blocker when restoring bundled definitions
would exceed the catalog limit.

Default reset is a two-step destructive command. The preview classifies every bundled
type as `RESTORE_MISSING`, `REFRESH_DEFAULT`, or
`REPLACE_CUSTOM_NAME_COLLISION`, and reports obsolete bundled types as
`REMOVE_OBSOLETE_DEFAULT`. Each row says whether the manifest semantics change. The
preview also lists existing device instances that use changed definitions, itemized
Environment Pool changes, and blockers caused by device/rule/spec incompatibility.
Each blocker carries a user-facing `itemLabel`, stable `reasonCode`, and English
technical `reason`; ordinary UI localizes the reason code and keeps the diagnostic in a
technical disclosure. `canApply=false` exactly when blockers are present.
For each reset Environment Pool change, the backend derives previous and current token
provenance separately from the templates actually referenced by canvas devices. A shared
variable is `BUNDLED` only when every provider on that side is a bundled type; a custom
provider or unresolved source prevents localization. This matters when a custom
name-collision is replaced by a bundled definition: the old and new snapshots can have
different provenance even though the variable name is unchanged.

The POST accepts only the opaque `impactToken` from that preview. Under the per-user
write lock it recomputes the preview; board/type drift returns `409` and performs no
write. It then deletes replaced/obsolete defaults, imports **all** bundled definitions,
runs template and NuSMV pre-checks, validates the existing device instances, rules, and
specifications against the new manifests, and updates the Environment Pool in one
transaction. Existing environment values outside a new domain are reset to that
definition's explicit default and appear as `environmentChanges`; they are not silently
retained or dropped. Any resource, validation, import, or pre-check failure rolls back
the complete reset.

`DefaultTemplateResetResultDto` contains `{ operation, impactToken, canApply,
templateChanges, affectedDevices, blockers, environmentChanges, currentTemplates,
environmentVariables }`. `affectedDevices` carries stable `deviceId` plus the
user-facing `deviceLabel` and `templateName`; the ordinary UI displays the labels, not
the internal id. On a committed reset, `currentTemplates` and `environmentVariables`
are authoritative post-transaction snapshots. On a lost/incomplete response, the
frontend reads both collections and presents that reconciled current state without
retrying the destructive request or claiming success.

Blocker `reasonCode` is one of `DEVICE_INSTANCE_INCOMPATIBLE`,
`AUTOMATION_RULE_INCOMPATIBLE`, `SPECIFICATION_INCOMPATIBLE`,
`ENVIRONMENT_POOL_INCOMPATIBLE`, or `BOARD_MODEL_INCOMPATIBLE`.

Deleting a template is intentionally strict in development. Because canvas nodes use
`templateName` as their semantic pointer into the template manifest, the backend rejects
deletion while that template is still referenced by any canvas device. This prevents a
board that looks valid in the UI but cannot be consumed by NuSMV, AI recommendations, or
fix logic.

Template deletion is a two-step command, not a one-click `DELETE`. The preview response
contains `{ operation, impactToken, canDelete, template, blockers, currentTemplates }`.
Each blocker is `{ reasonCode, itemId, itemLabel, reason }`; ordinary UI shows the
device label and localizes `DEVICE_INSTANCE_USES_TEMPLATE`, while the internal id and
English diagnostic stay in technical detail. A blocked preview has `canDelete=false`
and cannot be committed.

The commit request accepts only the preview's opaque `impactToken`. Under the per-user
write lock and transaction, the backend recomputes the template and blocker set. A stale
token returns `409` with `reasonCode=TEMPLATE_DELETION_PREVIEW_STALE` and
`currentPreview`; a still-in-use template returns `TEMPLATE_DELETION_BLOCKED`. Neither
case writes. A successful result includes `deletedTemplate` and authoritative
`currentTemplates`, which the client uses directly instead of guessing local state.
Both preview and commit scope lookup by `templateId + userId`. A missing id and a
template owned by another account therefore return the same `404`, without revealing
whether another user's resource exists.

`DeviceManifest` uses **PascalCase** JSON keys (`@JsonProperty`): `Name`,
`Description`, `Icon`, `Modes`, `InternalVariables`, `EnvironmentDomains`,
`ImpactedVariables`, `InitState`,
`WorkingStates`, `Transitions`, `APIs`, `Contents`. Key nested shapes:

`backend/device-template-schema.json` is the authoritative structural schema for the
`manifest` object. The backend validates the raw incoming `manifest` JSON against that
schema before DTO mapping, so unknown fields and lower-case alternatives are rejected
at the API boundary. Frontend helpers may normalize user-uploaded JSON before sending,
but the final request body must match this schema. The Maven build packages the same
file to `classpath:device-template-schema.json`, and `DEVICE_TEMPLATE_SCHEMA_PATH` may
override its filesystem location for deployments.

Structurally, the schema requires only `Name` at the manifest top level. Other arrays
may be omitted and are treated as empty by consumers. Semantically, a mode-based
template must provide the full state-machine trio: non-empty `Modes`, non-blank
`InitState`, and non-empty `WorkingStates`. If all three are absent/empty, the backend
treats the template as a no-mode device template and validates only variables,
environment impacts, contents, and the NuSMV probe pre-check. APIs are state actions and
therefore require at least one mode; stateless autonomous variable behavior belongs in a
triggered `Transition`.

`InitState` is a concrete complete configuration: it contains exactly one value per mode
and must exactly match one `WorkingStates.Name`. Empty segments, `_` wildcards, and
case-different aliases are rejected rather than allowing the generator to miss the
declared initial state and fall back to nondeterminism. Partial tuples remain valid only
where an API/Transition endpoint explicitly denotes a partial state change; they are
rejected for initial state because manual creation and portable scenes require one
deterministic starting point.

Template names and user-authored variable/property keys are literal business names.
There is no reserved `variable_` template-name prefix, and generated NuSMV prefixes or
suffixes such as `a_`, `trust_`, `privacy_`, `_rate`, `_a`, and `is_attack` are not
accepted as user-facing aliases. During template creation the backend rejects concrete
generated identifier collisions inside the same NuSMV module, for example an
InternalVariable `temperature_rate` colliding with the generated rate variable for
ImpactedVariable `temperature`, or InternalVariable `trust_temperature` colliding with
the generated trust variable for InternalVariable `temperature`. A prefixed business name
is valid when it does not collide with an actually generated identifier. Model
generation applies the same concrete-collision rule in `MODULE main`: device instance
ids must not collide with generated `a_<environmentName>`, the internal compromised-point
counter, or
auto-fix parameterization identifiers active in that model.

- `InternalVariable`: `Name`, `Description`, required `IsInside`,
  `FalsifiableWhenCompromised`, required `Trust`, required `Privacy`,
  `LowerBound`, `UpperBound`, `NaturalChangeRate`, `Values`. `Privacy` is a model
  sensitivity label used for propagation analysis; it does not configure runtime
  visibility, authorization, or encryption. `FalsifiableWhenCompromised` is required
  and states whether a compromised instance may replace this reported value with any
  value in its declared domain and mark the source untrusted. It applies to both shared
  (`IsInside=false`) and device-local (`IsInside=true`) readings, so API
  presence is not used to guess whether the value is sensor data. Use `false` for
  actuator progress/setpoints and other values outside that threat model. **Provide
  exactly one explicit domain: `Values` (enum, including `TRUE`/`FALSE` for booleans)
  XOR `LowerBound`+`UpperBound` (numeric range); never omit the domain, provide both
  forms, or provide only one bound** (backend `@AssertTrue isValidVariableDefinition`).
  Numeric bounds must be ascending. Enum values must remain distinct after spaces are
  removed for NuSMV. `NaturalChangeRate` is valid only for numeric domains, must fit a
  Java integer, and a two-value range must be ascending.
- `EnvironmentDomain`: `Name`, `Description`, required `Trust`/`Privacy`, and either
  `Values` or `LowerBound`+`UpperBound`, plus optional `NaturalChangeRate`. It supplies
  the domain for a name this template lists in `ImpactedVariables` but does not read;
  it creates no device variable and grants no rule/spec read capability. Every impact
  must resolve inside the same manifest, and unused/redundant domain entries are rejected.
- `WorkingState`: `Name`, `Description`, required `Trust`, required `Privacy`, `Dynamics[]`
  (`Dynamic` = `VariableName`, `Value`, `ChangeRate`). In a multi-mode template, every
  working-state name is a complete semicolon-separated tuple with one concrete value per
  mode. If the same mode-state component appears in several tuples, all of those rows
  must assign it the same effective `Trust` and `Privacy`; otherwise the manifest is
  rejected because the component-level formal labels cannot represent it losslessly.
  Trust is MEDIC's control-source label used when that state triggers a rule or safety
  property: one trusted contributing trigger source retains trusted control, while only
  an all-untrusted trigger set makes the target untrusted. It is not authentication or a
  generic data-integrity label. Privacy is the state's sensitivity label. These
  labels are modeled for stateful sensors even when the template has no command APIs.
  Raw `Invariant` strings are not accepted: the previous field was stored and displayed
  but never entered the generated model. Express device evolution through structured
  `Dynamics`/`Transitions`, and user requirements through structured specifications.
- `Content`: `Name`, optional explanatory `Description`, and required `Privacy`. Content sensitivity has no safe implicit
  default: omitting it is rejected rather than silently treating the item as public.
  Each Dynamic target must be either a device-local `InternalVariable` or a shared name
  listed in `ImpactedVariables`, and may appear once per WorkingState. Numeric targets use
  integer `ChangeRate`; enum/boolean targets use an in-domain `Value`. Wrong-domain,
  duplicate, or unknown effects are rejected rather than saved and skipped by generation.
- `Transition`: `Name`, `Description`, `StartState`, `EndState`, `Trigger`
  (`Attribute`, `Relation`, `Value`), `Assignments[]` (`Attribute`, `Value`). A Transition
  is autonomous device behavior, not a user-callable command. The current formal model
  accepts exactly one effect per Transition: one concrete mode target or one variable
  assignment, never both and never several. This fail-fast restriction prevents a
  conflict from applying only part of an accepted-looking action. A variable-changing
  transition requires a trigger. Trigger attributes and values must belong to a readable
  mode/variable domain; enum, mode, and boolean triggers use only `=`/`!=`. Every assignment
  target must be a declared `InternalVariable` or `EnvironmentDomain`, and its value must
  belong to that declaration's enum/range/boolean domain. Stateless templates may use
  trigger-plus-assignment transitions, but cannot declare state endpoints. `Signal` is not
  accepted on Transitions because rules and specifications cannot reference an internal
  transition pulse; user-consumable event pulses belong to state-changing APIs.
- `API`: `Name`, `Description`, `Signal`, optional `AcceptsContent`, `StartState`, `EndState`,
  `Trigger: null`. Despite the manifest field name, these are device commands/actions,
  not HTTP or network endpoint definitions. APIs change modeled state only: non-empty
  `Assignments` is rejected, as are stateless APIs and APIs with no possible state effect.
  API triggers are not a supported generator semantic; conditional autonomous behavior
  belongs in `Transitions`. `StartState` is required; an explicit empty string or `_`
  pattern means “callable from any state”, while a concrete value is the command
  precondition. `Signal` is a required explicit choice: `true` makes the
  action observable as an automation/specification trigger, while `false` leaves it
  command-only. When `Signal=true`, the API event is a one-step observation of
  an actual complete `StartState -> EndState` change, not a persistent "currently in the
  end state" flag. An observable API route may not overlap another API or autonomous
  Transition route, because a state-change-derived pulse could not identify which action
  occurred. `AcceptsContent` defaults to `false`; when `true`, a rule invoking this action
  may select exactly one template `Content` item as an additional sensitivity-propagation
  source. It does not model payload bytes, an upload protocol, access control, encryption,
  or successful delivery. Rules cannot attach content labels to ordinary actions that do
  not declare this capability.
- `Content`: `Name`, optional `Description`, `Privacy`.

Only templates instantiated by current board devices contribute environment semantics.
Installed but unused templates are irrelevant. Declarations for the same active shared
name must use the same literal casing, domain (including enum order), natural change
rate, default trust, and default privacy; node/scene writes reject conflicts before
persistence, so device ordering cannot choose the model silently.

`Icon` is optional and is ignored by NuSMV generation. It exists for UI rendering:
custom JSON imports may provide a self-contained `data:image/...` URI (max 256 KB).
Remote URLs are rejected so opening a catalog cannot contact a template-controlled host.
If `Icon` is omitted, the frontend first looks for a bundled
default asset matching the template/state, then generates a stable fallback icon from
the template name so custom templates never render as blank images.

Rule conditions must include `targetType` (`api | variable | mode | state`). The
backend stores and returns it as the authoritative semantic type for UI, AI, NuSMV
generation, and fix logic. Device references use canonical board node ids; labels are
display-only. See [../architecture/device-identity.md](../architecture/device-identity.md).

After schema validation, the NuSMV-specific constraints (identifier legality,
StartState/EndState format, trust/privacy values) are enforced by runtime validation —
see
[../architecture/nusmv-model.md](../architecture/nusmv-model.md) and the P1–P5 rules in
[../architecture/spec-templates.md](../architecture/spec-templates.md). In particular,
`Trust` must be `trusted` or `untrusted` and `Privacy` must be `public` or `private`
(case-insensitive; P4) — other values are rejected at generation time. Default template
JSON lives in `backend/src/main/resources/deviceTemplate/` and is also checked against
the canonical schema when imported.

---

## Recommendation, duplicate check, and AI similarity check

These delegate to AI tools (see [ai-tools.md](ai-tools.md)). They return
typed recommendation DTOs inside `Result<T>`; an AI-tool error is translated to the
matching HTTP status by `throwIfToolError`, and malformed success output fails closed
instead of crossing the controller as an untyped map.

Every standalone recommendation request requires an opaque `requestId` containing 8–80
characters. It starts with an ASCII letter or digit and otherwise accepts letters, digits,
`.`, `_`, `:`, and `-`; the same rule applies to request bodies, query parameters, status
paths, and cancellation paths.

| Method | Path | Query / Body | Notes |
| :--- | :--- | :--- | :--- |
| POST | `/api/board/rules/recommend` | JSON body `StandaloneRecommendationRequestDto`: required `requestId`, `maxRecommendations` (default 5; integer `1..10`), `category` (default `all`), `language` (default `en`), and optional `userRequirement` | Returns `RecommendationResponseDto<RuleRecommendationDto>` |
| POST | `/api/board/specs/recommend` | JSON body `StandaloneRecommendationRequestDto`: required `requestId`, `maxRecommendations` (default 5; integer `1..10`), `category` (`all`, `safety`, `response`, `consistency`, or `privacy`; default `all`), `language` (default `en`), and optional `userRequirement` | Returns `RecommendationResponseDto<SpecificationRecommendationDto>` |
| POST | `/api/board/devices/recommend` | Required `requestId` query parameter plus typed `DeviceRecommendationRequestDto`: `{ maxRecommendations, language, userRequirement }` | Returns `RecommendationResponseDto<DeviceRecommendationDto>` |
| POST | `/api/board/scenario/recommend` | Required `requestId` query parameter plus typed `ScenarioRecommendationRequestDto`: `{ maxDevices, maxRules, maxSpecs, language, userRequirement }` | Returns `ScenarioRecommendationResponseDto`, including `scenarioName`, a deterministic post-validation `rationale`, objective completeness, validation counters, structural readiness, semantic warnings, and a typed `PortableSceneDto` using the canonical `iot-verify.board-scene` import/export shape. |
| GET | `/api/board/recommendations/{requestId}` | Reads the authenticated user's matching active or just-finished request | Returns `InteractiveOperationStatusDto`; terminal status is retained briefly for the final polling tick, while unknown requests return 404 |
| DELETE | `/api/board/recommendations/{requestId}` | Cancels the authenticated user's matching in-flight request | Returns `boolean`; `true` means the durable stop signal was accepted for the matching local or remote execution. The callable may still be unwinding, so status remains authoritative until `FINISHED` |
| POST | `/api/board/rules/check-duplicate` | body: typed `RuleDto`; every condition includes `targetType`; rule API-signal conditions omit `relation`/`value` | Deterministic duplicate-rule check used by `RuleBuilderDialog` before saving. It does not call the external LLM and returns a typed `DuplicateRuleCheckResultDto`: required `isDuplicate`, `requiresReview`, `similarity` (`0..1`), `matchType`, stable `reasonCode`, technical `reason`/`message`, plus nullable readable `matchedRule`. Clients localize the ordinary explanation from `reasonCode`. |
| POST | `/api/board/rules/check-similarity` | body: typed `RuleDto`; every condition includes `targetType`; rule API-signal conditions omit `relation`/`value` | Explicit AI semantic similarity check available from `RuleBuilderDialog` and the Board rule-recommendation apply flow. It may call the configured LLM and returns a typed `RuleSimilarityResultDto`: required `isSimilar`, `isDuplicate`, authoritative `requiresReview`, `similarity` (`0..1`), stable `reasonCode`, technical `reason`/`message`, plus nullable readable `matchedRule`. Internal candidate references and LLM prose are not ordinary UI concepts. |

Duplicate-check `reasonCode` is one of `NO_EXISTING_RULES`, `EXACT_MATCH`,
`TRIGGER_SET_CONTAINS_OTHER`, `SAME_TRIGGER_SHAPE_DIFFERENT_VALUES`,
`PARTIAL_TRIGGER_OVERLAP`, or `NO_MATCHING_SIGNATURE`. AI similarity uses
`NO_EXISTING_RULES`, `AI_DUPLICATE`, `AI_SIMILAR`, `AI_HIGH_SCORE_REVIEW`, or
`AI_NO_SIGNIFICANT_SIMILARITY`. `requiresReview` is the server decision; clients do not
recompute it from the score. The score and AI reason are evidence, not proof of safety or
conflict freedom.

> Standalone device/rule/spec recommendation responses include backend-generated `message`,
> `count`, `requestedCount`, `validatedCount`, `filteredCount`, `filteredItems`,
> `rawCandidateCount`, `inspectedCount`, `truncatedCount`, and `recommendations`.
> Device and rule recommendation responses additionally include `adjustedCount` and
> `adjustedItems` for deterministic values added to, or semantics-preservingly
> normalized within, kept candidates.
> `count` and `validatedCount` are the kept recommendation count; `filteredCount` is the
> number of AI suggestions inspected but rejected because they did not match current
> board/template capabilities. `filteredItems[]` gives per-candidate feedback as
> `{ type, index, reasonCode, reason, label? }`; `reason` is localized according to
> `language`, and `label` is best-effort display text such as the saved rule name,
> specification rationale, device label, or template name. `rawCandidateCount` is the number of parsed AI
> candidate entries, `inspectedCount` is the number the backend actually validated, and
> `truncatedCount` is the number left uninspected after the requested limit was reached.
> The accounting identities are contractual: `inspectedCount = validatedCount +
> filteredCount` and `rawCandidateCount = inspectedCount + truncatedCount`, while
> `filteredCount` equals `filteredItems.length`. The Board displays all five counts in
> every recommendation panel and rejects an inconsistent response instead of showing a
> partially explained result. A parsed empty AI array is explicitly reported as zero raw
> candidates, distinct from candidates that the backend inspected and rejected.
> The backend localizes its own fallback/success messages according to `language`; the
> LLM prompt also instructs generated natural-language fields such as `name`, `rationale`, and
> `reason` to use that language. Omitted/blank filters use their documented defaults, but
> an unsupported language/category, non-string requirement, or `userRequirement` longer
> than 2,000 trimmed characters returns `400`; no explicit filter is silently downgraded or
> truncated before prompting.
> A standalone rule API event normally omits `relation` and `value`. The semantically
> equivalent AI spelling `{ relation: "=", value: "TRUE" }` is kept, normalized to the
> event form, returned as an `apiEventSyntaxNormalized` adjustment, and shown by the
> Board before application. Partial comparison fields, `FALSE`, and non-equality
> relations are filtered with `invalidApiEventSyntax`; the backend no longer silently
> erases a comparison that may change the event meaning.
> The controller maps the tool output into these DTOs and rechecks every accounting
> identity before returning HTTP 200. Missing audit fields, unexplained filtered or
> adjusted entries, unknown kept-candidate fields, and malformed portable-scene fields
> return HTTP 502 rather than crossing the REST boundary as an untyped success map.
> The standalone scenario endpoint likewise returns only its typed REST fields. Chat-only
> `draftStored` and `previousDraftRetained` metadata is added only when the same tool runs
> inside an authenticated chat session; it never leaks into `/scenario/recommend` success
> responses.
> Standalone recommendation DTOs omit genuinely absent optional values instead of
> serializing them as explicit `null`. Rule API conditions therefore remain relation/value-
> free, and specification recommendation conditions contain only authored semantic fields:
> persistence-only condition `id` and derived group `side` never cross this boundary.
> The Board validates every kept candidate before display/application and fails closed if
> this exact shape is violated; it does not invent a relation or coerce a scalar locally.
>
> Rule candidates contain required `name`, `conditions`, and `command`, plus optional
> advisory `category`. `name` is not
> advisory copy: it is the exact user-facing rule name persisted when Apply succeeds.
> Candidates are returned in relevance order and do not contain a `priority` field;
> applying one appends it to the end of the current execution order and never silently
> promotes it above existing rules. Specification candidates contain `rationale`,
> `templateId`, and all three condition arrays. `rationale` explains why the AI suggests
> checking the property but is not persisted or verified; the formal property consists of
> `templateId` plus structured conditions. Specification recommendations likewise have no
> priority/check-order field because every accepted property is checked. A missing rule
> name or specification rationale is an itemized filtered candidate, and the REST boundary
> rejects a kept candidate missing either field rather than returning a misleading HTTP 200.
>
> Device recommendations are instance-level. Each kept item contains `templateName`, an
> effective `suggestedLabel`, and may contain advisory `intendedUse`/`suggestedPlacement`;
> these two context fields are neither persisted device properties nor formal-model inputs. For a stateful or locally
> parameterized template it also contains effective `initialState` and
> `initialVariables`; explicit advanced overrides may add `currentStateTrust`,
> `currentStatePrivacy`, per-variable trust, and `initialPrivacies`. Runtime values are
> constrained to local template variables (`IsInside=true`). If an AI candidate supplies an
> invalid initial state, malformed runtime arrays, unknown local variables, invalid local
> variable values, or invalid trust/privacy values, the whole device candidate is rejected
> with a `filteredItems[]` reason instead of being returned with those fields silently
> dropped. Omitted state/value fields are materialized from template defaults and reported in
> `adjustedItems[]` as `{ type, index?, reasonCode, reason, label?, appliedValues }`, so the
> preview and later create request use the same initial model. Omitted trust/privacy
> fields stay absent so the active template remains authoritative. Display labels are unique
> across the whole board ignoring case, even across different templates. Multiple
> recommendations may use the same template when they represent different labels or
> advisory contexts. Applying a recommendation writes the effective device type, label,
> layout, and runtime values only. It may also initialize currently missing shared
> Environment Pool items required by the template; the Board previews their names and
> presents the authoritative `environmentChanges` returned by the create transaction.
>
> `/scenario/recommend` is intentionally not a wrapper around the three standalone
> recommendation endpoints. It asks the AI for one coupled scene draft, then validates
> temporary device aliases, template names, device initial runtime, rule capabilities, specification
> condition keys, and the scene environment pool against that single draft. If a generated
> device supplies an initial `state`, `currentStateTrust`, or `currentStatePrivacy` that does not match its
> template, the whole device candidate is filtered instead of being returned with a silent
> default. Environment variables are not arbitrary JSON attachments: a kept variable name
> must be declared as an external template variable or listed in `ImpactedVariables` by at
> least one kept device template; unknown environment candidates are filtered with
> `type: "environment"` so applying/exporting the scene will not silently drop them. Its response includes the same
> `requestedCount`, `validatedCount`, `filteredCount`, `filteredItems`, `adjustedCount`, `adjustedItems`,
> `rawCandidateCount`, `inspectedCount`, and `truncatedCount` feedback for generated
> devices/environment entries/rules/specs. `count` is the number of items in the final
> scene, including required environment variables; `requestedCount` is only the sum of
> the requested device/rule/specification limits. `validatedCount` counts inspected raw
> candidates that were kept, while `adjustedItems[]` reports deterministic defaults or
> missing required environment entries added to make the scene complete as
> `{ type, index?, reasonCode, reason, label?, appliedValues }`. These adjustments are
> distinct from rejected `filteredItems` and uninspected `truncatedCount`. Because a
> missing required environment entry can be synthesized rather than accepted from the
> raw AI output, scenario `count` is not required to equal `validatedCount`; clients
> verify `count` against `scene.devices + scene.environmentVariables + scene.rules +
> scene.specs` instead. The raw-candidate identities still use `validatedCount`.
> The response carries authoritative `objectiveStatus=COMPLETE|PARTIAL` and ordered
> `objectiveIssues[]` (`{ code, message }`). The controller and frontend recompute these
> fields from the canonical scene: missing devices, automation rules, or specifications
> produce `NO_DEVICES`, `NO_AUTOMATION_RULES`, and `NO_SPECIFICATIONS`, respectively.
> `COMPLETE` means only that all three core item classes are present; it is not a claim that
> the user's prose was satisfied or that formal verification passed.
> The response also carries authoritative `verificationReady` and ordered
> `readinessIssues[]` (`{ code, message }`). The REST controller and frontend recompute
> readiness from the canonical returned scene and reject a mismatch; currently
> `NO_DEVICES` and `NO_SPECIFICATIONS` are the deterministic issue codes. A draft that
> lacks specifications remains reviewable/applicable but is not presented as ready for
> `verify_model`.
> `verificationReady` means only that the retained scene has the devices and
> specifications required by the verification entry point. It does not mean that the
> draft satisfies the natural-language requirement. That separate boundary is exposed as
> ordered `semanticWarnings[]` (`{ code, message }`): `FILTERED_CANDIDATES` reports that
> validation removed generated content, `NO_AUTOMATION_RULES` reports that the retained
> scene establishes no automation loop, and `UNREFERENCED_DEVICES` names retained devices
> that participate in neither a retained rule nor a retained specification. These warnings
> are computed from the final canonical graph, not inferred from the user's prose. The
> returned `rationale` is likewise a backend-generated count summary of retained content;
> model-authored rationale is not passed through after filtering and the summary explicitly
> disclaims requirement satisfaction and formal-verification success.
> A rule API event source normally omits `relation` and `value`. If the AI emits the
> semantically equivalent pair `relation = "="`, `value = "TRUE"`, the backend keeps the
> rule, removes those redundant fields, and returns an `apiEventSyntaxNormalized`
> adjustment. It still rejects partial pairs, `FALSE`, and non-equality relations because
> those do not describe the same event-occurrence semantics.
>
> AI-proposed device ids are one-response aliases used only to bind the generated graph.
> The backend assigns portable `device_1`, `device_2`, ... references and rewrites every
> rule, content source, and specification reference consistently before returning the
> canonical scene. The aliases are not shown as user identity and cannot leak unsafe
> model names into an otherwise valid recommendation. A kept rule/specification is candidate-atomic: if any generated
> rule source, rule content binding, or specification condition fails validation, the whole
> rule/specification is rejected with a `filteredItems[]` reason rather than being returned
> after silently dropping only the invalid nested item. If validation removes every generated device, the
> response keeps an empty canonical `scene` and returns a no-applicable-scene message
> instead of reporting a complete scenario. Prefix-like business names such as `a_noise`, `trust_score`,
> `privacy_level`, or `variable_mode` stay literal in the returned scene; generated NuSMV
> identifiers remain an internal modeling detail.
> Candidate validation also intersects conditions within each rule and each A/IF/THEN
> specification group. Individually legal predicates that have no common declared state
> or variable value are rejected as a whole. Rule target-device predicates must also
> intersect the command API's non-empty `StartState`. These stricter checks apply to
> AI-authored candidates/mutations; ordinary user Board persistence keeps its existing
> structural authoring contract.

Standalone recommendations run in a bounded dedicated executor. Only one is admitted per user;
pool saturation returns `503`. While a request is active, its status DTO is
`{ requestId, state, stage, elapsedMs }`. `state` is `WAITING`, `RUNNING`, or briefly
`FINISHED`; `stage` is one of
`QUEUED`, `RUNNING`, `PREPARING_CONTEXT`, `REQUESTING_MODEL`, `VALIDATING_RESULT`, or
`CANCELLING` for this workflow. The UI polls this endpoint and shows the submitted Board-context
counts, selected tool, elapsed time, and the actual server-observed stage. It does not infer a
phase from elapsed time, and these operational stages are not hidden model reasoning. Stop and
panel-close actions call the cancellation endpoint before aborting the browser request.
Owner, status, and cancellation records are token-fenced in Redis, so another backend
instance can observe and stop the accepted request without allowing an expired worker to
overwrite a reused id. Active records renew for the callable's lifetime and the final status
is retained briefly. Redis failure falls back to process-local tracking; a different instance
cannot see that local execution, so clients use a fresh random request id for every attempt.

After a stop action the Board keeps the workflow visibly stopping until status reports
`FINISHED`. A first `404` can be a registration-versus-cancellation race and is not treated
as proof of completion. Five consecutive unavailable status reads end local polling with a
visible outcome-unknown warning, preventing both a false success claim and an endless spinner.
Recommendation prompts use a compact capability projection; the complete template manifests
remain server-side for authoritative validation.

If the AI provider's whole response is malformed JSON or lacks the required
recommendation/scene arrays, recommendation endpoints return HTTP `502` through
`BadGatewayException` (`AI_RESPONSE_INVALID` at the tool boundary). This is distinct
from a valid response whose individual candidates were rejected through
`filteredItems`, and from a valid empty recommendation set.
The same HTTP-502 behavior applies to an unusable AI similarity response; the endpoint
does not degrade it to `isSimilar=false`. A duplicate must also be marked similar. Both
rule-check endpoints and the frontend reject missing required fields, non-numeric or
out-of-range scores, and wrong field types instead of interpreting them as a clear check.
