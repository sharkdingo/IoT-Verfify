# Board Storage & Recommendation API

Field-level contract for `/api/board` — the persisted canvas (nodes, edges, rules,
specs, layout, active tabs), device templates, and AI-backed recommendation endpoints.
The `Result<T>` envelope, auth, and error codes are defined in
[overview.md](overview.md).

All endpoints are authenticated and scoped to the current user (`@CurrentUser`).
Verified against code on 2026-07-03. Source:
`service/impl/BoardStorageServiceImpl.java`, `controller/BoardStorageController.java`,
`dto/device/`, `dto/board/`, `dto/rule/`, `dto/spec/`.

**Write strategy differs by collection — this matters:**

- `nodes`, `edges`, `specs` are **full replace** (`deleteByUserId` + `saveAll`): the
  request body becomes the entire stored set, and server-assigned ids are regenerated.
- `rules` is an **incremental upsert** (`saveRules`): a `RuleDto` with an `id` updates
  that rule in place (preserving its original `createdAt`); a `RuleDto` without an `id`
  is inserted; existing rules whose id is absent from the request are deleted. An `id`
  that belongs to another user is ignored and inserted as a new rule.

  *Why it is not full-replace:* rule identity must be stable across saves — `createdAt`
  is preserved, and fault localization keys off the rule's position/id (see
  [../architecture/auto-fix.md](../architecture/auto-fix.md)). A delete-and-recreate
  would churn ids and break both. When editing a rule client-side, send its existing
  `id` back; do not drop it.

---

## Canvas storage

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/nodes` | → `DeviceNodeDto[]` | List device instances |
| POST | `/api/board/nodes` | `DeviceNodeDto[]` → `DeviceNodeDto[]` | Full replace |
| GET | `/api/board/edges` | → `DeviceEdgeDto[]` | List connections |
| POST | `/api/board/edges` | `DeviceEdgeDto[]` → `DeviceEdgeDto[]` | Full replace |
| GET | `/api/board/rules` | → `RuleDto[]` | List rules |
| POST | `/api/board/rules` | `RuleDto[]` → `RuleDto[]` | **Incremental upsert** (see write-strategy note above) — send existing `id`s back |
| GET | `/api/board/specs` | → `SpecificationDto[]` | List specs |
| POST | `/api/board/specs` | `SpecificationDto[]` → `SpecificationDto[]` | Full replace |
| GET | `/api/board/layout` | → `BoardLayoutDto` | Panel/canvas layout |
| POST | `/api/board/layout` | `BoardLayoutDto` → `BoardLayoutDto` | |
| GET | `/api/board/active` | → `BoardActiveDto` | Active tabs |
| POST | `/api/board/active` | `BoardActiveDto` → `BoardActiveDto` | |

### `DeviceNodeDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `id` | `String` | Required |
| `templateName` | `String` | Required |
| `label` | `String` | Required |
| `position` | `{ x: Double, y: Double }` | Required |
| `state` | `String` | Required (`@NotBlank`) — see the InitState fallback note in `CHANGELOG.md` (2026-03-04) |
| `width` / `height` | `Integer` | Required |
| `currentStateTrust` | `String` | Optional; `trusted` / `untrusted` |
| `variables` | `VariableStateDto[]` | Optional; `{ name, value, trust }` |
| `privacies` | `PrivacyStateDto[]` | Optional; `{ name, privacy }` |

> `DeviceNodeDto` is the canvas-CRUD shape (includes UI layout). The verification path
> uses the leaner `DeviceVerificationDto` — see
> [verification.md](verification.md).

### `DeviceEdgeDto`

`{ id, from, to, fromLabel, toLabel, fromPos: {x,y}, toPos: {x,y} }` — all required.

### `RuleDto` / `SpecificationDto`

Defined in [verification.md](verification.md) (they are shared with the verification
request).

### `BoardLayoutDto`

`{ input: PanelPosition, status: PanelPosition, canvasPan: {x,y}, canvasZoom: Double,
dockState: { input: DockState, status: DockState } }`, where `PanelPosition` is
`{x, y}` and `DockState` is `{ isDocked: Boolean, side: "left"|"right"|"top"|"bottom"|null,
lastPos: PanelPosition }`.

### `BoardActiveDto`

`{ input: String[], status: String[] }` — both required (`@NotNull`); the lists of
active tab ids.

---

## Device templates

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/templates` | → `DeviceTemplateDto[]` | The current user's templates |
| POST | `/api/board/templates` | `DeviceTemplateDto` → `DeviceTemplateDto` | Create a custom template (runs a NuSMV probe pre-check) |
| DELETE | `/api/board/templates/{id}` | → `null` | Delete one template |
| POST | `/api/board/templates/reload` | → `Integer` | **Reset**: delete the user's templates, re-import defaults; returns the imported count |

### `DeviceTemplateDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `id` | `Long` | Null on create; assigned by DB |
| `name` | `String` | Required |
| `manifest` | `DeviceManifest` | Required |

`DeviceManifest` uses **PascalCase** JSON keys (`@JsonProperty`): `Name`,
`Description`, `Modes`, `InternalVariables`, `ImpactedVariables`, `InitState`,
`WorkingStates`, `Transitions`, `APIs`, `Contents`. Key nested shapes:

- `InternalVariable`: `Name`, `Description`, `IsInside`, `PublicVisible`, `Trust`,
  `Privacy`, `LowerBound`, `UpperBound`, `NaturalChangeRate`, `Values`. **Provide either
  `Values` (enum) XOR `LowerBound`+`UpperBound` (numeric range), or neither — never
  both, and never only one bound** (backend `@AssertTrue isValidVariableDefinition`).
- `WorkingState`: `Name`, `Description`, `Trust`, `Privacy`, `Invariant`, `Dynamics[]`
  (`Dynamic` = `VariableName`, `Value`, `ChangeRate`).
- `API` / `Transition`: `Name`, `Description`, `Signal`, `StartState`, `EndState`,
  `Trigger` (`Attribute`, `Relation`, `Value`), `Assignments[]` (`Attribute`, `Value`).
- `Content`: `Name`, `Privacy`, `IsChangeable`.

The manifest constraints that matter for NuSMV (identifier legality, StartState/EndState
format, trust/privacy values) are enforced by validation — see
[../architecture/nusmv-model.md](../architecture/nusmv-model.md) and the P1–P5 rules in
[../architecture/spec-templates.md](../architecture/spec-templates.md). In particular,
`Trust` must be `trusted` or `untrusted` and `Privacy` must be `public` or `private`
(case-insensitive; P4) — other values are rejected at generation time. Default template
JSON lives in `backend/src/main/resources/deviceTemplate/`.

---

## Recommendation & duplicate check

These delegate to AI tools (see [ai-tools.md](ai-tools.md)). They return
`Result<Map<String, Object>>`; an AI-tool error is translated to the matching HTTP
status by `throwIfToolError`.

| Method | Path | Query / Body | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/rules/recommend` | `maxRecommendations` (default 5), `category` (default `all`) | AI rule recommendations |
| GET | `/api/board/specs/recommend` | `maxRecommendations` (default 5), `category` (default `all`) | AI specification recommendations |
| POST | `/api/board/devices/recommend` | body: `{ devices, templates }` (Map) | AI device recommendations |
| POST | `/api/board/rules/check-duplicate` | body: `RuleDto` | AI duplicate-rule check; frontend integrated in `RuleBuilderDialog` as an optional manual pre-save check (non-blocking) |

> For the `devices/recommend` body, the frontend maps template fields to lowercase
> camelCase keys (`variables`, `apis`, `workingStates`) — see
> [../guides/frontend-integration.md](../guides/frontend-integration.md).
