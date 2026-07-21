# Frontend Integration Guide

How the Vue 3 frontend calls the backend: the HTTP client, the API modules and their
real shapes, SSE streaming, and where the TypeScript types live. This replaces the
old `frontend/API-DOCUMENTATION.md`, which had drifted from the code.

Verified against code on 2026-07-22. Source: `frontend/src/api/`,
`frontend/src/types/`, `frontend/src/components/ChatView.vue`,
`frontend/src/views/Board.vue`, `frontend/src/App.vue`, and `frontend/src/router/index.ts`.

---

## Directory layout (actual)

```
frontend/src/
├── api/
│   ├── http.ts          # Axios instance (interceptors, unpack lives in board.ts)
│   ├── auth.ts          # authApi — auth calls
│   ├── board.ts         # default-export object: board CRUD + verification + fix
│   ├── chat.ts          # named exports: sessions + SSE streaming
│   ├── rules.ts         # rule recommendation only (persistence lives in board.ts)
│   ├── simulation.ts    # default-export object: simulation calls
│   └── fuzzing.ts       # default-export object: bounded exploration tasks/runs/findings
└── types/
    ├── auth.ts   canvas.ts   chat.ts   device.ts   edge.ts   fix.ts
    ├── fuzzing.ts   node.ts   rule.ts   simulation.ts   spec.ts   verify.ts
```

> There is **no** `api/verify.ts` and **no** `types/trace.ts`. Verification calls live
> in `board.ts`; trace types (`Trace`, `TraceState`, `TraceDevice`, …) live in
> `types/verify.ts`.

---

## HTTP client — `api/http.ts`

Axios instance:

- `baseURL: (import.meta.env.VITE_API_BASE_URL || '') + '/api'`
- `timeout: 100000` (100 s)
- Request interceptor: attaches `Authorization: Bearer <token>` from the auth store.
- Response interceptor: on HTTP `401`, clears auth state and redirects to the landing
  page's integrated login panel: `/?mode=login`. If the user was on a protected route,
  it also adds `redirect=<current fullPath>` so a successful login can return them to
  that route. Standalone `/login` and `/register` routes were removed during the
  landing-page consolidation; do not reintroduce compatibility routes during the
  current development phase.

> **Base URL is uniform and relative by default.** Both `http.ts` (axios, most modules)
> and `chat.ts` (SSE) derive their base URL from `import.meta.env.VITE_API_BASE_URL`.
> When it is empty (the default), requests go to a relative `/api`, which the Vite dev
> server proxies (`vite.config.ts`) and a production reverse proxy (Nginx) forwards —
> so dev and same-origin prod work with no config. Set an absolute
> `VITE_API_BASE_URL` only for cross-origin deployments. See
> [../getting-started/configuration.md](../getting-started/configuration.md#frontend-vite).

The endpoint columns below are **client-relative** paths passed to this axios instance
(`/auth/login`, `/board/nodes`, and so on). The actual HTTP paths on the backend include
the `/api` prefix, for example `/api/auth/login`; the authoritative backend index is
[../api/rest-endpoints.md](../api/rest-endpoints.md).

Current routes are deliberately small: `/` is the public landing page with integrated
login/register modes, `/board` is the authenticated application, `/404` is public, and
all unknown routes redirect to `/404` under hash history. Direct non-hash URLs are
normalized to hash URLs during app startup.

---

## Response unwrapping — two conventions

The backend wraps everything (except SSE) in the `Result<T>` envelope (authoritative
definition: [../api/overview.md](../api/overview.md)). What this guide owns is that the
frontend does **not** unwrap it uniformly:

| Module | Returns | Caller must read |
| :--- | :--- | :--- |
| `board.ts`, `simulation.ts`, `fuzzing.ts`, `rules.ts` (rule recommendation only) | already-unwrapped `T` (via a local `unpack` that returns `response.data.data`) | the value directly; targeted rule mutations map backend `RuleDto` values back to `RuleForm` and return the authoritative current collection |
| `auth.ts` | the full `Result<T>` (returns `response.data`) | `.data` for payload endpoints, `.code` for status; void responses may omit `data` |

So `authApi.login(...)` resolves to `Result<LoginResponse>` — after confirming
`result.data` exists, read `result.data.token`, **not** `result.token`. This asymmetry
is real; mirror it in components.

---

## Auth — `api/auth.ts`

Exported as an object `authApi` (not named functions):

| Method | HTTP | Endpoint | Returns |
| :--- | :--- | :--- | :--- |
| `authApi.login(data)` | POST | `/auth/login` | `Result<LoginResponse>` |
| `authApi.register(data)` | POST | `/auth/register` | `Result<RegisterResponse>` |
| `authApi.logout()` | POST | `/auth/logout` | `Result<void>` |
| `authApi.deleteAccount(data)` | DELETE | `/auth/account` | `Result<void>` |

`LoginResponse` carries `userId`, `phone`, `username`, `token` (all camelCase). See
[../api/overview.md](../api/overview.md) for the general `Result<T>` envelope,
and the backend `dto/auth/` for request field rules. Login uses `identifier`
(phone number or username) plus `password`; registration still validates phone,
username, and password separately.
`deleteAccount` sends `{ password, confirmation }`; the backend requires the password
to match and `confirmation` to equal the current username or phone number. On success,
clear local auth state and send the user back to the landing page.
`logout` only revokes the current token; background verification/simulation/exploration tasks are
not cancelled. `deleteAccount` is the destructive path: it cancels active tasks,
serializes in-flight writes with account deletion, and removes user-owned data.

Example:

```ts
import { authApi } from '@/api/auth';

const res = await authApi.login({ identifier: 'testuser', password: '123456' });
if (res.code === 200) {
  const { userId, token } = res.data; // note: res.data, not res
}
```

---

## Board + verification + fix — `api/board.ts`

`board.ts` default-exports one object that covers board CRUD **and** verification/fix.
Its methods return already-unwrapped values. Non-exhaustive:

- Board CRUD: `getNodes`/`addNodes`/`updateNodeLayout`/`updateNodeRuntime`/
  `renameNode`/`deleteNode`,
  `getSpecs`/`addSpec`/`removeSpec`, `getRules`/`addRule`/`removeRule`, and
  `getLayout`/`saveLayout`. Visible canvas connections are derived from `rules`; there
  is no persisted edges API.
  `BoardLayoutDto` owns both canvas pan/zoom and panel UI state
  (`panels.control` / `panels.inspector`: collapsed, width, active section); there is no
  separate active-tabs API.
- Templates: `getDeviceTemplates`, `getDeviceTemplateSchema`, `addDeviceTemplate`,
  `deleteDeviceTemplate`, `previewDefaultTemplateReset`, `resetDefaultTemplates`. Use
  `DeviceTemplateDto.defaultTemplate` to group default vs custom types. Reset is a
  two-step command: render the preview's itemized type/device/environment effects and
  blockers, then submit its `impactToken`. Reconcile both `currentTemplates` and
  `environmentVariables` from the committed response; do not infer success from a count.
- Control Center template UI is split into **Create Template** and **Template Repository**.
  Clicking a template card opens its detail preview; dragging a template card to the
  canvas opens a device-instance naming dialog and only saves after confirmation.
- Clicking a canvas device opens the device detail/runtime dialog. Its visible instance
  actions include rename and confirmed delete; rename must not depend on discovering a
  hidden mouse gesture. Mouse right-click opens the same device context actions, while
  the Context Menu key or `Shift+F10` provides the keyboard equivalent. Runtime edits
  (`state`, `currentStateTrust`, `currentStatePrivacy`, device-local `variables`, and
  device-local `privacies`) use the same validation helpers as single-device creation and JSON/CSV
  import, then replace the complete runtime subresource through
  `PUT /board/nodes/{nodeId}/runtime`. Moving/resizing uses the separate complete layout
  subresource at `PUT /board/nodes/{nodeId}/layout`. The Board serializes create, layout,
  runtime, rename, and confirmed-delete calls before applying their authoritative
  `currentNodes` snapshots; a late response therefore cannot roll back a later device
  action. Environment
  variables are not device runtime fields; edit their shared value/trust/privacy through
  `/board/environment`. Submit only the changed non-null fields; omitted/null fields are
  preserved, not reset.
- Device creation supports single, batch, and JSON/CSV import modes in the Devices tab.
  Batch/import are frontend conveniences over the targeted `addNodes` contract: parse,
  preview, generate unique labels, then append the accepted devices once. Device create,
  layout/runtime/rename/delete, rule/spec create/delete/reorder, Environment Pool edits,
  device-type import/delete/default reset, and confirmed scene replacement share one
  client-side mutation queue. Each operation applies its authoritative response or
  completes error reconciliation before the next request starts, so an older collection
  response cannot overwrite a newer local action. This is frontend response ordering,
  not a claim that separate ordinary REST calls form one transaction; only one batch
  replacement request is atomic as a group.
  Every successful axios mutation of Board semantics and every completed assistant Board
  refresh publishes a same-user `BroadcastChannel` invalidation. Receiving tabs enqueue one
  coalesced full semantic snapshot refresh through that same mutation queue; an invalidation
  received while hidden or while another refresh is running remains pending. Visibility and
  focus refreshes remain as the compatibility/recovery path when `BroadcastChannel` is not
  available. This reconciles device, template, Environment Pool, rule, and specification
  changes made in another tab without overwriting the current tab's pending mutation;
  initial mount, manual retry, and invalidation reads all use the same coordinator. A delayed
  initial response must complete before the pending invalidation fetch begins, so it cannot
  arrive after and overwrite a newer cross-tab snapshot.
  persisted canvas/panel layout remains a separate concern. Read-only POST checks such as
  rule duplicate/similarity validation do not publish invalidations.
  The UI generates an opaque stable `DeviceNode.id` independently of the user-visible
  label. Renaming a device therefore never changes rule/spec identity, and labels are
  compared case-insensitively without applying NuSMV normalization rules to what the
  user sees. Single creation and rename keep the exact typed label and block a conflict;
  they do not commit an unconfirmed suffix. Batch/import deliberately allocate unique
  suffixes in the visible preview, then abort the whole append if the current Board has
  drifted and those previewed names are no longer available.
  Device import accepts either one JSON object or a JSON array with
  `template`/`templateName`/`type` plus `name`/`label`/`deviceName`, or CSV/tab-separated
  rows with two columns: template name, device name. A `template,name` header is optional.
  JSON rows may also include `state`, `currentStateTrust`, `currentStatePrivacy`, `variables[{name,value,trust}]`,
  and `privacies[{name,privacy}]`; these are validated against the selected template
  with the same runtime semantics used by single-device creation and backend board saves.
  Any other top-level or nested JSON field rejects that row and is named in the preview;
  it is never ignored as optional metadata. CSV continues to accept exactly two columns.
  `IsInside=true` local variables are saved on the created
  device instance. Environment variables declared by the selected template are split out
  of the imported row and sent as environment patches in the same atomic device-create
  request; they are not stored on the
  node. Variables affected only through `ImpactedVariables` are created by the environment
  pool self-heal path and are edited from the Environment Pool.
  Missing template names, unknown templates, missing device names, malformed JSON, malformed
  quoted CSV, extra CSV columns, invalid runtime state/trust/privacy/variable values, and
  duplicate runtime overrides are shown in the preview and disable creation. Duplicate
  device names are made unique in the preview (for example `ac` -> `ac_1`) and remain
  creatable. If two JSON rows provide different value, source, or sensitivity fields for
  the same scene-shared environment variable, the preview names both rows and disables
  the whole batch; identical or complementary fields merge. When batch creation includes
  environment-variable patches, the backend
  appends the devices and updates the environment pool in one transaction.
- Scene import/export lives in the Board header as a whole-board portability affordance,
  not as a backend endpoint. Export requests a browser download for an
  `iot-verify.board-scene` JSON file with
  exact `schema`, `version: 4`, referenced `templates`, `devices`,
  `environmentVariables`, `rules`, and
  `specs`; there is no timestamp inside the JSON because scene files are meant to be
  canonical and round-trip comparable. The toast reports that the download was requested,
  not that the browser or file system completed it; device-template JSON export uses the
  same wording. Export sorts templates/devices/environment and
  object keys into a stable order, but preserves authored arrays such as `rules[]`, rule
  `sources[]`, `specs[]`, and spec condition lists because order participates in rule
  precedence and preserves the user's authored semantics. Public fix localization uses
  stable adjustment ids rather than array positions. Rule ids are omitted so an imported scene
  creates fresh backend rows, as do specifications; only stable device ids are preserved.
  Import rejects a missing/different schema or any unsupported version instead of
  guessing aliases and rewriting future data into version 4. It validates duplicate
  device ids, required identity/position/size, state required only for state-machine
  templates, state forbidden for stateless templates, required rule target command fields
  (`toId`/`toApi`), supported relation operators, specification template condition-side
  shape, and rule/spec device references in the browser, then sends the
  standard JSON template snapshots and complete board collections to `/board/batch`.
  Before showing the destructive confirmation it calls `/board/replacement-preview` and
  displays the authoritative current server counts. The confirmed request carries that
  opaque `impactToken`; a `BOARD_REPLACEMENT_STALE` 409 means nothing was replaced, so
  refresh and require another confirmation rather than retrying automatically. The batch
  API has no null-means-preserve form: all four semantic collections and the exact
  template dependency array are required.
  Geometry validation is shared with the persisted canvas contract: finite coordinates
  are limited to `-1000000..1000000`, width to `80..2000`, and height to `60..2000`.
  This exact domain also applies to AI scene drafts, preserving export/import closure at
  the range boundaries.
  The canvas may hold `Working` as a stateless rendering placeholder, but version 4 export
  omits it together with current-state trust/privacy; import restores it only internally.
  Specification `templateLabel`, formula/device caches, and condition display metadata
  are excluded and rebuilt from `templateId` plus conditions. The environment pool is
  exact: every variable required by the referenced templates must appear once with
  explicit trust/privacy labels; missing, duplicate, or unknown entries reject import
  before confirmation.
  A scene is self-contained: it must carry exactly one matching snapshot dependency for
  every referenced template and no unreferenced snapshot. The backend enforces that rule
  even when the target account already has the template, atomically rejects same-name
  manifest mismatches, creates only missing referenced templates, validates the exact
  submitted environment pool, and saves nodes, environment, rules, and specs. A failed import does not trigger a client-side
  compensating write, because the server transaction leaves the prior scene intact.
  The response reports `createdTemplates` so the UI can state any template side effect
  explicitly. The Board header also exposes **Clear Scene**, which saves empty
  nodes/rules/specs and an empty environment pool through the same batch authority. Its
  destructive confirmation explicitly states that the device-template catalog, run
  history, and AI conversations are outside the scene and remain intact.
  A `422 ValidationException` carries every field problem under `data.errors`. A single
  problem uses the compact toast; multiple scene problems open a diagnostic list with
  user-facing item coordinates plus the JSON field path. No failed validation mutates
  the current scene.
- Recommendation: `recommendRelatedDevices`, `recommendSpecifications`, and
  `recommendScenario`. `recommendScenario` returns a canonical, importable but unverified
  `iot-verify.board-scene` draft for the Action Dock scene workflow; applying it should use the same scene-import
  path as file import so template checks, environment-pool validation, atomic batch
  saves, and user-visible template creation stay identical. Device recommendations return
  instance proposals with an effective `suggestedLabel`, optional advisory
  `intendedUse`/`suggestedPlacement`, and materialized local runtime values. Omitted
  trust/privacy fields remain template fallbacks rather than copied instance overrides. The two
  advisory fields explain recommendation context but are not persisted device fields or
  formal-model inputs. Omitted template defaults are listed in
  `adjustedItems` and must be shown before application; explicitly invalid runtime values
  reject the whole candidate. Apply them as device instances, not merely as template badges.
  Before creation, show any currently missing Environment Pool names required by the
  selected template; after creation, reconcile and display the server's authoritative
  itemized environment changes.
  Rule recommendation `name` is the exact display name persisted on apply. Specification
  recommendation `rationale` is explanation only; applying persists `templateId` and
  structured conditions. Neither candidate type exposes `priority`: relevance is return
  order, while rule precedence remains the Board's explicit execution order and every
  specification is checked. Treat a missing name/rationale as an incomplete response.
  The scene tool's LLM device ids are temporary aliases. The backend returns portable
  `device_1...` ids after rewriting every rule/spec/content dependency, reports rejected
  candidates in `filteredItems`, and reports deterministic defaults or inserted required
  environment values separately in `adjustedItems`; the panel shows both categories
  before the user confirms full scene replacement. The REST scene type is the exact
  portable shape, not a reuse of broader Board DTOs, so serialization cannot add null
  template ids/flags, condition display caches, or state-label fields that file import
  would reject. Optional rule titles stay optional and never cause a semantically valid
  AI rule to be filtered.
- Device creation: manual creation, device-list JSON import, standalone AI device
  recommendation, and assistant `add_device` all materialize the same template-local
  starting state/variable values. The shared `materializeDeviceRuntimeConfig` helper
  overlays explicit values and label overrides while leaving omitted trust/privacy
  labels template-owned. In device-list
  JSON, omitted or `null` scalar fields select defaults; blank strings are validation
  errors. Standard scene files carry explicit persisted overrides; omitted labels continue
  to resolve from the imported template.
  Device display names are case-insensitively unique in every entry path. Manual creation
  blocks a conflict; batch/JSON import shows the exact suffix in its preview; an AI
  recommendation asks the user to confirm the exact available name before writing. If
  that name conflicts again while queued, creation aborts instead of adding another
  unconfirmed suffix.
- Recommendation application has separate processing and committed states. A rule,
  device, or specification candidate says "Applying, not confirmed yet" while its
  validation/similarity gate or persistence request is outstanding. It says "Added to
  board" only after the authoritative response, or after reconciliation proves the item
  exists. Application state is scoped to the recommendation response epoch, so a late
  completion cannot mark the same array position in a regenerated list.
- Scene import/clear acquires an interaction lock before showing its destructive
  confirmation and after earlier Board writes drain. Confirmation counts therefore
  describe a stable Board; live edits, new assistant requests, verification, and
  simulation stay blocked through response reconciliation. A streaming assistant must
  stop or finish first because aborting SSE cannot revoke a tool call already started.
- Verification: `verify(req)`, `verifyAsync(req): Promise<VerificationTask>`, `getTasks`,
  `getTask`, `getTaskProgress`, `cancelTask`, and trace list/detail/delete.
- Counterexample exploration: `fuzzingApi.getCurrentModelFingerprint()`,
  `startAsync(req)`, task polling/cancellation, run list/detail/delete, and lazy finding
  detail. The accepted task is authoritative; the client never sends a Board/model
  payload or fabricates a task ID.
- Fix: `getFaultRules(traceId)`, `fixTrace(traceId, request?)`.

> **`verifyAsync` signature**: `verifyAsync(req): Promise<VerificationTask>` — it takes
> only the request and resolves to the authoritative accepted task. The client reads the
> server-generated `task.id`, persisted `status`/`progress`, and frozen `modelSnapshot`;
> it does not fabricate a local task row or pass an id in. Acceptance is not completion.
> If this promise rejects with validation (`400` DTO errors or `422` service/runtime
> errors) or service-unavailable errors, no pollable task id exists for the UI flow;
> show the submit error and do not start polling.

Rules sent through `addRule`, `checkDuplicateRule`, `verify`, or `simulate` must have
at least one concrete trigger source. The frontend stores new rule source/target device
references as canonical board node ids, and `board.ts` maps them to backend
`RuleDto.conditions` / `command`. `RuleSource.itemType` is required and maps directly to
backend `targetType`.
Before `verify`, `verifyAsync`, `simulate`, or `simulateAsync`, the board request
builder converts those board node ids to model `varName` values for devices, rules, and
specifications, filters device runtime fields to local variables only, and sends the
current `/board/environment` values as top-level `environmentVariables`. Do not send raw
board ids directly to model endpoints, and do not put environment values into
`devices[].variables`.

The rule builder must keep source conditions and target commands separate. Source
`itemType="api"` is a signal event and should list only template APIs with
`Signal=true`, without relation/value fields. Target commands may list all template
APIs because they are actions invoked by the rule.
Selecting or filling a source edits a draft row only. Add it to the rule after an
explicit **Add source** action (or Enter from the value field); selection changes and
field blur must not silently commit a trigger while the same explicit action remains
visible.
Content sensitivity is a separate optional rule input and is shown only after the chosen
target API declares `AcceptsContent=true`. Changing the target device/action to one that
does not accept content clears both content fields; hidden stale values must never be
submitted. The selected source item contributes only its `public`/`private` label, not
payload bytes or a guarantee of delivery.

For value-based rule/spec conditions, dialogs should use canonical relations
`=`, `!=`, `>`, `>=`, `<`, `<=`, `in`, and `not in`. Enum-like mode/state/API/trust/privacy
conditions should expose only `=`, `!=`, `in`, and `not in`; numeric variables should expose
those operators plus ordering comparisons. Enum-like sets can serialize as comma-, semicolon-, or pipe-separated values. Multi-mode
`state` options are full tuples such as `home;idle`; therefore state sets must serialize
tuples with comma or pipe separators, for example `home;idle,sleep;idle`, so the
semicolon remains part of the tuple rather than a list delimiter.
REST and AI entry points also accept relation aliases such as `EQ`, `GTE`, and
`NOT_IN`, but storage and model requests are normalized back to the canonical values
above. Frontend controls should keep emitting canonical values so users see one stable
vocabulary.

`addRule` and `removeRule` return `CollectionMutationResult<RuleForm>` with the exact
affected rule plus the authoritative current collection. Callers replace local rule
state with `currentItems` so temporary ids are exchanged for stable server ids and
concurrent changes are not erased. Omitted rules are never interpreted as deletions.

The inspector presents the returned list as execution order. If multiple enabled rules
command one device mode in the same model step, the first matching rule wins for that
mode. Up/down controls send the complete current id order to `PUT /board/rules/order`;
the server rejects duplicate, partial, or stale lists and returns the authoritative
ordered rules. Search disables reordering because a filtered subset is not a complete
semantic order. This targeted command preserves rule ids and never uses `/board/batch`.
After a reorder, the UI states that model behavior may have changed and verification
must be run again.

Board layout and visual shell rules:

- Persist user layout through `BoardLayoutDto.panels` plus `canvasPan`/`canvasZoom`.
  Do not reintroduce a separate active-tabs endpoint.
- Treat the persisted layout as the wide-screen workspace. At narrow widths, collapse
  both side panels locally, fit the current nodes into the available canvas, keep a
  permanent 44px fit control reachable, and do not overwrite the saved pan/zoom or
  panel state. Restore that saved wide layout when the viewport widens again.
- Treat node positions as canvas world coordinates. Keep node geometry in pixels, but
  make surrounding UI chrome responsive with CSS grid/flex, `clamp()`, `dvh/dvw`, and
  board-level CSS variables.
- Canvas devices use three information-density tiers derived from on-screen node size:
  compact nodes show the icon only, medium/default nodes show icon + name + state, and
  expanded nodes show runtime chips. The default 176x128 node size should be large
  enough for the detailed tier at normal zoom, and the whole node is the detail-opening
  target; do not add a second detail button inside the node.
- Paint the grid on the viewport-sized canvas shell and offset it from `canvasPan` /
  `canvasZoom`; do not paint it on a finite transformed inner layer, otherwise users
  will see grid edges while panning an infinite canvas.
- Board surfaces, cards, forms, timelines, mini task indicators, and history panels use
  semantic CSS tokens from `base.css` / `board.css`. Prefer `board-surface-panel`,
  `board-card-surface`, `board-muted-surface`, and `board-segmented` over one-off
  `dark:` utility chains.
- Keep the entity model discoverable: `ControlCenter` owns the detailed create/edit
  forms, while `SystemInspector` owns the current-board lists. The inspector uses
  device/rule/specification tabs rather than one long stacked list, and each tab keeps
  a local add action that opens the matching control-center form. The visible entity
  section has a consistent collapsible header, a local search field, and filtered/total
  counts; rule/spec searches must match rule/spec semantics (conditions, actions,
  formulas, operators, values, and related devices), not only device names. Persist both
  active sections in `BoardLayoutDto.panels`.
- Timeline controls are bottom-centered between the side panels. When a trace or
  simulation animation is visible, viewport calculations reserve bottom space so
  fit-to-content and center-selection do not place nodes under the timeline. The
  timeline supports both explicit jump controls and direct track clicks; playback
  and manual jumps must update the same selected state so node, edge, and
  environment-variable highlights stay synchronized. Playback is a read-only view of
  saved model-trace data: node state must never fall back to the current Board value.
  Current Board devices absent from the saved trace remain only as dimmed spatial
  context and are identified as not represented. Live device details/editors are not
  opened from playback because they describe the current Board, not the saved state.
  A background result must remain in run history instead of forcing playback over an
  editor that the user is actively using. Keep playback controls and the selected-state
  delta in the first visible layer. Frozen-snapshot/model-scope explanations belong in
  a collapsed run-scope section, while incomplete-model, shortened-horizon, and current-
  Board drift warnings remain visible because they change how the trace may be
  interpreted. Simulation run details must report `states.length`, actual `steps`, and
  `requestedSteps` separately (`states = steps + 1` when parsing is complete); execution
  logs, per-state tables, and raw NuSMV output are diagnostic sections opened on demand,
  not the primary playback surface.
- Canvas rule edges are derived from `rules` whenever either nodes or rules change.
  Do not cache or persist edge rows. Keep edge labels hidden by default and reveal
  them on hover/focus through the SVG hit area so dense boards stay readable while
  keyboard users can still inspect each connection. During trace playback, edge
  highlighting must use backend `TraceStateDto.triggeredRules` stable rule snapshots.
  Do not re-evaluate conditions in the browser or depend on generated event-signal names.
  During playback, reserve animation for the delta that produced the selected state:
  changed devices receive a localized highlight, while a separate draggable change
  panel shows their user-facing before/after values and security-label changes. Do not
  place the full delta inside a device node: compact nodes can hide it or let it cover
  neighboring content. Backend-reported delivered rules emphasize their edges with
  command flow, while compromised delivery points remain static and red. Unchanged trace
  devices retain quiet context instead of pulsing continuously. Use the same semantic
  device comparison for the canvas and the change panel, including mode, compromise,
  trust, and privacy changes. Cross-fade to the selected model value immediately; do not
  keep an old icon/value visible until an animation timer expires. Keep command-flow
  duration shorter than one playback step and honor `prefers-reduced-motion`.
- After creating a device from the manager, drag/drop template dialog, batch import, or
  JSON/CSV import, focus the created device on the canvas and mark the Devices inspector
  row. After creating a rule, focus the created rule's derived edge(s), pan to the
  involved devices, and mark the Rules inspector row. This focus is an orientation aid
  only; it does not open the device detail dialog.
- Device detail semantics come only from the current template catalog response. Do not
  recover a missing manifest from `localStorage` or another browser cache: a stale
  template can contradict the model that verification will build. When the current
  template cannot be resolved, keep the instance identity visible, hide capability and
  formula sections, and ask the user to refresh before editing or interpreting them.
- The canvas map is integrated into the `SystemInspector` overview slot on the right
  side, above the device/rule/specification tabs. It is hidden while simulation,
  verification, history, or recommendation overlays are open so it does not compete with
  task panels or cover important controls. Keep the map compact, theme-aware, and
  neutral; red remains reserved for warnings, violations, and destructive actions.
- The Environment Pool in `SystemInspector` is another overview surface. It groups
  current board variables returned by `/board/environment`, using templates to explain
  which devices read or affect each variable, and displays the user-facing variable name,
  range, shared value, trust, and privacy. Backend-only NuSMV names such as `a_<name>`
  stay out of this UI surface. The component receives the
  persisted environment pool from `/board/environment` and saves each edit as a
  name-keyed field patch. The response must explain every patch with
  `suppliedFields`, `changedFields`, `preservedFields`, and before/after values, and must
  include the authoritative full pool plus any self-heal changes. The UI reconciles from
  that snapshot and says whether the selected field changed; it never rebuilds a whole
  row from possibly stale props. Device creation/deletion triggers a refresh so the backend can insert
  defaulted required variables and prune unneeded ones. The pool is collapsed by
  default to protect inspector scanability, but still shows the variable count and
  a compact name summary. Clicking a source device is a navigation affordance only;
  source devices do not store the environment value. Simulation and verification
  timelines use the same user-facing names from `TraceStateDto.envVariables`; generated
  NuSMV aliases are not displayed or matched as a frontend contract. Runtime NuSMV
  globals such as the actual `compromisedPointCount` are exposed separately through
  `TraceStateDto.globalVariables` so they cannot collide with user environment names.
- The simulation/counterexample-exploration/verification/history/recommendation actions live in a right-side tool
  rail placed just outside the inspector, never overlapping the inspector itself.
- Model-trace playback is one exclusive review surface. While either the simulation
  timeline or counterexample timeline is open, the Action Dock cannot open run history,
  task inbox, run settings, or recommendations; handlers enforce the same guard as the
  disabled controls. Users close the current trace before choosing another saved run.
  Desktop widths show icon+text buttons grouped as run tools and AI suggestion tools;
  narrower viewports collapse the labels but keep `aria-label`, `role="toolbar"`, and
  grouped `role="group"` semantics. Desktop floating panels open to the left of this
  rail so close buttons and form controls are never covered by toolbar hit areas. Do
  not use unexplained red corner badges for active state; prefer the button's selected
  or disabled state and the global task/timeline indicators.
- Stable `data-testid` attributes exist for the board root, side panels, control tabs,
  canvas, canvas map, history panel, mini task indicator, simulation/verification
  panels, recommendation panels, and trace/simulation timelines. Real-browser tests
  should use these instead of localized text.
- `AppErrorBoundary` contains route-view and lazily mounted assistant render failures in
  separate subtrees. Its localized fallback offers a subtree retry and an explicit full-page
  reload; changing routes resets the boundary. Do not move both surfaces behind one boundary,
  because an assistant failure must not remove the Board and a route failure must not prevent
  recovery controls from rendering.
- Recommendation panels must use i18n keys for labels, counts, empty states, and action
  buttons. They are opened in real-browser tests under both English and Chinese locales.
  Rule/spec/device recommendation calls pass the active locale as `language`; backend
  fallback/success messages and LLM natural-language fields should follow that language.
  When recommendation responses include `filteredCount > 0`, surface a neutral validation
  note plus the first few `filteredItems[]` reasons (`type`, 1-based `index`,
  localized `reason`, optional `label`) instead of making the smaller result count look
  like an unexplained failure. When `truncatedCount > 0`, also surface that raw AI
  candidates were not inspected because the requested result limit had already been
  reached.
- Device images should degrade to an inline SVG fallback when a template asset is
  missing or fails to load, so long-running trace animation remains understandable.
- Timeline state chips stay compact for short traces and become horizontally scrollable
  for long traces; do not shrink long timelines until state buttons become unreadable.
  The range input, number input, state chip row, and direct timeline-track click are
  equivalent navigation surfaces and must remain in sync.

Async pattern:

```ts
import boardApi from '@/api/board';

const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));

const submittedTask = await boardApi.verifyAsync(request);
const taskId = submittedTask.id;
let task = submittedTask;

while (true) {
  task = await boardApi.getTask(taskId);               // includes progress + progressStage
  if (task.status === 'COMPLETED' || task.status === 'FAILED' || task.status === 'CANCELLED') {
    break;
  }
  await sleep(2000);
}

// cancel: await boardApi.cancelTask(taskId);
```

Use a serial `while`/`await sleep` loop rather than `setInterval(async ...)` so polling
does not re-enter while a previous request is still in flight. Keep any page-level
`isVerifying`/loading state alive until this loop exits, including the cancelled and
failed terminal states.
When a board view unmounts, stop client-side polling and skip any late state writes.
The backend task should keep running unless the user explicitly calls the cancel API.
For a background-task UI, do not trap the user inside the submit panel. Allow the panel
to close and keep a global mini task indicator visible while active tasks exist. Run
history has two user layers, not three peer artifact tabs:

1. **Task Status** uses `GET /api/verify/tasks`, `GET /api/simulate/tasks`, and
   `GET /api/fuzz/tasks`. These lists contain active work plus failed/cancelled tasks
   that produced no result.
2. **History Results** combines `GET /api/verify/runs`, `GET /api/fuzz/runs`, and saved
   simulation runs from `GET /api/simulate/traces`. One completed run is one top-level
   history item.

Completed work is excluded from the task-status lists. Verification counterexamples are
nested evidence under their owning verification result and keep replay/fix actions;
they are not presented as independent runs. Show `violatedSpecCount` separately from
`counterexampleCount`, because a violated property is not guaranteed to have a
parseable/replayable trace. Failed and cancelled task rows can be dismissed through the
task `DELETE` endpoints; deleting a verification result deletes all of its linked
counterexamples.

Exploration findings are likewise nested under their run, but they are candidate
finite paths rather than NuSMV counterexamples. `FOUND_VIOLATION` is shown as candidate
evidence, `BUDGET_EXHAUSTED` stays neutral and explicitly says it is not a proof, and
`INCONCLUSIVE` names the eligibility/limitation boundary. Finding actions are replay and
formal verification only; never expose Fix for a fuzz finding.
The submit form mirrors the workload and target-selection guard owned by
[the exploration API contract](../api/fuzzing.md#submit-and-task-lifecycle).
Result UI localizes eligibility `reasonCode` and `limitations[]` codes; English backend
diagnostics are reserved for logs or advanced details.

History list calls are summary-only. `GET /api/verify/runs` and `GET /api/fuzz/runs`
already nest lightweight evidence summaries, so the Board must not also fetch global
full-trace/finding lists. Load full verification/fuzz run detail, full trace/finding
states, or full simulation states only when the user opens that result/replay. Keep
`dataAvailable=false` rows visible with a
damaged-history explanation and deletion action, but disable open/replay/fix; one bad
row must not turn the entire history panel into "load failed".
Exploration history requests one bounded page at a time and exposes a localized Load
More action in the exploration filter. Appends are de-duplicated by run ID; deleting a
run resets offset pagination to the first page so shifted rows are not skipped. Exact
page bounds remain owned by [the exploration API](../api/fuzzing.md#run-results).
The Board also reads the current exploration model fingerprint. Fingerprinted history
must have a matching current fingerprint before it is treated as unchanged, so a
temporary fingerprint-read failure is shown as unconfirmed rather than silently falling
back to equal counts. Legacy runs without a fingerprint fall back to the public model
counts and must not be presented as an exact semantic match.

Treat task `status` as execution lifecycle only. A task's direct polling endpoint may
return `COMPLETED` so the submitter can obtain the result, but the history UI then moves
that work to History Results. A violated verification must remain visually red, a
satisfied-but-incomplete run amber, and a complete simulation must say that all rules
entered the generated model rather than imply that the home is safe.
When a task is already being watched through the 1s per-task polling loop, pass
`excludeTaskIds` to the summary-list refresh so the inbox does not fetch and merge the
same task redundantly; keep the locally watched task in the list until the watch loop
ends.
Render the localized `progressStage` returned with each task instead of deriving a phase
from its percentage or elapsed time. Verification, simulation, and exploration stages
are persisted with the percentage by the backend, so one task-detail poll is both more
consistent and cheaper than separate progress and detail requests.

User-facing verification modes should distinguish behavior, not implementation jargon:
synchronous `verify` waits on the current page and returns the result directly;
asynchronous `verifyAsync` creates a pollable task with progress/cancel controls and
task-backed results. The Board defaults verification and simulation to background mode
because it preserves navigation, exposes real phases, and supports cancellation; the
synchronous option remains available when a user deliberately wants to wait in place.
Before verification, simulation, or exploration captures immutable input, the Board waits
for pending fix reconciliation and its mutation queue to drain, then rechecks the current
devices/rules/specifications. Verification/simulation build a client model request;
exploration sends only its budget/target selection and the backend captures the Board.
A run includes edits whose save was already started; later edits cannot rewrite the
captured run snapshot.

Enable the attack option only when the current scene contains an automation rule or a
device-template reading with `FalsifiableWhenCompromised=true`. Otherwise explain that
the scene has no attack surface that can change model behavior; the backend rejects the
same no-op configuration with `422`.
If later Board edits reduce that attack surface below the selected budget, preserve the
user's value and mark the run configuration invalid. Do not silently clamp the budget or
turn attack modeling off; require the user to choose the new limit (or disable the mode)
before submission so the request still expresses their deliberate intent.

Treat attack configuration as run-local, not as a property of the canvas. Verification
offers `ANY_UP_TO_BUDGET` (all modeled combinations up to the chosen limit) and
`EXACT_POINTS` (only the checked device/rule-link points). Simulation offers only
`EXACT_POINTS`; it must never randomly choose compromised points behind the user's back.
Automation-link selections use persisted rule ids, so unsaved rules remain visible but
unavailable for exact selection. Result/history UI reads
`modelSemantics.attackSelectionPolicy` and `selectedAttackPoints`: exact runs name the
chosen device ids/rule ids, while only exhaustive runs are described as a budget.

Device trust/privacy labels use template declarations by default. Ordinary device
creation sends no label override; advanced settings may explicitly override the current
state or a local variable. Choosing "use template default" removes that override instead
of copying the current template value into the device instance. Existing imported or
persisted explicit overrides remain authoritative. Shared Environment Pool labels follow
the same backend template fallback and are edited in the inspector's advanced details.

Verification results and completed async verification tasks include `outcome`,
`modelComplete`, `disabledRuleCount`, `skippedSpecCount`, and item-level
`generationIssues`; technical warnings also appear in `checkLogs` with
`[rule-disabled]` / `[spec-skipped]` markers. UI code must surface every issue label and
reason even
when `outcome === 'SATISFIED'`, because they mean the generated SMV model omitted or
degraded part of the requested rules/specs. Present `INCONCLUSIVE` separately from
`VIOLATED`; there is no boolean `safe` shortcut because it collapses completeness and
property outcome into a misleading binary.
`modelComplete` is authoritative and required on interpretable completed results. The UI
must not reconstruct it from zero warning counts; a missing value is an incomplete
response and must never be promoted to a green complete-model state.

Every accepted verification/simulation task and every run result/trace carries
`modelSnapshot`: capture time plus device, rule, specification, effective environment,
and distinct referenced-template counts. `templatesFrozen=true` means generation used
the manifests captured at submission even if the template catalog changed while an
async task waited. It does not mean the current Board still matches. The UI may compare
a same-tab submission signature with current modelable input; historical/reloaded runs
must instead say that the current Board was not compared and scope the result to the
saved snapshot.

Completed async verification tasks also expose `specResults` and `nusmvOutput`,
matching synchronous verification results. Completed async simulations expose their raw
NuSMV output through the persisted `SimulationTraceDto` referenced by
`simulationTraceId`.

Verification traces return a structured verification-time `violatedSpec`; raw
`violatedSpecJson`, ownership ids, and request snapshots remain backend-internal.
Verification `specResults` is an array of `{ specId, templateId, specificationLabel,
formulaPreview, formulaKind, outcome, expression }` objects for the specifications
actually emitted to NuSMV. Render `specificationLabel`/localized `templateId`,
`formulaPreview`, and `formulaKind` in the ordinary result row; keep technical `specId`
and the actual NuSMV `expression` in an expandable technical section. These fields are
captured from the submitted run, so never look up the mutable current Board by `specId`
to rebuild a historical result. The array order is verifier-emission order, not
necessarily current canvas order. A completed verification can be `outcome='INCONCLUSIVE'` with an
empty `specResults` when generation emitted no specifications, or with
`outcome='INCONCLUSIVE'` entries when NuSMV produced no trustworthy result for an
emitted property; do not present either case as a property violation or as "all
specifications satisfied".

Verification requests (`verify` and `verifyAsync`) must include at least one specification.
Simulation remains the no-spec workflow.

Contracts for board storage and board recommendation endpoints live in
[../api/board.md](../api/board.md). Contracts for verification, traces, and fix live in
[../api/verification.md](../api/verification.md).

Template manifests submitted through `addDeviceTemplate` must match
`backend/device-template-schema.json` exactly. The frontend may normalize user-uploaded
JSON into the PascalCase schema shape before submission, but it should not send
lower-case aliases or extra fields and should keep `API.Trigger` as `null`; transition
conditions belong in `Transitions[].Trigger`. The backend validates the raw manifest
before DTO mapping, so schema violations return a `400` instead of being silently
ignored. Every `InternalVariables[]` item must explicitly set `IsInside` and
`FalsifiableWhenCompromised`; `IsInside=true` is device-local and `false` is scene-shared,
and omission is rejected rather than silently selecting shared scope. Each variable also
declares `Values` (including `TRUE/FALSE` for booleans) or complete numeric bounds; an
omitted domain is invalid. `FalsifiableWhenCompromised` controls whether a compromised
instance may falsify that reading within its declared domain. API presence is not a
sensor/actuator classifier.

For custom-template icons, the optional PascalCase `Icon` field may contain a
`data:image/...` URI (best for self-contained JSON imports) or an HTTPS image URL.
If it is missing, UI code should render the bundled state icon when one exists and
fall back to a generated template icon rather than showing a broken image.

---

## Simulation — `api/simulation.ts`

Default-export object: `simulate`, `simulateAsync (→ Promise<SimulationTask>)`, `getTasks`,
`getTask`, `getTaskProgress`, `cancelTask`, `simulateAndSave`, `getUserSimulations`,
`getSimulation`, `deleteSimulation`. Same unwrap convention as `board.ts`.
Like `verifyAsync`, `simulateAsync` resolves to the authoritative accepted task, whose
server-generated `id` is used for polling. If the promise rejects with validation or
service-unavailable errors, do not start polling.
Synchronous `simulate` and `simulateAndSave` also reject invalid requests instead of
returning a success-shaped empty result. Timeout, interruption, failed execution, and
zero parsed states use the same submit error path. Successful results, async tasks, and
saved traces carry `modelComplete`, `disabledRuleCount`, and `generationIssues`; show
reduced-model traces as incomplete and list every omitted automation with its reason.
Saved trace context is returned as derived `isAttack`, `attackBudget`, `enablePrivacy`, and
`modelSemantics`, not as a
raw request JSON blob. Describe every simulation as generated-model behavior, not a
physical-home prediction.
Treat `historyPersistence` independently from trajectory validity. Plain `simulate`
returns `NOT_REQUESTED`. `simulateAndSave` may return playable states with
`OUTCOME_UNKNOWN`; refresh saved-run history and warn that persistence could not be
confirmed, but do not discard the trajectory, claim it was saved, or retry automatically.
Synchronous verification uses the same contract: preserve the formal conclusion while
presenting its separate run-history persistence status.
For users, present simulation modes as "preview now" versus "save in background": plain
`simulate` previews immediately and does not persist a trace, `simulateAndSave` previews
and stores the synchronous trace, and `simulateAsync` stores the trace automatically when
the task completes. A background simulation completion should leave the task-status
layer and update saved-run history instead of forcibly opening the timeline over the
user's current work.
The `1..100` simulation-step control exposes synchronized decrement/increment buttons,
direct integer entry, and a range slider. Normalize direct input at the control boundary;
all three surfaces must submit the same validated step count.
Compact run-setting panels keep long attack-selection and trust/privacy model explanations
behind accessible hover/focus/click info tooltips. Keep state-specific limitations and
errors visible inline: no modeled attack effect, the 50-point run cap, invalid budget or explicit point,
forced privacy propagation, disabled rules, and incomplete-model outcomes must never be
hidden as optional help.

## Rule recommendation — `api/rules.ts`

This module owns **rule recommendation only**: named exports `recommendRules` and
`cancelRecommendRules` (cancellable via `cancelRecommendRules()`), plus a default-export
object of the same two. **Rule persistence is not here**: targeted `getRules`/`addRule`/
`removeRule` methods live on `boardApi` (`api/board.ts`), which owns the `RuleDto` to
`RuleForm` mapping.

---

## Chat (SSE) — `api/chat.ts`

Named exports. Session management (`getSessionList`, `createSession`,
`getSessionHistory`, `getSessionActivity`, `requestSessionStop`, `deleteSession`) uses
axios; **streaming does not**.
`getSessionHistory` returns `{ messages, nextBeforeId, hasMore }`; the first call requests
the newest bounded page, and `ChatView` passes `nextBeforeId` back as `beforeId` when the
user loads older messages. Older pages are prepended while preserving scroll position.

`sendStreamChat(...)` uses the native `fetch` API against
`${VITE_API_BASE_URL || ''}/api/chat/completions` (relative by default, so it also goes
through the proxy), sends a per-request `turnId`, and reads the response body with
`response.body.getReader()` (SSE).
This is the one place the axios
instance and its interceptors are bypassed — the `Authorization` header must be set
manually here. Protocol detail: [../api/chat-sse.md](../api/chat-sse.md).

`onProgress` appends verifiable execution events instead of replacing one generic
loading label. `ChatView` renders a full-width activity record with context loading,
task resumption after confirmation, every planning round, localized tool actions, tool
outcomes, cumulative success/failure/unconfirmed counts, duplicate-loop protection, and
final-answer generation inside the active assistant message. A resumed-task event shows
the bounded original user objective supplied by the backend; it does not expose model
reasoning. The record remains attached to that message and is persisted with the terminal
assistant row. History reload replaces the local response only when that row has the same
`turnId`, so an older completed turn cannot erase the current request.
The wrapper invokes `onAccepted` as soon as the HTTP response succeeds, because the backend
has already persisted and admitted the request at that point. A later missing-body or SSE
parse failure is treated as an accepted-stream failure: local state is retained until
authoritative history settlement decides whether a terminal row exists. An HTTP rejection
before acceptance removes optimistic placeholders and restores the ordinary text draft.

`getSessionList` also returns `ChatSession.active`. `ChatView` refreshes this list whenever
the panel becomes visible and whenever the document returns to the foreground. With no
selected conversation it automatically opens the first active session. Selecting a row
already marked active starts activity polling and locks mutations before history loading,
so a slow or failed history request cannot briefly unlock known-running work; rows without
that signal perform the dedicated activity check. This is an authoritative activity
reattachment rather than an SSE replay: the UI shows that server work is still running,
exposes the real stop endpoint, and keeps mutations locked. Once activity becomes idle it
reloads the terminal assistant row (including the persisted trace) and reconciles the
Board/run history. Terminal history/session refresh still runs when Board reconciliation
fails; the reconciliation retry remains visible and locked, but the completed assistant
record is not hidden behind an unrelated Board refresh failure. Session-list activity dots
make runs started in another tab visible without waiting for a conflicting action to fail.

The chat stop control first calls `requestSessionStop`, then aborts the SSE response. It
cannot undo a backend tool call that already started, but the backend still persists a
result that returns after the stop request before ending the workflow. `ChatView`
therefore polls `getSessionActivity` until the cross-instance execution lease reports
idle, keeps assistant mutations locked, then reloads conversation/board/history.
Session switching, new-conversation creation, and deletion wait for the same settling
step. Activity checks have their own 2.5-second request timeout, so three consecutive
query failures produce an outcome-unknown warning and an authoritative state refresh
within seconds rather than inheriting the general 100-second axios timeout. Do not label this
control as cancelling the requested operation.
If the server continues to report an active tool for the 10-second settlement window,
the UI switches to the same visible retry/locked state instead of spinning for the full
SSE timeout or releasing a known-running mutation.

Stream commands cross the component boundary through a promise-returning
`executeCommand` callback. `ChatView` does not release its global interaction lock until
the Board confirms the refresh. A failed targeted refresh falls back to `board_state`;
if that also fails, a localized retry panel keeps assistant requests, scene replacement,
and trace playback locked until reconciliation succeeds. Sign-out invokes the same
settlement through the exposed `prepareForLogout()` method, requiring explicit user
confirmation when the backend tool outcome remains unknown. SSE `401` responses clear
authentication and navigate to login; `403` responses remain authorization errors and do
not discard a valid login session.
Board collection refreshes triggered by chat are serialized through the same mutation
queue. Read-only trace playback and a pending scene replacement disable new assistant
requests; starting either while an assistant stream is active is blocked until the stream
stops and its authoritative refresh can complete.

`onFinish` is emitted only when the response stream reaches normal completion, not on
abort. `ChatView` assigns epochs to streams, session-history loads, and session-list
loads; callbacks from replaced requests cannot clear a newer controller or overwrite a
newly selected conversation. Conversation-history loading is separate from response
generation, so the Stop control is shown only for a response that can actually be
aborted.

---

## Types

Backend↔frontend field alignment worth noting:

- `types/spec.ts` `SpecCondition` (`side`, `deviceId`, `deviceLabel`, `targetType`,
  `key`, `relation`, `value`) and `Specification`
  (`aConditions`/`ifConditions`/`thenConditions`/`devices`) match the backend
  `SpecConditionDto` / `SpecificationDto` shape. For board storage, spec `deviceId`
  fields are raw board node ids. For model requests, the request builder converts them
  to normalized `varName` values. `deviceLabel` is only a display snapshot and is not
  used for resolution. See
  [../architecture/device-identity.md](../architecture/device-identity.md).
- Spec `formula` and `devices[]` are derived display caches, not authority. Manual
  creation, AI recommendation apply, and standard scene import rebuild both from the
  accepted structured conditions; they do not trust an AI/file-authored cache. Call
  `buildSpecFormula(spec, { nodes, deviceTemplates })` so the preview mirrors NuSMV
  state tuples, environment variables, and trust/privacy resolution. `board.ts`
  `toBackendSpecificationWriteDto` strips `templateLabel`, `formula`, `devices[]`, and
  condition display/UI fields from targeted and batch writes. Model requests likewise
  submit structured conditions as authority; only a run result's checked expression says
  what the checker actually evaluated.
- `types/verify.ts` holds `VerificationRequest`, `VerificationResult`,
  `VerificationTask`, generation warning counts, and the trace types.
- `types/fix.ts` holds fix-related types.
- **Runtime option lists** (`relationOperators`, `targetTypes`, `specTemplateDetails`)
  live only in `assets/config/specTemplates.ts` — that is the single source components
  import. Do not reintroduce copies in `types/spec.ts`.
- **Known intentional parallelism**: `types/simulation.ts` (`SimulationState` /
  `SimulationDevice` / `SimulationVariable` / `SimulationTrustPrivacy`) and the
  `types/verify.ts` trace types both mirror the backend `TraceStateDto` tree. They are
  kept as two near-identical trees on purpose (verification vs simulation consumers);
  this is deliberate parallelism, not accidental duplication. They are **not fully
  isomorphic** — e.g. `TraceTrustPrivacy.trust` is `boolean | null` and `privacy` is
  required (closely mirroring backend `TraceTrustPrivacyDto`: `Boolean trust`, `String
  privacy`), whereas `SimulationTrustPrivacy` uses the looser `trust?: boolean` /
  `privacy?: string`. When a **backend field** changes, keep the shared shape aligned on
  both sides; but each side may keep its own optionality/nullability to suit its
  consumers.

When a backend DTO changes, update the corresponding `types/*.ts` and this guide in
the same PR (see [../../CONTRIBUTING.md](../../CONTRIBUTING.md)).
