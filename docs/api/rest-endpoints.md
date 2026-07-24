# REST Endpoint Index

**This document is an index only.** It lists every backend endpoint with its HTTP
method, path, owning controller, and a one-line note. It intentionally contains **no
DTO fields, request/response bodies, or examples** — those live in the domain API
documents linked from the "Detail" column.

> **Single source of truth**: this is the only document that lists the full endpoint
> set. It is meant to be **regenerated (semi-automatically) from controller
> annotations** rather than hand-edited — see [Regeneration](#regeneration) below.
> Do not add field-level detail here; add it to the domain doc.

All paths are relative to the server root. Responses use the standard `Result<T>`
envelope (except the SSE endpoint `/api/chat/completions`) and authenticated endpoints
require `Authorization: Bearer <token>` — the authoritative definition of both lives in
[overview.md](overview.md).

Verified against code on 2026-07-24.

---

## Auth — `AuthController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/auth/register` | Register a new user | `docs/api/auth.md` |
| POST | `/api/auth/login` | Log in, returns JWT token | `docs/api/auth.md` |
| POST | `/api/auth/logout` | Log out, blacklists token | `docs/api/auth.md` |
| DELETE | `/api/auth/account` | Permanently delete the current account and user-owned data | `docs/api/auth.md` |

## Board storage — `BoardStorageController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/nodes` | List device instances | `docs/api/board.md` |
| POST | `/api/board/nodes` | Atomically append one or more device instances | `docs/api/board.md` |
| PUT | `/api/board/nodes/{nodeId}/layout` | Replace only one device's complete canvas layout | `docs/api/board.md` |
| PUT | `/api/board/nodes/{nodeId}/runtime` | Replace only one device's complete device-local runtime configuration | `docs/api/board.md` |
| PATCH | `/api/board/nodes/{nodeId}/label` | Rename one device instance and refresh spec display labels | `docs/api/board.md` |
| GET | `/api/board/nodes/{nodeId}/deletion-preview` | Preview every rule, specification, and Environment Pool effect of deleting one device | `docs/api/board.md` |
| POST | `/api/board/nodes/{nodeId}/delete` | Confirmed atomic device/rule/spec cascade delete | `docs/api/board.md` |
| GET | `/api/board/environment` | List and self-heal the board environment pool | `docs/api/board.md` |
| POST | `/api/board/environment` | Apply itemized field-level patches to the board environment pool | `docs/api/board.md` |
| GET | `/api/board/specs` | List specifications | `docs/api/board.md` |
| POST | `/api/board/specs` | Create one specification | `docs/api/board.md` |
| DELETE | `/api/board/specs/{specId}` | Delete one specification | `docs/api/board.md` |
| GET | `/api/board/rules` | List automation rules | `docs/api/board.md` |
| POST | `/api/board/rules` | Create one automation rule | `docs/api/board.md` |
| PUT | `/api/board/rules/order` | Atomically replace rule execution order | `docs/api/board.md` |
| DELETE | `/api/board/rules/{ruleId}` | Delete one automation rule | `docs/api/board.md` |
| GET | `/api/board/replacement-preview` | Preview authoritative current-scene counts and obtain the confirmation impact token | `docs/api/board.md` |
| POST | `/api/board/batch` | Confirmed atomic full-scene replacement/clear with exact template snapshots | `docs/api/board.md` |
| GET | `/api/board/snapshot` | Atomic initial Board semantic snapshot | `docs/api/board.md` |
| GET | `/api/board/layout` | Get board layout | `docs/api/board.md` |
| POST | `/api/board/layout` | Save board layout | `docs/api/board.md` |
| GET | `/api/board/templates` | List device templates | `docs/api/board.md` |
| GET | `/api/board/templates/schema` | Download the authoritative device-template JSON Schema | `docs/api/board.md` |
| POST | `/api/board/templates` | Create custom template | `docs/api/board.md` |
| GET | `/api/board/templates/{id}/deletion-preview` | Preview exact template-deletion blockers and obtain an impact token | `docs/api/board.md` |
| POST | `/api/board/templates/{id}/delete` | Confirm deletion against the unchanged preview | `docs/api/board.md` |
| GET | `/api/board/templates/defaults/reset-preview` | Preview exact default-type reset effects | `docs/api/board.md` |
| POST | `/api/board/templates/defaults/reset` | Confirm and atomically apply the previewed default-type reset | `docs/api/board.md` |
| POST | `/api/board/rules/recommend` | AI rule recommendations | `docs/api/board.md` |
| POST | `/api/board/devices/recommend` | AI device recommendations | `docs/api/board.md` |
| POST | `/api/board/rules/check-duplicate` | Deterministic duplicate-rule check used before saving a rule | `docs/api/board.md` |
| POST | `/api/board/rules/check-similarity` | Explicit AI rule-similarity check available from `RuleBuilderDialog` | `docs/api/board.md` |
| POST | `/api/board/specs/recommend` | AI specification recommendations | `docs/api/board.md` |
| POST | `/api/board/scenario/recommend` | AI importable scene-draft recommendation | `docs/api/board.md` |
| GET | `/api/board/recommendations/{requestId}` | Read the server-observed stage of an active or just-finished standalone recommendation | `docs/api/board.md` |
| DELETE | `/api/board/recommendations/{requestId}` | Cancel an in-flight standalone recommendation | `docs/api/board.md` |

## Verification — `VerificationController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/verify` | Synchronous verification | `docs/api/verification.md` |
| POST | `/api/verify/async` | Submit async verification; returns the accepted task snapshot for polling | `docs/api/verification.md` |
| GET | `/api/verify/tasks` | Active/failed/cancelled verification task status (completed results excluded) | `docs/api/verification.md` |
| GET | `/api/verify/tasks/{id}` | Task status | `docs/api/verification.md` |
| DELETE | `/api/verify/tasks/{id}` | Dismiss a failed/cancelled task with no result | `docs/api/verification.md` |
| GET | `/api/verify/tasks/{id}/progress` | Task progress (0–100) | `docs/api/verification.md` |
| POST | `/api/verify/tasks/{id}/cancel` | Request cancellation and return the actual outcome | `docs/api/verification.md` |
| GET | `/api/verify/runs` | Completed verification result summaries | `docs/api/verification.md` |
| GET | `/api/verify/runs/{id}` | Completed verification result detail | `docs/api/verification.md` |
| GET | `/api/verify/runs/{id}/traces` | Replayable counterexamples nested under one verification result | `docs/api/verification.md` |
| DELETE | `/api/verify/runs/{id}` | Delete a verification result and all linked counterexamples | `docs/api/verification.md` |
| GET | `/api/verify/traces` | List verification traces | `docs/api/verification.md` |
| GET | `/api/verify/traces/{id}` | Trace detail | `docs/api/verification.md` |
| DELETE | `/api/verify/traces/{id}` | Delete trace | `docs/api/verification.md` |
| GET | `/api/verify/traces/{id}/fault-rules` | Counterexample rule involvement with source-model completeness and limitations | `docs/api/verification.md` |
| POST | `/api/verify/traces/{id}/fix` | Generate signed fix suggestions | `docs/api/verification.md` |
| GET | `/api/verify/fix-requests/{requestId}` | Read the server-observed stage of an active or just-finished fix search | `docs/api/verification.md` |
| DELETE | `/api/verify/fix-requests/{requestId}` | Cancel an in-flight fix search | `docs/api/verification.md` |
| POST | `/api/verify/traces/{id}/fix/apply` | Apply the exact signed suggestion after snapshot checks | `docs/api/verification.md` |
| GET | `/api/verify/tasks/{id}/traces` | Traces for a specific async verification task | `docs/api/verification.md` |

## Simulation — `SimulationController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/simulate` | Synchronous simulation (not persisted) | `docs/api/verification.md` |
| POST | `/api/simulate/async` | Submit async simulation; returns the accepted task snapshot for polling | `docs/api/verification.md` |
| GET | `/api/simulate/tasks` | Active/failed/cancelled simulation task status (completed results excluded) | `docs/api/verification.md` |
| GET | `/api/simulate/tasks/{id}` | Task status | `docs/api/verification.md` |
| DELETE | `/api/simulate/tasks/{id}` | Dismiss a failed/cancelled task with no result | `docs/api/verification.md` |
| GET | `/api/simulate/tasks/{id}/progress` | Task progress (0–100) | `docs/api/verification.md` |
| POST | `/api/simulate/tasks/{id}/cancel` | Request cancellation and return the actual outcome | `docs/api/verification.md` |
| POST | `/api/simulate/traces` | Simulate and persist | `docs/api/verification.md` |
| GET | `/api/simulate/traces` | List saved simulations (summary) | `docs/api/verification.md` |
| GET | `/api/simulate/traces/{id}` | Simulation detail (full states) | `docs/api/verification.md` |
| DELETE | `/api/simulate/traces/{id}` | Delete simulation | `docs/api/verification.md` |

## Counterexample exploration — `FuzzController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| GET | `/api/fuzz/model-fingerprint` | Read the current Board's canonical bounded-search model fingerprint without creating a task | `docs/api/fuzzing.md` |
| POST | `/api/fuzz/workload/preview` | Calculate the current Board's authoritative bounded-search workload without creating a task | `docs/api/fuzzing.md` |
| POST | `/api/fuzz/paper-domain/preview` | Read the current Board's authoritative paper-mode initial-state and Event domains without creating a task | `docs/api/fuzzing.md` |
| POST | `/api/fuzz/async` | Capture the current Board and submit a bounded background search | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/tasks` | Active/failed/cancelled exploration task status (completed results excluded) | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/tasks/{id}` | Exploration task detail | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/tasks/{id}/progress` | Exploration progress (0-100) | `docs/api/fuzzing.md` |
| POST | `/api/fuzz/tasks/{id}/cancel` | Request cancellation and return the actual outcome | `docs/api/fuzzing.md` |
| DELETE | `/api/fuzz/tasks/{id}` | Dismiss a failed/cancelled task with no result | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/runs` | Completed exploration result summaries with finding summaries | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/runs/{id}` | Completed exploration result with full findings | `docs/api/fuzzing.md` |
| DELETE | `/api/fuzz/runs/{id}` | Delete an exploration result and all findings | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/runs/{id}/findings` | Full candidate findings for one completed run | `docs/api/fuzzing.md` |
| GET | `/api/fuzz/findings/{id}` | One owned candidate finding | `docs/api/fuzzing.md` |

## Chat — `ChatController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| GET | `/api/chat/sessions` | List chat sessions | `docs/api/chat-sse.md` |
| POST | `/api/chat/sessions` | Create session | `docs/api/chat-sse.md` |
| GET | `/api/chat/sessions/{sessionId}/messages` | Cursor-paged message history (`beforeId`, `limit`) | `docs/api/chat-sse.md` |
| GET | `/api/chat/sessions/{sessionId}/activity` | Check whether server work is still active for the session | `docs/api/chat-sse.md` |
| GET | `/api/chat/sessions/{sessionId}/confirmation` | Read pending protected-action kinds for explicit UI confirmation | `docs/api/chat-sse.md` |
| POST | `/api/chat/sessions/{sessionId}/stop` | Request an explicit turn-aware stop; body carries the local `turnId` or `null` for reattached work | `docs/api/chat-sse.md` |
| POST | `/api/chat/completions` | Send message — **SSE stream** (not `Result<T>`) | `docs/api/chat-sse.md` |
| DELETE | `/api/chat/sessions/{sessionId}` | Delete session | `docs/api/chat-sse.md` |

---

## Regeneration

This index should be kept honest by generating it from the controllers rather than
editing by hand. The endpoint set is defined by the `@RequestMapping` on each
controller plus the `@GetMapping` / `@PostMapping` / `@DeleteMapping` on its methods,
under:

```
backend/src/main/java/cn/edu/nju/Iot_Verify/controller/
├── AuthController.java
├── BoardStorageController.java
├── ChatController.java
├── FuzzController.java
├── SimulationController.java
└── VerificationController.java
```

A minimal check (list every mapping) that can seed or validate this table:

```bash
grep -rhnE "@(RequestMapping|GetMapping|PostMapping|DeleteMapping|PutMapping|PatchMapping)" \
  backend/src/main/java/cn/edu/nju/Iot_Verify/controller/
```

**CI suggestion**: fail the build if the set of mappings extracted from the
controllers differs from the paths listed here. That turns "the index drifted from
the code" from a review burden into an automated gate.
