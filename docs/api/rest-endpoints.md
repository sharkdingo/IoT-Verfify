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

Verified against code on 2026-07-03.

---

## Auth — `AuthController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/auth/register` | Register a new user | `docs/api/auth.md` |
| POST | `/api/auth/login` | Log in, returns JWT token | `docs/api/auth.md` |
| POST | `/api/auth/logout` | Log out, blacklists token | `docs/api/auth.md` |

## Board storage — `BoardStorageController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| GET | `/api/board/nodes` | List device instances | `docs/api/board.md` |
| POST | `/api/board/nodes` | Save device instances (full replace) | `docs/api/board.md` |
| GET | `/api/board/edges` | List device connections | `docs/api/board.md` |
| POST | `/api/board/edges` | Save device connections (full replace) | `docs/api/board.md` |
| GET | `/api/board/specs` | List specifications | `docs/api/board.md` |
| POST | `/api/board/specs` | Save specifications | `docs/api/board.md` |
| GET | `/api/board/rules` | List automation rules | `docs/api/board.md` |
| POST | `/api/board/rules` | Save rules | `docs/api/board.md` |
| GET | `/api/board/layout` | Get board layout | `docs/api/board.md` |
| POST | `/api/board/layout` | Save board layout | `docs/api/board.md` |
| GET | `/api/board/active` | Get active board state | `docs/api/board.md` |
| POST | `/api/board/active` | Save active board state | `docs/api/board.md` |
| GET | `/api/board/templates` | List device templates | `docs/api/board.md` |
| POST | `/api/board/templates` | Create custom template | `docs/api/board.md` |
| DELETE | `/api/board/templates/{id}` | Delete template | `docs/api/board.md` |
| POST | `/api/board/templates/reload` | Reset to default templates (returns count) | `docs/api/board.md` |
| GET | `/api/board/rules/recommend` | AI rule recommendations | `docs/api/board.md` |
| POST | `/api/board/devices/recommend` | AI device recommendations | `docs/api/board.md` |
| POST | `/api/board/rules/check-duplicate` | AI duplicate-rule check; available from `RuleBuilderDialog` as an optional manual check | `docs/api/board.md` |
| GET | `/api/board/specs/recommend` | AI specification recommendations | `docs/api/board.md` |

## Verification — `VerificationController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/verify` | Synchronous verification | `docs/api/verification.md` |
| POST | `/api/verify/async` | Async verification, returns `taskId` (Long) | `docs/api/verification.md` |
| GET | `/api/verify/tasks/{id}` | Task status | `docs/api/verification.md` |
| GET | `/api/verify/tasks/{id}/progress` | Task progress (0–100) | `docs/api/verification.md` |
| POST | `/api/verify/tasks/{id}/cancel` | Cancel task | `docs/api/verification.md` |
| GET | `/api/verify/traces` | List verification traces | `docs/api/verification.md` |
| GET | `/api/verify/traces/{id}` | Trace detail | `docs/api/verification.md` |
| DELETE | `/api/verify/traces/{id}` | Delete trace | `docs/api/verification.md` |
| GET | `/api/verify/traces/{id}/fault-rules` | Fault localization | `docs/api/verification.md` |
| POST | `/api/verify/traces/{id}/fix` | Fix suggestions | `docs/api/verification.md` |

## Simulation — `SimulationController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| POST | `/api/simulate` | Synchronous simulation (not persisted) | `docs/api/verification.md` |
| POST | `/api/simulate/async` | Async simulation, returns `taskId` (Long) | `docs/api/verification.md` |
| GET | `/api/simulate/tasks/{id}` | Task status | `docs/api/verification.md` |
| GET | `/api/simulate/tasks/{id}/progress` | Task progress (0–100) | `docs/api/verification.md` |
| POST | `/api/simulate/tasks/{id}/cancel` | Cancel task | `docs/api/verification.md` |
| POST | `/api/simulate/traces` | Simulate and persist | `docs/api/verification.md` |
| GET | `/api/simulate/traces` | List saved simulations (summary) | `docs/api/verification.md` |
| GET | `/api/simulate/traces/{id}` | Simulation detail (full states) | `docs/api/verification.md` |
| DELETE | `/api/simulate/traces/{id}` | Delete simulation | `docs/api/verification.md` |

## Chat — `ChatController`

| Method | Path | Note | Detail |
| :--- | :--- | :--- | :--- |
| GET | `/api/chat/sessions` | List chat sessions | `docs/api/chat-sse.md` |
| POST | `/api/chat/sessions` | Create session | `docs/api/chat-sse.md` |
| GET | `/api/chat/sessions/{sessionId}/messages` | Message history | `docs/api/chat-sse.md` |
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
