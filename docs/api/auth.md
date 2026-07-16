# Authentication API

Field-level contract for `/api/auth`. The `Result<T>` envelope, the `Bearer` scheme,
and error codes are defined once in [overview.md](overview.md); this doc covers the
request/response bodies only.

Verified against code on 2026-07-16. Source: `controller/AuthController.java`,
`service/impl/AuthServiceImpl.java`, and `dto/auth/`.

---

## `POST /api/auth/register`

Public. Creates a user.

**Request body**: `RegisterRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `phone` | `String` | Required; must match `^1[3-9]\d{9}$` (mainland China mobile) |
| `username` | `String` | Required; 3–20 characters; unique and can be used to log in |
| `password` | `String` | Required; 6–20 characters |

**Response**: `AuthResponseDto` (under `data`)

| Field | Type |
| :--- | :--- |
| `userId` | `Long` |
| `phone` | `String` |
| `username` | `String` |
| `token` | `String` |

Registration and initial bundled device-type creation are one transaction. The endpoint
returns an authenticated response only when the complete default type catalog was imported.
A missing or invalid bundled definition fails registration and rolls back the new user;
the API does not return a usable-looking account with a partial or empty catalog. Bundled
definitions are parsed and schema-validated once per backend process, then instantiated for
each new user inside the registration transaction. Clients should store `data.token` and enter
the authenticated application directly; a second login request is not required.

```bash
curl -X POST http://localhost:8080/api/auth/register \
  -H "Content-Type: application/json" \
  -d '{"phone":"13800138000","username":"testuser","password":"password123"}'
```

---

## `POST /api/auth/login`

Public. Returns a JWT token.

**Request body**: `LoginRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `identifier` | `String` | Required; phone number or username |
| `password` | `String` | Required |

**Response**: `AuthResponseDto` (under `data`)

| Field | Type | Notes |
| :--- | :--- | :--- |
| `userId` | `Long` | |
| `phone` | `String` | |
| `username` | `String` | |
| `token` | `String` | JWT; send as `Authorization: Bearer <token>` on later requests |

```bash
TOKEN=$(curl -sX POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"identifier":"testuser","password":"password123"}' | jq -r '.data.token')
```

Note the field is `data.token` — the payload lives under the `Result<T>` envelope's
`data`.

---

## `POST /api/auth/logout`

Authenticated. Blacklists the current token in Redis (fail-open — see
[overview.md](overview.md)).

- **Request**: no body. Requires `Authorization: Bearer <token>` (the header is read
  directly to identify the token to revoke).
- **Response**: `data` is `null`.
- Logout only revokes the current token and clears the client session. It does not
  cancel server-side verification/simulation/exploration tasks; those tasks remain associated
  with the account and can be viewed after the user signs in again.

```bash
curl -X POST http://localhost:8080/api/auth/logout \
  -H "Authorization: Bearer $TOKEN"
```

---

## `DELETE /api/auth/account`

Authenticated. Permanently deletes the current account and user-owned data.
The database transaction first validates the account and removes all user-owned rows.
Only after that transaction commits does the backend revoke the current token and interrupt
locally executing verification, simulation, counterexample-exploration, and AI-chat work. This
prevents a failed deletion from revoking a still-valid session or stopping tasks whose
database state was rolled back. User-owned data deletion removes board devices, rules,
specifications, templates, formal traces,
exploration findings, task rows, and AI chat records. If a
worker wakes after the account is gone, result persistence is rejected by the active-user
lock or by the missing task row, so deleted accounts do not receive late history entries.

**Request body**: `DeleteAccountRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `password` | `String` | Required; must match the current account password |
| `confirmation` | `String` | Required; must exactly match the current `username` or `phone` |

Password or confirmation mismatches return `400 Bad Request`; they do not revoke the
current session. Missing/invalid authentication still returns `401 Unauthorized`.

**Side effects**:

- Blacklists the current token after the data-deletion transaction commits, same as logout.
- Interrupts locally executing verification, simulation, exploration, and AI-chat work after
  commit; queued workers subsequently observe that their durable task/session row no longer
  exists.
- Database ownership constraints connect every user-owned `user_id` to `app_user` with
  `ON DELETE CASCADE`. Writes that commit first are removed with the account; writes that
  reach the database after deletion are rejected because the parent account no longer exists.
- Every chat-session or chat-message write locks the active user row and rechecks session
  ownership in the same transaction. A stream that reaches a persistence point after account
  deletion therefore stops instead of recreating chat rows.
- `chat_message.session_id` cascades from `chat_session`, and exploration findings use a
  composite `(user_id, fuzz_task_id)` ownership constraint against their task. A late child row
  therefore cannot attach to a missing parent or to another user's task.
- Deletes the current user's board layout, device nodes, rules, specifications,
  device templates, verification traces/tasks, simulation traces/tasks, exploration
  findings/tasks, and AI chat sessions/messages.
- Deletes the `app_user` row last.

`JwtAuthenticationFilter` also checks that the token's user id still exists before
establishing authentication. This keeps a deleted account from authenticating even if
Redis blacklist revocation is temporarily unavailable.

Startup first performs an idempotent transactional cleanup of legacy rows whose `user_id` no
longer exists in `app_user`, chat messages whose session or session owner is gone, and findings
whose task is missing or belongs to another user. It then adds or verifies the cascade ownership
constraints and required indexes. An unexpected non-cascade constraint fails startup instead of
silently weakening account-deletion integrity. Active-account rows are not rewritten.

```bash
curl -X DELETE http://localhost:8080/api/auth/account \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"password":"password123","confirmation":"testuser"}'
```
