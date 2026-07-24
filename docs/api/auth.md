# Authentication API

Field-level contract for `/api/auth`. The `Result<T>` envelope, the `Bearer` scheme,
and error codes are defined once in [overview.md](overview.md); this doc covers the
request/response bodies only.

Verified against code on 2026-07-24. Source: `controller/AuthController.java`,
`service/impl/AuthServiceImpl.java`, and `dto/auth/`.

---

## `POST /api/auth/register`

Public. Creates a user.

**Request body**: `RegisterRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `phone` | `String` | Required; must match `^1[3-9]\d{9}$` (mainland China mobile) |
| `username` | `String` | Required; raw input at most 100 characters; NFC-normalized and stripped of surrounding Unicode whitespace; 3–20 Unicode code points afterwards; no control, invisible format, or line-separator characters; must not match the phone-number pattern; unique with case- and accent-sensitive matching; usable for login |
| `password` | `String` | Required; 10–64 characters and at most 72 UTF-8 bytes |

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
Login is rate-limited per normalized account identifier and registration per phone number,
with separate higher source-IP ceilings so ordinary users behind one NAT do not share the
low credential limit. Username buckets retain the normalized identifier's case and accent
because those distinctions identify different valid accounts. Excess attempts return
structured `429` data and `Retry-After`.
The owning limits and multi-instance guidance live in the
[configuration reference](../getting-started/configuration.md#authentication-jwt).
Registration, login, deletion confirmation, and authentication throttling use the same
username normalization, so surrounding whitespace cannot create an unreachable account.

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
| `identifier` | `String` | Required; phone number or username; at most 100 characters; usernames use the registration normalization above |
| `password` | `String` | Required; at most 128 characters |

**Response**: `AuthResponseDto` (under `data`)

| Field | Type | Notes |
| :--- | :--- | :--- |
| `userId` | `Long` | |
| `phone` | `String` | |
| `username` | `String` | |
| `token` | `String` | JWT; send as `Authorization: Bearer <token>` on later requests |

Unknown accounts and incorrect passwords both return `401 Unauthorized` with the same
account-neutral message, so the response works for phone and username login without
revealing whether an identifier exists.

```bash
TOKEN=$(curl -sX POST http://localhost:8080/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"identifier":"testuser","password":"password123"}' | jq -r '.data.token')
```

Note the field is `data.token` — the payload lives under the `Result<T>` envelope's
`data`.

Phone-shaped usernames are forbidden, so phone and username identifiers occupy disjoint
namespaces. Login classifies the normalized identifier once and queries only that namespace.

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
| `password` | `String` | Required; at most 128 characters and must match the current account password |
| `confirmation` | `String` | Required; at most 100 characters; normalized like login and then must exactly match the current `username` or `phone` |

Password or confirmation mismatches return `400 Bad Request`; they do not revoke the
current session. Missing/invalid authentication still returns `401 Unauthorized`.
Because a missing response or `5xx` can arrive after the deletion transaction committed,
clients must not retry blindly. The web client clears its local session and asks the user
to sign in again to determine whether the account still exists. An explicit `4xx` response
is treated as a definite rejection and leaves the deletion form available for correction
(an authentication `401` still clears the invalid local session through the shared client).

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
- `chat_message.session_id` and `chat_session_pre_admission_stop.session_id` cascade from
  `chat_session`; the latter stores bounded turn-specific Stop fences. Exploration findings use
  a composite `(user_id, fuzz_task_id)` ownership constraint against their task. A late child
  row therefore cannot attach to a missing parent or to another user's task.
- Durable AI continuation, confirmation, and scenario-draft rows use a composite
  `(user_id, session_id)` constraint against their chat session. They cannot be attached to
  another user's session and cascade when that session is deleted.
- Deletes the current user's board layout, device nodes, rules, specifications,
  device templates, verification traces/tasks, simulation traces/tasks, exploration
  findings/tasks, AI continuation/confirmation/draft state, and AI chat sessions/messages.
- Deletes the `app_user` row last.

`JwtAuthenticationFilter` also checks that the token's user id still exists before
establishing authentication. This keeps a deleted account from authenticating even if
Redis blacklist revocation is temporarily unavailable.

Startup first performs an idempotent transactional cleanup of legacy rows whose `user_id` no
longer exists in `app_user`, chat/AI state whose session or session owner is gone, and findings
whose task is missing or belongs to another user. It then adds or verifies the cascade ownership
constraints and required indexes. An unexpected non-cascade constraint fails startup instead of
silently weakening account-deletion integrity. Active-account rows are not rewritten. MySQL
startup also verifies and, when necessary, migrates `app_user.username` to the case- and
accent-sensitive `utf8mb4_0900_as_cs` collation.

```bash
curl -X DELETE http://localhost:8080/api/auth/account \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"password":"password123","confirmation":"testuser"}'
```
