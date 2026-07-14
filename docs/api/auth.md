# Authentication API

Field-level contract for `/api/auth`. The `Result<T>` envelope, the `Bearer` scheme,
and error codes are defined once in [overview.md](overview.md); this doc covers the
request/response bodies only.

Verified against code on 2026-07-12. Source: `controller/AuthController.java`,
`dto/auth/`.

---

## `POST /api/auth/register`

Public. Creates a user.

**Request body**: `RegisterRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `phone` | `String` | Required; must match `^1[3-9]\d{9}$` (mainland China mobile) |
| `username` | `String` | Required; 3–20 characters; unique and can be used to log in |
| `password` | `String` | Required; 6–20 characters |

**Response**: `RegisterResponseDto` (under `data`)

| Field | Type |
| :--- | :--- |
| `userId` | `Long` |
| `phone` | `String` |
| `username` | `String` |

Registration and initial bundled device-type creation are one transaction. The endpoint
returns `RegisterResponseDto` only when the complete default type catalog was imported.
A missing or invalid bundled definition fails registration and rolls back the new user;
the API does not return a usable-looking account with a partial or empty catalog.

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
  cancel server-side verification/simulation tasks; those tasks remain associated
  with the account and can be viewed after the user signs in again.

```bash
curl -X POST http://localhost:8080/api/auth/logout \
  -H "Authorization: Bearer $TOKEN"
```

---

## `DELETE /api/auth/account`

Authenticated. Permanently deletes the current account and user-owned data.
Before deleting rows, the backend revokes the current token and requests cancellation for
all active verification/simulation tasks. User-owned data deletion then removes board
devices, rules, specifications, templates, traces, task rows, and AI chat records. If a
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

- Blacklists the current token, same as logout.
- Cancels the current user's pending/running verification and simulation tasks before
  deleting stored task records.
- User-owned write paths and result persistence take a user-row lock before writing,
  so account deletion and in-flight board/template/history writes are serialized:
  writes that finish first are deleted with the account, while writes that arrive
  after deletion fail instead of creating orphan records.
- Deletes the current user's board layout, device nodes, rules, specifications,
  device templates, verification traces/tasks, simulation traces/tasks, and AI chat
  sessions/messages.
- Deletes the `user` row last.

`JwtAuthenticationFilter` also checks that the token's user id still exists before
establishing authentication. This keeps a deleted account from authenticating even if
Redis blacklist revocation is temporarily unavailable.

```bash
curl -X DELETE http://localhost:8080/api/auth/account \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"password":"password123","confirmation":"testuser"}'
```
