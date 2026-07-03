# Authentication API

Field-level contract for `/api/auth`. The `Result<T>` envelope, the `Bearer` scheme,
and error codes are defined once in [overview.md](overview.md); this doc covers the
request/response bodies only.

Verified against code on 2026-07-03. Source: `controller/AuthController.java`,
`dto/auth/`.

---

## `POST /api/auth/register`

Public. Creates a user.

**Request body**: `RegisterRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `phone` | `String` | Required; must match `^1[3-9]\d{9}$` (mainland China mobile) |
| `username` | `String` | Required; 3–20 characters |
| `password` | `String` | Required; 6–20 characters |

**Response**: `RegisterResponseDto` (under `data`)

| Field | Type |
| :--- | :--- |
| `userId` | `Long` |
| `phone` | `String` |
| `username` | `String` |

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
| `phone` | `String` | Required |
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
  -d '{"phone":"13800138000","password":"password123"}' | jq -r '.data.token')
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

```bash
curl -X POST http://localhost:8080/api/auth/logout \
  -H "Authorization: Bearer $TOKEN"
```
