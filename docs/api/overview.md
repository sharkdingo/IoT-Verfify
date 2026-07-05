# API Conventions

Authoritative definition of the cross-cutting API conventions: the `Result<T>`
response envelope, the authentication scheme, and the error/status codes. This is the
**single source of truth** for these three things — every other API document links
here instead of restating them.

Verified against code on 2026-07-04. Source: `dto/Result.java`,
`exception/GlobalExceptionHandler.java`, `security/`.

---

## Response envelope — `Result<T>`

Every REST response is wrapped in `Result<T>` **except** the SSE endpoint
`POST /api/chat/completions` (see [chat-sse.md](chat-sse.md)).

```json
{
  "code": 200,
  "message": "success",
  "data": { }
}
```

| Field | Type | Notes |
| :--- | :--- | :--- |
| `code` | `Integer` | Mirrors the HTTP status code |
| `message` | `String` | `"success"` on success, otherwise an error message |
| `data` | `T` | Payload; shape depends on the endpoint. `null` for void operations. |

`Result` is annotated `@JsonInclude(NON_NULL)`, so `data` is omitted from the JSON when
null. Success responses are produced by `Result.success(data)` (code `200`).

When a domain doc says "**Response**: `SomeDto`", it means that DTO appears under
`data`. When it says "**Response `data`**: `Long`", the payload is that raw value.

---

## Authentication

Stateless JWT (HS256). Obtain a token via `POST /api/auth/login` (see
[auth.md](auth.md)), then send it on every authenticated request:

```
Authorization: Bearer <token>
```

- The filter chain extracts the user id from the token;
  `JwtAuthenticationFilter.getUserIdFromToken()` is wrapped in try-catch, so a
  malformed token is treated as unauthenticated (leads to `401`).
- Tokens have a lifetime of `JWT_EXPIRATION` (default 24h — see
  [../getting-started/configuration.md](../getting-started/configuration.md)).
- Logout blacklists the token in Redis. The blacklist is **fail-open**: if Redis is
  down the app keeps serving, but logout-revocation degrades.
- Controllers receive the authenticated user id via the `@CurrentUser Long userId`
  argument; it is never taken from the request body.

The public endpoints (no token required) are `POST /api/auth/register` and
`POST /api/auth/login`.

---

## Error and status codes

Errors are mapped centrally by `GlobalExceptionHandler` to a `Result<T>` whose `code`
equals the HTTP status. Domain exceptions and their statuses:

| HTTP | Exception | Meaning |
| :--- | :--- | :--- |
| 400 | `BadRequestException` | Malformed request / invalid argument |
| 401 | `UnauthorizedException` | Missing/invalid/expired token |
| 403 | `ForbiddenException` | Authenticated but not allowed (e.g. another user's resource) |
| 404 | `ResourceNotFoundException` | Resource does not exist |
| 409 | `ConflictException` / `DataIntegrityViolationException` | State/uniqueness conflict |
| 422 | `ValidationException` | Semantic validation failure |
| 500 | `InternalServerException`, `SmvGenerationException` (and uncaught) | Server-side failure |
| 503 | `ServiceUnavailableException` | Thread pool saturated / task rejected |

Additional mappings: bean-validation failures (`@Valid`, `@NotNull`, etc.) and
malformed JSON map to `400`; `IllegalArgumentException` is masked to a generic `400`
and `IllegalStateException` to `500`, so internal detail is not leaked.

**Message suppression**: `application.yaml` sets `server.error.include-message: never`
and `include-binding-errors: never`, so Spring's `/error` endpoint does not expose
internal exception detail. Error `message` fields returned through
`GlobalExceptionHandler` are deliberately generic for server-side failures
(`InternalServerException` and uncaught exceptions return `"Internal server error"`).

**Exception — `SmvGenerationException` (500)** is intentionally more specific: it
returns a controlled `message` of the form `"[<errorCategory>] <generation error>"`
and also sets `data` to `{ "errorCategory": "<category>" }`, so the frontend can
surface *why* model generation failed (e.g. an invalid template value) without exposing
a stack trace. This is the one server-side error that carries a meaningful message.

Generation warnings that do not abort model generation are not HTTP errors. Verification
returns `200` with warning details in `VerificationResultDto.checkLogs`,
`disabledRuleCount`, and `skippedSpecCount`; clients must display them even when
`safe=true`.

---

## Related

- Endpoint index: [rest-endpoints.md](rest-endpoints.md)
- Auth contract: [auth.md](auth.md)
- Config (JWT, Redis, CORS): [../getting-started/configuration.md](../getting-started/configuration.md)
