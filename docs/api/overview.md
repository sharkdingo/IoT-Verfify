# API Conventions

Authoritative definition of the cross-cutting API conventions: the `Result<T>`
response envelope, the authentication scheme, and the error/status codes. This is the
**single source of truth** for these three things — every other API document links
here instead of restating them.

Verified against code on 2026-07-22. Source: `dto/Result.java`,
`exception/GlobalExceptionHandler.java`, `configure/JacksonConfig.java`,
`configure/ApplicationTimeConfig.java`,
`component/model/ModelRequestParser.java`, `security/`.

---

## Response envelope — `Result<T>`

Every application JSON REST response is wrapped in `Result<T>`. The exceptions are a
successfully established SSE stream from `POST /api/chat/completions` (see
[chat-sse.md](chat-sse.md)) and the protocol-level empty `406 Not Acceptable` response when
the client accepts neither JSON nor an endpoint's success representation. Synchronous setup
errors from the chat endpoint still use a JSON `Result<T>` envelope and their original HTTP
status, including when the request advertises only `Accept: text/event-stream`.

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
| `data` | `T` / omitted | Payload; shape depends on the endpoint. Omitted when the backend value is `null`, including void operations. |

`Result` is annotated `@JsonInclude(NON_NULL)`, so `data` is omitted from the JSON when
null. Success responses are produced by `Result.success(data)` (code `200`).

When a domain doc says "**Response**: `SomeDto`", it means that DTO appears under
`data`. When it says "**Response `data`**: `Long`", the payload is that raw value.

### Timestamp format

Java `LocalDateTime` response fields are serialized as ISO-8601 date-times with the offset
for the configured application zone, for example `2026-07-22T12:30:00+08:00`. Clients must
parse the supplied offset and must not append `Z`. Request fields accept the legacy local
form without an offset; when an offset is present, it must be a valid offset for the
configured zone at that local time or deserialization returns `400`. The owning zone and
default are documented in the
[configuration reference](../getting-started/configuration.md#application-time).

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
- A valid token only establishes authentication when its user id still exists in the
  `app_user` table. This makes account deletion effective even if Redis blacklist checks
  are temporarily unavailable.
- Tokens have a lifetime of `JWT_EXPIRATION` (default 24h — see
  [../getting-started/configuration.md](../getting-started/configuration.md)).
- Logout blacklists the token in Redis. The blacklist is **fail-open**: if Redis is
  down the app keeps serving, but logout-revocation degrades.
- Controllers receive the authenticated user id via the `@CurrentUser Long userId`
  argument; it is never taken from the request body.

The public endpoints (no token required) are `POST /api/auth/register` and
`POST /api/auth/login`. `POST /api/auth/logout` and `DELETE /api/auth/account` live
under `/api/auth` but still require a valid bearer token at both the security-filter and
`@CurrentUser` ownership boundaries. The application excludes Spring Boot's generated
default user because authentication is JWT-only.

---

## Error and status codes

Errors are mapped centrally by `GlobalExceptionHandler` to a `Result<T>` whose `code`
equals the HTTP status, except for the empty protocol-level `406` described above. Error
envelopes explicitly use `Content-Type: application/json` instead of allowing a
success-media `Accept` header to obscure the original error. Domain and framework
exceptions and their statuses:

| HTTP | Exception | Meaning |
| :--- | :--- | :--- |
| 400 | `BadRequestException` | Malformed request / invalid argument |
| 401 | `UnauthorizedException` | Missing/invalid/expired token |
| 403 | `ForbiddenException` | Authenticated but not allowed (e.g. another user's resource) |
| 404 | `ResourceNotFoundException` | Resource does not exist |
| 405 | `HttpRequestMethodNotSupportedException` | The path exists but does not support the requested HTTP method |
| 406 | `HttpMediaTypeNotAcceptableException` | No acceptable representation can be produced; the response body is intentionally empty |
| 409 | `ConflictException`, `ChatSessionBusyException`, `TemplateDeletionConflictException`, `DataIntegrityViolationException` | State/uniqueness conflict; specialized conflicts include structured reason data |
| 413 | `RequestBodySizeFilter` | JSON request body exceeds the configured byte limit and is rejected before DTO binding |
| 415 | `HttpMediaTypeNotSupportedException` | The request content type is unsupported |
| 422 | `ValidationException` | Semantic validation failure |
| 429 | `FuzzTaskQuotaExceededException`, `FuzzTaskStorageQuotaExceededException`, `AsyncTaskQuotaExceededException`, `UserOperationBusyException`, `AuthRateLimitException` | Per-user active/stored background-task limit, per-user synchronous-operation limit, or public authentication attempt limit reached. Operation admission returns `USER_FORMAL_OPERATION_BUSY` or `USER_CHAT_OPERATION_BUSY`; authentication limits return an `AUTH_*_RATE_LIMIT_REACHED` reason, scope, retry delay, and `Retry-After` header. |
| 500 | `InternalServerException`, `SmvGenerationException`, `PersistedDataIntegrityException` (and uncaught) | Server-side failure or unusable persisted semantic data |
| 502 | `BadGatewayException` | The configured AI provider replied, but its output could not be parsed as the requested structured result |
| 503 | `ServiceUnavailableException`, `FixApplyPreflightUnavailableException` | Service temporarily unavailable or an automatic-fix apply preflight could not confirm model equality; the specialized fix rejection includes `data.reasonCode=FIX_APPLY_PREFLIGHT_UNAVAILABLE` and is guaranteed to occur before the board write |
| 504 | `SimulationExecutionException` | Synchronous simulation timed out before producing a usable model trace |

Additional mappings: missing required query parameters, bean-validation failures (`@Valid`,
`@NotNull`, etc.), and malformed JSON map to `400`; `IllegalArgumentException` is masked
to a generic `400` and `IllegalStateException` to `500`, so internal detail is not leaked.

JSON scalar coercion is disabled for REST request DTOs. Integer fields require JSON
integer numbers (not quoted strings, booleans, or floats), floating-point fields require
JSON numbers (not quoted strings or booleans), and boolean fields require JSON booleans
(not `0`/`1`, strings, or floats). Type mismatches fail during request deserialization
before bean validation or service-layer semantic checks run. The `400` response names
the safe JSON path (for example `items[0].count`) in both `message` and `data.errors`;
it does not echo the rejected value or a Java implementation type.

Unknown JSON fields are also rejected rather than silently discarded. This applies to
ordinary board mutations, authentication, chat, automatic-fix requests, and other typed
REST request bodies. Their `400` response identifies the unknown field and its nested
path. Verification and simulation use a dedicated strict parser because
an ignored nested field could change the checked model; their `400` message identifies
the exact unsupported path (for example `devices[0].currentStateTrsut`) and explains
that the request was not executed. Template-manifest endpoints additionally validate the
raw object against `backend/device-template-schema.json` before DTO conversion.

**Message suppression**: `application.yaml` sets `server.error.include-message: never`
and `include-binding-errors: never`, so Spring's `/error` endpoint does not expose
internal exception detail. Error `message` fields returned through
`GlobalExceptionHandler` are deliberately generic for server-side failures
(`InternalServerException` and uncaught exceptions return `"Internal server error"`).

**Exception — `SmvGenerationException` (500)** is intentionally more specific: it
returns a controlled `message` of the form `"[<errorCategory>] <generation error>"`
and also sets `data` to `{ "errorCategory": "<category>" }`, so the frontend can
surface *why* model generation failed (e.g. an invalid template value) without exposing
a stack trace.

**Specialized conflict data (409)**: an active chat session returns
`{ reasonCode: "CHAT_SESSION_BUSY", sessionId }`. A stale or blocked device-template
deletion returns `{ reasonCode, currentPreview }`, where `reasonCode` is
`TEMPLATE_DELETION_PREVIEW_STALE` or `TEMPLATE_DELETION_BLOCKED`. Clients use the
structured data to refresh the exact pending decision instead of parsing the English
message.

**Persisted semantic integrity (500)**: JSON columns that define a model, run, trace,
template, or structured chat-tool message are decoded fail-closed. Missing, blank,
malformed, or unknown JSON fields, mismatched template names, or an unsupported persisted chat role return the
safe message `Stored model data is invalid; the operation was stopped before using an
incomplete model.` with `data={ reasonCode: "PERSISTED_SEMANTIC_DATA_INVALID",
recordType, recordId?, field }`. The backend does not reinterpret corrupt data as an
empty list, default role, or missing model feature. History list endpoints may instead
isolate a damaged row as a documented `dataAvailable=false` placeholder so other valid
history remains accessible.

**Structured validation errors (400/422)** return every available field error, not only
the first one. This applies to DTO/constraint validation (`400`) and service semantic
`ValidationException` failures (`422`). `message` remains a short first-error summary,
while `data` is:

```json
{
  "errors": {
    "nodes[0].id": "Reason for this field",
    "rules[1].conditions": "Reason for this field"
  }
}
```

Clients must account for every entry when an operation validates a compound object such
as a complete scene. Field paths are diagnostic coordinates; ordinary UI translates
them to user-facing item labels and localized failure states. Because legacy validation
reasons are English technical diagnostics rather than locale-stable copy, clients place
the raw field/reason pair in Technical Details unless a domain endpoint supplies a
stable `reasonCode`. Unknown backend free text must not be inserted into a different-
language interface.

**Exception — `SimulationExecutionException` (500/503/504)** means a synchronous
simulation produced no usable model trace. Its controlled message is accompanied by
`data: { reasonCode, logs }`; `reasonCode` distinguishes timeout, interruption, empty
parsed states, and general execution failure. It is an error response, never an empty
success-shaped `SimulationResultDto`.

Generation warnings that do not abort model generation are not HTTP errors. Verification
returns `200` with warning details in `VerificationResultDto.checkLogs`,
`disabledRuleCount`, `skippedSpecCount`, and item-level `generationIssues`; clients must
display each omitted item's label and reason even when
`outcome=SATISFIED`, and also use `modelComplete` to qualify the conclusion.

---

## Related

- Endpoint index: [rest-endpoints.md](rest-endpoints.md)
- Auth contract: [auth.md](auth.md)
- Config (JWT, Redis, CORS): [../getting-started/configuration.md](../getting-started/configuration.md)
