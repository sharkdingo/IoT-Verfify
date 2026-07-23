# Chat API (SSE Streaming)

Contract for `/api/chat` — session management plus the streaming completion endpoint.
Session endpoints use the standard `Result<T>` envelope ([overview.md](overview.md));
the streaming endpoint does **not** — it is an SSE stream.

Verified against code on 2026-07-23. Source: `controller/ChatController.java`,
`service/impl/ChatServiceImpl.java`, `dto/chat/`.

---

## Session management (`Result<T>`)

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/chat/sessions` | → `ChatSessionResponseDto[]` | List the user's sessions |
| POST | `/api/chat/sessions` | → `ChatSessionResponseDto` | Create a session (no body) |
| GET | `/api/chat/sessions/{sessionId}/messages?beforeId=&limit=50` | → `ChatHistoryPageDto` | Bounded message history, newest page first |
| GET | `/api/chat/sessions/{sessionId}/activity` | → `ChatSessionActivityDto { sessionId, active }` | Authoritative cross-instance check for whether a request is still active for the session |
| GET | `/api/chat/sessions/{sessionId}/confirmation` | → `ChatPendingConfirmationDto { sessionId, kinds }` | Server-authoritative protected-action kinds waiting for an explicit UI decision |
| POST | `/api/chat/sessions/{sessionId}/stop` | → `null` | Idempotently request that the active response stop; already-started writes are not rolled back |
| DELETE | `/api/chat/sessions/{sessionId}` | → `null` | Delete a session |

`ChatSessionResponseDto`: `{ id: String, userId: Long, title: String | null, createdAt,
updatedAt, active: boolean }`. `active` is computed from the same renewable database
lease as the dedicated activity endpoint, allowing a new browser connection to discover
an already-running session from the list response.
`title=null` means the session has no user-derived title yet; clients render their own
localized "new conversation" label. Persistence placeholders such as `New Chat` are not
part of the user-facing contract and are normalized to `null` when reading older rows.
At most 100 sessions are stored per user. Creation beyond that limit returns `400` and asks
the user to delete an old session; the list endpoint is correspondingly bounded to the 100
most recently updated sessions.
Each session also has a configured stored-message ceiling. Before accepting a completion,
the backend reserves enough rows for one worst-case complete tool turn. A conversation too
close to the ceiling returns `429` before claiming a lease with
`data={ reasonCode: "CHAT_HISTORY_LIMIT_REACHED", messageCount, maxMessagesPerSession,
requiredTurnCapacity }`.
`ChatHistoryPageDto` is `{ messages: ChatMessageResponseDto[], nextBeforeId: Long | null,
hasMore: boolean }`. `limit` defaults to 50 and accepts `1..100`; `beforeId` is the positive
message-id cursor returned by the preceding page. The service scans at most 2,000 raw rows
per request while hiding internal tool messages, so a tool-heavy turn cannot turn one history
read into an unbounded allocation.
`ChatMessageResponseDto`: `{ id: Long, sessionId: String, role: String, content:
String, turnId?: String, createdAt, executionTrace?: ProgressDto[], executionElapsedSeconds?: Integer,
executionStatus?: "COMPLETED" | "AWAITING_CONFIRMATION" | "PARTIAL" | "STOPPED" |
"DISCONNECTED" | "FAILED" }`.
Every started user turn that reaches message persistence attempts to save a visible
terminal assistant record, including provider failure and client-disconnect paths. A
terminal-write failure does not create a misleading disconnect row; the client retains
its local response when authoritative history has no terminal row with the same `turnId`.
When saved, the row stores
the exact bounded execution record, elapsed time, and explicit terminal status; `PARTIAL`
means tool work began before a later failure, an execution guard, or an uncertain result.
`COMPLETED` means the visible response stream and terminal persistence completed; it does
not prove that a requested platform objective completed. When planning executes no tool,
the server prefixes the visible response with an authoritative notice that no current
Board data was read and no platform operation was confirmed, even if model prose claims
otherwise. `AWAITING_CONFIRMATION` means a no-write preview is waiting for the user's decision.
`STOPPED` means the user explicitly requested the response to stop, while `DISCONNECTED`
means transport loss ended it. Neither status implies rollback. Older rows without this metadata
are reconstructed from persisted internal tool-call/result blocks. Raw tool JSON, internal
identifiers, provider exceptions, and private model reasoning remain hidden.

Only one stream request may be active for a session across all backend instances.
A concurrent request or deletion returns `409` with
`data={ reasonCode: "CHAT_SESSION_BUSY", sessionId }`; it does not interrupt the first
request. Registration happens before the worker is queued, so the short enqueue window
cannot admit a second request. The active request id, expiry, and stop flags are stored on
the locked `chat_session` row. Activity checks and stop requests therefore remain
authoritative without load-balancer affinity. A scheduled heartbeat renews the short-lived
lease while the owning worker is registered; timing keys and defaults are owned by the
[configuration reference](../getting-started/configuration.md#ai-assistant). Renewal uses a
short transaction that locks the matching session row and recomputes the effective current
time after any lock wait from both the database clock and monotonic elapsed time. It extends
only the same still-unexpired execution id, so a delayed or stale worker cannot revive an
expired lease or overwrite a replacement lease.
Transient database failures are retried, but the local worker is cancelled once ownership
has remained unconfirmed for one complete database-lease TTL.
Lease creation, activity checks, renewal, release, and expiry cleanup all compare against
the database clock rather than a JVM clock. The execution id acquired before dispatch is
also carried through the queued worker and controller cleanup: a worker whose local
registration was replaced cannot start, and an older request's `finally` cannot remove or
release the replacement execution.
The execution id also fences persisted user/tool/terminal messages and the shared
confirmation, scenario-draft, and task-continuation state. Ordinary AI writes perform a
non-locking ownership precheck, then briefly lock and recheck the session row immediately
before commit. Long tool transactions therefore do not block the heartbeat, while a replaced,
stopped, or expired worker still rolls back instead of appending audit rows or overwriting
follow-up state.
The same scheduled pass clears expired lease ids and stop flags. A crashed or restarted
worker therefore releases its session after at most one TTL instead of leaving it busy for
hours, while a healthy execution can run past any single lease window. Normal completion
and queue rejection still clear the lease immediately.

Across sessions, each user may run at most two assistant streams at once. Redis
coordinates this admission across backend instances; if Redis is unavailable, the same
limit is enforced within each process. A token-checked heartbeat renews every live Redis
admission lease, so a healthy stream can run beyond its initial two-hour safety TTL without
another instance admitting a replacement. Controller cleanup releases the in-process slot
in a `finally` path even when database execution-lease cleanup fails. Excess requests return
`429` before a stream starts.
If token renewal proves that ownership was replaced, or Redis remains unavailable through
the complete lease TTL, the old worker is interrupted and its controller rechecks the lease
before returning a result. A brief Redis outage remains fail-open as documented in the
configuration reference, but an expired unconfirmed worker is not allowed to run indefinitely
beside a replacement.

The admission response includes `data.reasonCode=USER_CHAT_OPERATION_BUSY`, operation
kind, coordination scope, and limit. The frontend renders this as a wait-for-other-session
message instead of exposing the backend's English diagnostic.

Permanent account deletion is stronger than ordinary per-session activity handling. The backend
marks every persisted execution lease for that user as stopped and completes locally bound
emitters. Correctness does not depend on the local emitter optimization: each
session/message write locks the active user row and rechecks that the session is still owned by
that user in the same transaction. Database cascade constraints make this invariant independent
of the chat process: work committed first is removed with the account, while a user/session/task
write that arrives after deletion is rejected because its parent row no longer exists. A remote
or late stream therefore cannot recreate data after the account has been removed.

---

## `POST /api/chat/completions` — streaming (SSE)

Sends a user message and streams the assistant's visible reply. **Not** wrapped in
`Result<T>` — the response is `text/event-stream` produced by a Spring `SseEmitter`
(60-minute default timeout, configured by `CHAT_SSE_TIMEOUT_MS`).
Synchronous rejections that occur before the stream is established (for example invalid
input, an unknown session, or a busy session) use the standard JSON `Result<T>` error
envelope and retain their documented HTTP status even when the client sends
`Accept: text/event-stream`.

Every non-blank message first runs model-driven planning with the complete registered
tool catalog. The model may choose zero tools for ordinary conversation, or freely chain
read, recommendation, mutation, verification, and status tools when the request spans
domains. This decision is based on the message meaning and conversation context rather
than a keyword or deterministic intent route. Tool calls and bounded tool results are
persisted as internal chat messages but are not exposed as raw user-visible text. A result
over `CHAT_MAX_TOOL_RESULT_BYTES` becomes a structured `TOOL_RESULT_TOO_LARGE` unavailable
result before persistence or reuse as provider context.
Structured progress frames expose the verifiable execution state and outcome of each
step while it runs. After planning completes, the final assistant reply is generated
through the streaming LLM path so tool-backed answers also arrive as incremental text
chunks.
If planning chooses no tool, the streamed and persisted answer begins with a deterministic
server notice that the turn did not confirm current Board data or a completed platform
operation. The backend does not infer platform intent from keywords; ordinary conversation
may still finish as `COMPLETED`, whose meaning is response completion only.

Planning is objective-oriented rather than a rigid domain workflow. A delegated task may
combine targeted deletion, creation, environment, rule, specification, simulation, and
verification tools in the order supported by current state and tool results. A successful
tool call does not by itself end the task. Planning continues until the original objective
is complete or a confirmation, unavailable-result, no-progress, or emergency boundary
requires it to stop.

Questions about the current scene, including device/rule/specification counts, are
planned from `board_overview` rather than inferred from chat history. A request to extend
or complete the current scene reads that overview first and may compose targeted device,
environment, rule, and specification recommendation/mutation tools while preserving the
existing scene. Before adding a device, the planner reads `list_templates` for the exact
available template name instead of treating `board_overview` as a template catalog or
inventing a name. `recommend_scenario` remains a complete replacement/import draft and
is used only when the user explicitly asks for that workflow. When the user later asks
to apply that chat-generated draft, the planner calls `apply_scenario` directly instead
of reading the Board and deleting devices individually. The tool first returns a
no-write impact preview; after a later explicit confirmation it uses the same atomic
Board replacement authority as UI scene import. See [ai-tools.md](ai-tools.md) for the
stored-draft and expiration contract.

Tool execution is not one transaction across an entire user request. Each mutating tool
commits or rejects independently. AI-originated Board writes, verification/simulation task
creation and cancellation, synchronous verification-history persistence, and trace deletion
require the same unexpired execution id with no committed stop request. Ordinary write
transactions acquire the session-row lock only at their commit fence, so a replacement or
stop committed before that fence rejects and rolls back the mutation. Verification and
simulation cancellation are the exception: because they trigger an irreversible local process
stop before database commit, their short transactions lock and verify the session immediately.
Long NuSMV computation never holds the chat row lock. There is no five-round product budget: planning
continues while calls or results are changing. Two guards prevent runaway execution:
consecutive rounds that repeat the exact same calls and results stop after
`CHAT_MAX_STAGNANT_ROUNDS`, and `CHAT_MAX_TOOL_ROUNDS` is a high emergency ceiling rather
than a normal task limit. One planning response is additionally limited by
`CHAT_MAX_TOOL_CALLS_PER_ROUND`; an oversized response executes none of its calls. These
guards preserve earlier commits, emit a visible guard
event, and still run the streaming final-answer model with an instruction to identify
completed, failed, and unfinished work accurately.

Account deletion removes confirmation, draft, continuation, chat history, and the account
inside the same database transaction. Only after commit does it stop local chat transport
and revoke the current token. A rollback therefore restores all durable account state.

`requiresUserConfirmation=true` is a generic no-write boundary, not only a deletion
preview. The planning loop stops immediately for destructive previews and for proposed
alternatives such as an available replacement device name. The assistant must state that
nothing was changed and wait for the user's choice; it cannot accept its own suggestion
in a later planning round of the same message.

That boundary pauses only the protected step. The backend keeps the original user
objective in a per-user, per-session server-side continuation entry for 15 minutes. On a
later explicit confirmation it restores both the live confirmation authority and the
original objective. The continuation also retains up to four recent user messages plus a
bounded, sanitized summary of the pending tool result. The latest user message is
authoritative when it changes or narrows the older objective. After the confirmed tool
returns a usable result, the planner resumes the remaining work with the complete tool
catalog. A targeted replacement can therefore preview and confirm a deletion, create the
replacement, repair dependent rules/specs, and run requested verification without treating
the confirmation as the end of the task. A second protected action still requires its own
preview and confirmation. Ordinary questions and task updates preserve the pending preview;
explicit cancellation, session/account cleanup, and expiration clear it. Continuation
state is stored in the shared database, so a normal backend restart or load-balanced
follow-up does not by itself discard a still-live entry.

If a model response contains several parallel tool calls and one call reaches this
boundary, later calls in that same response are not executed. The backend records an
explicit `skipped=true` tool result for each one so the provider conversation remains
protocol-complete and the final visible explanation can still stream. The same rule
applies after `RESULT_UNAVAILABLE`; skipped calls are not counted as successful or
failed executions.

History reconstruction also validates that every persisted assistant tool-call id has
exactly one matching tool-result id before sending that block back to a provider.
Incomplete, duplicate, malformed, or isolated internal tool blocks are omitted from the
model context, while surrounding user-visible conversation remains available. This lets
sessions created before the same-round skip rule recover without repeating a provider
protocol error. During the active request, blank or reused correlation ids returned by a
compatible provider are replaced with unique internal ids before persistence or tool
execution, and the same repaired ids are used for assistant calls and their results.
Pending destructive confirmation data is not recovered from that bounded history. On an
explicit confirmation turn, the backend injects compact server-authoritative context for
the pending tool, target, and opaque token, so a large preview cannot force the assistant
to request the same confirmation repeatedly. Full-scene application likewise keeps the
draft and Board impact token server-side and injects only the instruction to call
`apply_scenario` with `confirmed=true`. The separate continuation entry supplies only
user-authored objectives/updates and sanitized tool output, not model reasoning, so
successful confirmation can be followed by the remaining requested tools even when older
chat detail fell outside the history window.

Protected destructive previews (deletions and bundled-default reset) additionally return
an opaque `impactToken`. The backend keeps one pending protected action per authenticated
user and chat session, bound to the tool, target, and canonical digest of the visible
preview. Confirmation is target-aware rather than position-aware: ordinary questions or
changed instructions may intervene without discarding the preview.

Protected authority never comes from model interpretation of ordinary text. The client
reads `GET /api/chat/sessions/{sessionId}/confirmation`, renders an explicit decision for
each returned kind, and sends the selected `kind` plus `CONFIRM` or `CANCEL` in the next
stream request's structured `confirmation` field. The accepted kinds are `DESTRUCTIVE`,
`DEFAULT_TEMPLATE_RESET`, and `SCENE_REPLACEMENT`. The backend requires that exact kind to
still be pending for the authenticated session; an invented, stale, or mismatched command
authorizes no write. Natural-language classification remains available only for
non-destructive choice prompts and cannot create or consume protected authority.
The token is valid for 15 minutes and is consumed once
before mutation; a second tool call in the same model response cannot reuse it. Wrong,
expired, cross-session, cross-user, changed-preview, and replayed tokens return a no-write
`409` with `requiresUserConfirmation=true` and a fresh preview where available. Explicit
cancellation clears the relevant pending action; session/account deletion and expiration
also clear it. Pending confirmations are stored in the shared database and consumed with
an optimistic compare-and-delete, so restart or instance switching preserves both the
binding and single-use guarantee. This binding applies uniformly to device, template, rule,
specification, verification-trace, and simulation-trace deletion.

`RESULT_UNAVAILABLE` is distinct from both success and failure. It means response details
could not be serialized after the tool reached its response stage. The loop stops so it
cannot automatically repeat a possibly committed mutation. If
`mutationMayHaveCommitted=true`, affected data is refreshed, the result is counted as
unconfirmed rather than usable, and the user is told to inspect current state before
retrying. With `mutationMayHaveCommitted=false`, no mutation refresh is sent.

**Request body**: `ChatRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `sessionId` | `String` | Required; ≤64 characters |
| `content` | `String` | Required; ≤10000 characters |
| `turnId` | `String` | Optional for compatibility; ≤64 characters. Current clients send a unique value used to associate the user message and terminal assistant record. The server generates one when omitted. |
| `confirmation` | `ChatConfirmationCommandDto` | Optional explicit protected-action decision: `{ action: "CONFIRM" | "CANCEL", kind: "DESTRUCTIVE" | "DEFAULT_TEMPLATE_RESET" | "SCENE_REPLACEMENT" }`. It is accepted only when that kind is currently pending for the session. |

If the chat thread pool is saturated the request is rejected with `503`
(`ServiceUnavailableException`) before streaming starts. Errors that happen after the
emitter is created, including an inaccessible session or LLM provider failure, are
reported as an SSE content frame prefixed with `[ERROR] ` and then the stream completes.
After the user message has been saved, the same error path also persists a visible
`FAILED` or `PARTIAL` terminal assistant row. A detected disconnect persists
`DISCONNECTED`; the client reloads authoritative history after the backend reports the
session idle, so that record remains visible even when its SSE frame could not arrive.

### Stream frames

Each SSE `data:` frame carries a JSON-serialized `StreamResponseDto`:

```json
{ "content": "partial assistant text" }
```

| Field | Type | Meaning |
| :--- | :--- | :--- |
| `content` | `String` | A chunk of assistant text (streamed incrementally) |
| `command` | `CommandDto` | Optional front-end command: `{ type, payload }` where `type` is e.g. `REFRESH_DATA` / `SHOW_TOAST` / `NAVIGATE` and `payload` is a `Map<String, Object>` (e.g. `{"target":"device_list"}`) |
| `progress` | `ProgressDto` | Optional live status `{ stage, toolName?, round?, outcome?, successfulSteps?, failedSteps?, unconfirmedSteps?, detail? }`; `detail` is a bounded task-resumption summary, model-authored reasoning summary, or operation-aware tool-result summary |

Progress stages and outcomes:

| Stage | Meaning | Outcome when present |
| :--- | :--- | :--- |
| `CONTEXT_READY` | Request accepted; conversation and Board context are available | — |
| `TASK_RESUMED` | A confirmed step is resuming the stored original objective; `detail` contains its bounded user-authored summary | — |
| `PLANNING` | The model is choosing the next tool step for `round` | — |
| `REASONING` | Before tool execution, `detail` carries the model's bounded, sanitized user-visible summary of the current goal, observed facts, next action, and remaining work | — |
| `TOOL_EXECUTION` | `toolName` has started | — |
| `TOOL_RESULT` | The tool returned and cumulative counters were updated | `USABLE`, `PARTIAL`, `FAILED`, `RESULT_UNAVAILABLE`, or `CONFIRMATION_REQUIRED` |
| `EXECUTION_GUARD` | Duplicate no-progress execution or the emergency runaway ceiling stopped further calls | `NO_PROGRESS` or `EMERGENCY_LIMIT` |
| `WRITING_RESPONSE` | Tool work ended and the visible final answer is streaming | — |

Frames are emitted with `MediaType.APPLICATION_JSON`. Notes on framing:

- Text chunks arrive as `StreamResponseDto` objects with a `content` field.
- Front-end commands (canvas refresh, toast, navigation) arrive as separate frames
  carrying `command`. Refresh commands are collected from usable mutating tools and from
  result-unavailable tools that explicitly say a mutation may already have committed,
  then sent before the final streamed assistant text. If a later planning or reply step
  throws, pending refresh commands are sent before the SSE error when the connection is
  still usable.
- A `recommend_scenario` result whose deterministic `objectiveStatus` is `PARTIAL` remains
  reviewable, but the final assistant row is `PARTIAL` and carries a server notice that
  missing core scene parts were not completed.
- Progress frames arrive before and between potentially slow model/tool calls. They let the UI
  show a full-width ReAct-style record of sanitized reasoning summaries, localized actions,
  observations, confirmation points, cumulative outcomes, and elapsed time. `REASONING` is an
  audit-oriented summary requested from the model, not the provider's private hidden chain-of-thought.
  Compatible-provider fields explicitly named as safe summaries (`reasoning_summary`,
  `reasoningSummary`, `reasoning_summary_content`, `analysis_summary`, or
  `analysisSummary`) are accepted through the provider adapter. Raw `reasoning_content`
  and `analysis` fields are deliberately ignored.
  Live frames are not stored as separate rows. After completion, the exact emitted event list
  and elapsed time are serialized on the final assistant message, so reloads preserve task
  resumption, confirmation, and execution-guard boundaries. Legacy assistant rows fall back to
  reconstruction from internal tool-call/result rows; that fallback omits same-round calls
  explicitly recorded as skipped and never executed.
- Every planning round receives the complete registered tool catalog. The model can use
  conversation context and tool schemas to select zero or more tools across domains;
  pending-message semantics are classified by the configured model, while the actual
  authorization remains server-scoped to an existing pending kind, exact target/digest,
  authenticated user/session, 15-minute lifetime, and single-use token.
- Board refresh targets are `device_list`, `environment_list`, `rule_list`, `spec_list`,
  `template_list`, and `run_history`. A tool emits every target it may have changed;
  device mutations therefore also refresh the shared Environment Pool, while async task
  creation/cancellation, sync verification, and saved-trace deletion refresh run history.
- Errors are emitted as a `content` frame prefixed with `[ERROR] ` and then the stream
  completes.
- The client also tolerates a literal `[DONE]` sentinel (ignored) and non-JSON text
  lines (treated as raw content).

### Consuming the stream (frontend)

The frontend does **not** use axios for this endpoint — it uses the native `fetch`
API and reads `response.body.getReader()`, so the `Authorization: Bearer <token>`
header is set manually. See
[../guides/frontend-integration.md](../guides/frontend-integration.md) for the
`sendStreamChat(...)` wrapper (with `onMessage` / `onCommand` / `onError` / `onFinish`
callbacks and `AbortController` support). `onFinish` means the response stream reached
normal completion; a client abort does not masquerade as completion.

`REFRESH_DATA` commands use a promise-returning component callback rather than a
fire-and-forget event. The assistant remains interaction-locked until the owning Board
method confirms the targeted refresh. If that refresh fails, the client immediately
attempts the client-only `board_state` reconciliation. A second failure leaves a visible,
localized retry panel open and keeps assistant requests, scene replacement, and trace
playback locked until a later full reconciliation succeeds.

The Stop control first sends `POST /api/chat/sessions/{sessionId}/stop`, then aborts the
browser stream. This distinguishes an explicit user stop from an unexpected transport
loss. The owning backend immediately closes a blocked provider stream or cancels a pending
planning future; another backend instance observes the durable stop flag during lease
maintenance and closes its local provider request. Stop still cannot cancel or roll back a
tool transaction already running on the server. A tool that has already returned is still classified and persisted before the
worker stops when the same execution still owns the lease, so committed writes and
confirmation previews do not lose their audit result. A worker replaced by a newer execution
cannot persist that result or a terminal assistant row.
After an explicit stop or a session-switch/new-session request, the Board polls
the session activity endpoint until `active=false`, keeps assistant mutations locked
during that settling period, and only then reloads message history, board collections,
and run history. Normal stream completion also waits for `active=false` and reloads
authoritative message history so persisted terminal status wins over locally inferred
progress. History replaces the local response only when the terminal row carries the same
`turnId`; an older terminal reply cannot erase the current request. Closing the floating
panel only hides it and does not abort the request. If three consecutive activity checks
fail, each check uses a dedicated 2.5-second timeout instead of the general 100-second
REST timeout, so the client reaches an outcome-unknown warning and authoritative
reconciliation within seconds rather than several minutes. It does not claim cancellation
or automatically repeat the command. The
client-only `board_state` refresh target is used for full reconciliation; it is not an AI
tool result.
Frontend cross-tab discovery, immediate locking, foreground refresh, and settlement behavior
are owned by the [frontend integration guide](../guides/frontend-integration.md).
Live SSE progress frames are not replayed to a new connection; the complete persisted
execution trace becomes available with the terminal assistant row.
If the activity endpoint remains reachable but still reports `active=true` for the
10-second settlement window, the client stops spinning, keeps the interaction lock, and
asks the user to retry settlement later; it does not treat a running tool as cancelled.

Signing out asks the mounted assistant to perform the same settlement first. A confirmed
idle/reconciled result proceeds normally; an outcome-unknown result requires an explicit
second confirmation, and a failed authoritative reconciliation blocks sign-out until the
user retries synchronization. An SSE `401` clears local authentication and navigates to
the login route like the axios interceptor. An SSE `403` is shown as an authorization
failure and does not log out an otherwise valid session.
Every stream and session-history load has a client request epoch. Late chunks, commands,
completion callbacks, or history responses from a stopped/replaced request are ignored,
so they cannot clear or overwrite a newer conversation. Loading session history has a
separate UI state and does not expose a non-functional "stop response" control.

The floating assistant is mounted lazily on its first open and then hidden rather than
destroyed when the user closes the panel. Closing the panel therefore preserves the
selected conversation and does not mean "stop receiving"; the explicit stop control is
the operation that aborts the browser stream and triggers reconciliation. On the first
mounted open, the client requests the session list even when the panel was already
visible before the component finished loading. The sidebar distinguishes loading, empty,
and failed states and offers an explicit retry after a failed list request. Before the
first response chunk arrives, the assistant's pending status is rendered inside one
compact assistant bubble rather than as an empty message followed by detached status
text.
The client treats any successful HTTP response as transport acceptance because the backend
has already claimed the execution slot and persisted the request before returning the SSE
response. A missing or unreadable response body remains a localized stream error, but it
does not roll back a request that may still be running. A pre-stream `400`, `409`, `429`, or
`503` removes optimistic user and assistant placeholders, restores an ordinary text draft,
and leaves protected-action confirmation state intact; a rejected request therefore never
appears as persisted history.

Backend-supplied safety notices and fallback explanations follow the language of the
current user message for Chinese and English conversations. This applies to no-write
confirmation previews, failed or result-unavailable tool steps, execution-guard and
missing-reply fallbacks, and mapped stream errors. These deterministic notices remain
visible and are persisted with the assistant reply; raw English control text is not
prepended to an otherwise Chinese answer.

Client-detected stream protocol failures use stable error kinds (`HTTP_ERROR`,
`MISSING_BODY`, `EMPTY_STREAM`, `INVALID_FRAME`, `SERVER_FRAME`) and are localized by
the frontend. Internal parser messages such as `No response body` remain diagnostic
details and are not displayed verbatim in a localized conversation.

> Note: this endpoint derives its base URL from `VITE_API_BASE_URL` (empty by default →
> a relative `/api`, proxied), the same source the axios layer uses.
