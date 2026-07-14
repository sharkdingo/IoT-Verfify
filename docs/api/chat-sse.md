# Chat API (SSE Streaming)

Contract for `/api/chat` — session management plus the streaming completion endpoint.
Session endpoints use the standard `Result<T>` envelope ([overview.md](overview.md));
the streaming endpoint does **not** — it is an SSE stream.

Verified against code on 2026-07-14. Source: `controller/ChatController.java`,
`service/impl/ChatServiceImpl.java`, `dto/chat/`.

---

## Session management (`Result<T>`)

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/chat/sessions` | → `ChatSessionResponseDto[]` | List the user's sessions |
| POST | `/api/chat/sessions` | → `ChatSessionResponseDto` | Create a session (no body) |
| GET | `/api/chat/sessions/{sessionId}/messages` | → `ChatMessageResponseDto[]` | Message history |
| GET | `/api/chat/sessions/{sessionId}/activity` | → `ChatSessionActivityDto { sessionId, active }` | Authoritative check for whether this backend is still processing a request for the session |
| DELETE | `/api/chat/sessions/{sessionId}` | → `null` | Delete a session |

`ChatSessionResponseDto`: `{ id: String, userId: Long, title: String | null, createdAt,
updatedAt }`.
`title=null` means the session has no user-derived title yet; clients render their own
localized "new conversation" label. Persistence placeholders such as `New Chat` are not
part of the user-facing contract and are normalized to `null` when reading older rows.
`ChatMessageResponseDto`: `{ id: Long, sessionId: String, role: String, content:
String, createdAt }`.

Only one stream request may be active for a session on one running backend instance.
A concurrent request or deletion returns `409` with
`data={ reasonCode: "CHAT_SESSION_BUSY", sessionId }`; it does not interrupt the first
request. Registration happens before the worker is queued, so the short enqueue window
cannot admit a second request. The activity flag is cleared in the worker's `finally`
block and on queue rejection. Multi-instance deployments require shared request-affinity
or distributed activity coordination; this in-memory guard is not a cluster-wide lock.

---

## `POST /api/chat/completions` — streaming (SSE)

Sends a user message and streams the assistant's visible reply. **Not** wrapped in
`Result<T>` — the response is `text/event-stream` produced by a Spring `SseEmitter`
(10-minute default timeout, configured by `CHAT_SSE_TIMEOUT_MS`).

Conversational messages without a board/tool intent stream directly. Messages that
mention board operations such as devices, rules, specifications, verification,
simulation, templates, traces, or recommendations first run one or more non-visible
tool-planning rounds. Tool calls and tool results are persisted as internal chat
messages, but they are not emitted as user visible text. After planning completes, the
final assistant reply is generated through the streaming LLM path so tool-backed answers
also arrive as incremental text chunks.

Tool execution is not one transaction across an entire user request. Each mutating tool
commits or rejects independently. Reaching the five-round planning limit therefore stops
additional steps but does not roll back earlier ones. The stream reports usable, failed,
and result-unavailable tool-step counts and explicitly labels the request as potentially
incomplete; failure or missing-final-reply fallbacks never say that the whole operation
completed.

`requiresUserConfirmation=true` is a generic no-write boundary, not only a deletion
preview. The planning loop stops immediately for destructive previews and for proposed
alternatives such as an available replacement device name. The assistant must state that
nothing was changed and wait for the user's choice; it cannot accept its own suggestion
in a later planning round of the same message.

`RESULT_UNAVAILABLE` is distinct from both success and failure. It means response details
could not be serialized after the tool reached its response stage. The loop stops so it
cannot automatically repeat a possibly committed mutation. If
`mutationMayHaveCommitted=true`, affected data is refreshed, the result is counted as
unconfirmed rather than usable, and the user is told to inspect current state before
retrying. With `mutationMayHaveCommitted=false`, no mutation refresh is sent.

**Request body**: `ChatRequestDto`

| Field | Type | Rules |
| :--- | :--- | :--- |
| `sessionId` | `String` | Required |
| `content` | `String` | Required; ≤10000 characters |

If the chat thread pool is saturated the request is rejected with `503`
(`ServiceUnavailableException`) before streaming starts. Errors that happen after the
emitter is created, including an inaccessible session or LLM provider failure, are
reported as an SSE content frame prefixed with `[ERROR] ` and then the stream completes.

### Stream frames

Each SSE `data:` frame carries a JSON-serialized `StreamResponseDto`:

```json
{ "content": "partial assistant text" }
```

| Field | Type | Meaning |
| :--- | :--- | :--- |
| `content` | `String` | A chunk of assistant text (streamed incrementally) |
| `command` | `CommandDto` | Optional front-end command: `{ type, payload }` where `type` is e.g. `REFRESH_DATA` / `SHOW_TOAST` / `NAVIGATE` and `payload` is a `Map<String, Object>` (e.g. `{"target":"device_list"}`) |

Frames are emitted with `MediaType.APPLICATION_JSON`. Notes on framing:

- Text chunks arrive as `StreamResponseDto` objects with a `content` field.
- Front-end commands (canvas refresh, toast, navigation) arrive as separate frames
  carrying `command`. Refresh commands are collected from usable mutating tools and from
  result-unavailable tools that explicitly say a mutation may already have committed,
  then sent before the final streamed assistant text. If a later planning or reply step
  throws, pending refresh commands are sent before the SSE error when the connection is
  still usable.
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

Aborting the browser stream means **stop receiving the AI response**, not cancel or roll
back a tool transaction already running on the server. After an explicit stop or a
session-switch/new-session request, the Board polls the session activity endpoint until
`active=false`, keeps assistant mutations locked during that settling period, and only
then reloads message history, board collections, and run history. Closing the floating
panel only hides it and does not abort the request. If three consecutive activity checks
fail, the client releases the wait with an outcome-unknown warning and reconciles current
state; it does not claim cancellation or automatically repeat the command. The
client-only `board_state` refresh target is used for full reconciliation; it is not an AI
tool result.
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

Backend-supplied safety notices and fallback explanations follow the language of the
current user message for Chinese and English conversations. This applies to no-write
confirmation previews, failed or result-unavailable tool steps, planning-limit and
missing-reply fallbacks, and mapped stream errors. These deterministic notices remain
visible and are persisted with the assistant reply; raw English control text is not
prepended to an otherwise Chinese answer.

Client-detected stream protocol failures use stable error kinds (`HTTP_ERROR`,
`MISSING_BODY`, `EMPTY_STREAM`, `INVALID_FRAME`, `SERVER_FRAME`) and are localized by
the frontend. Internal parser messages such as `No response body` remain diagnostic
details and are not displayed verbatim in a localized conversation.

> Note: this endpoint derives its base URL from `VITE_API_BASE_URL` (empty by default →
> a relative `/api`, proxied), the same source the axios layer uses.
