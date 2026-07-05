# Chat API (SSE Streaming)

Contract for `/api/chat` — session management plus the streaming completion endpoint.
Session endpoints use the standard `Result<T>` envelope ([overview.md](overview.md));
the streaming endpoint does **not** — it is an SSE stream.

Verified against code on 2026-07-04. Source: `controller/ChatController.java`,
`service/impl/ChatServiceImpl.java`, `dto/chat/`.

---

## Session management (`Result<T>`)

| Method | Path | Body / Response | Notes |
| :--- | :--- | :--- | :--- |
| GET | `/api/chat/sessions` | → `ChatSessionResponseDto[]` | List the user's sessions |
| POST | `/api/chat/sessions` | → `ChatSessionResponseDto` | Create a session (no body) |
| GET | `/api/chat/sessions/{sessionId}/messages` | → `ChatMessageResponseDto[]` | Message history |
| DELETE | `/api/chat/sessions/{sessionId}` | → `null` | Delete a session |

`ChatSessionResponseDto`: `{ id: String, userId: Long, title: String, createdAt,
updatedAt }`.
`ChatMessageResponseDto`: `{ id: Long, sessionId: String, role: String, content:
String, createdAt }`.

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
  carrying `command`. Refresh commands are sent after successful mutating tools and
  before the final streamed assistant text.
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
callbacks and `AbortController` support).

> Note: this endpoint derives its base URL from `VITE_API_BASE_URL` (empty by default →
> a relative `/api`, proxied), the same source the axios layer uses.
