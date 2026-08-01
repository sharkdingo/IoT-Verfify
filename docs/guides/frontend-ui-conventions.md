# Frontend UI conventions

Two decision records that govern the board's URL surface and all user feedback.
These are **rules, not descriptions** — when code and this document disagree, one of them is
a bug. Keep them short; they exist to stop the same argument being re-litigated per PR.

## 1. What belongs in the URL

The board's URL answers exactly one question: **which artifact is the user looking at?**
Everything else is either server-persisted workspace state or transient component state.

### Deep-linked (in the URL)

| Param | Values | Meaning |
| :--- | :--- | :--- |
| `run` | `verification:<id>`, `simulation:<id>`, `exploration:<id>` | The run whose result surface is open |
| `trace` | `<id>` | Counterexample trace being replayed (only with `run=verification:<id>`) |
| `finding` | `<id>` | Exploration finding being replayed (only with `run=exploration:<id>`) |

Rationale: each is a **server-owned entity with a stable numeric id**, it changes what the
user is looking at, and "send me the counterexample you're seeing" is a real workflow. A
link stays meaningful for anyone with access to that run.

### Deliberately *not* in the URL

- **Panel layout** — `collapsed`, `width`, `activeSection` for both side panels, plus
  `canvasPan` / `canvasZoom`. These are already persisted **server-side per user** via
  `BoardLayoutDto` (`boardApi.saveLayout`). Putting them in the URL would create a second
  source of truth for the same value and make every drag write history.
- **Tool panel visibility** — verification/simulation/exploration/recommendation panels.
  These are *input forms*, not content. A shared link that reopens someone else's
  half-filled form is noise, and they are mutually exclusive already.
- **Dialog intent** — rename, delete confirmation, device details, rule builder, logout.
  Restoring a destructive confirmation from a URL is actively unsafe.
- **Transient run state** — in-flight progress, playback frame index, animation state.
  Frequent, meaningless to another user, and would flood history.
- **Anything sensitive or bulky** — never a token, never a serialized board.

### Rules

- **One authority per value.** The URL owns `run`/`trace`/`finding`. Component state mirrors
  it one-way (URL → state); state changes navigate rather than assigning locally.
- **Opening an artifact is `push`** (back should close it). Correcting or clearing a stale
  param is `replace` (no junk history entry).
- **Invalid, stale, or unauthorized params degrade to the plain board** with one
  page-level explanation — never a fabricated empty result, never a silent redirect loop.
- **Back/forward must restore the surface**, not just the address bar.

## 2. Feedback semantics

One intent, one mechanism. Pick by **how long the information stays true** and **whether the
user must act**.

| Situation | Mechanism | Why |
| :--- | :--- | :--- |
| Operation succeeded, result visible on screen | **nothing** | The updated UI *is* the feedback. A toast repeating it is noise. |
| Assistant changed shared state | `notifyInfo` after authoritative refresh | The result may be visible, but its AI origin is not; the receipt makes agency perceptible without blocking use. |
| Operation succeeded, result not visible | `notifySuccess` (toast) | Short, non-blocking confirmation. |
| Transient failure, retryable, non-blocking | `notifyError` (toast) | |
| Blocked by current state (e.g. playback open) | `notifyBlocked` (toast) | Explains *why* and what to close. |
| Field-level validation | **inline, next to the field** + `aria-describedby` | Never a toast: the user needs it while fixing the field. |
| Page/section failed to load; critical state unknown | **persistent banner** with retry | Must survive until resolved; a toast disappears before the user can act. |
| Destructive action needing agreement | `confirmDestructive` | Uniform title/body/danger button; resolves `false` on cancel. |
| Diagnostic the user cannot act on | `acknowledge` | Alert with an optional `tone`; may carry a VNode for per-field detail. |
| Permanent account deletion | `AccountDeleteDialog` | Needs password + typed confirmation, so it is a bespoke form, not a message box. |
| Background async task | task indicator / run history | Not a toast per state change. |

### Rules

- **Never `window.alert` / `confirm` / `prompt`.**
- **One mechanism per outcome.** Never a toast *and* a banner *and* an inline error for the
  same failure.
- **Toasts are for what the UI cannot already show.** Before adding one, ask what changed
  on screen.
- **Assistant agency is explicit.** Show one localized receipt only after the corresponding
  authoritative refresh succeeds. Preview, read-only, rejected, unchanged, and unaccepted
  cancellation results show no action receipt. Persisted run history labels assistant-originated
  work and unknown legacy provenance; direct user work needs no origin badge.
- Identical error toasts are grouped with a repeat count; concurrent refresh paths must not
  stack the same message over the working surface.
- Same semantic ⇒ same component, wording shape, icon, button order, focus behaviour.
- Error text keeps what helps the user act; **no stack traces, no internal identifiers.**
  Raw backend diagnostics belong in Technical Details or the console.
- Prefer stable reason codes over free-text; fall back through `utils/userMessage.ts`.
- **A disabled submit needs a visible reason.** Derive both from one computed value (e.g.
  `specConditionBlockedReason`) so the button and the message can never disagree, and point
  the control at it with `aria-describedby`. If the form already blocks the action, the
  handler must not also toast — that is the duplicate-feedback rule.
- Never surface a client-side `error.message`. A transport or programming failure
  ("connect ECONNREFUSED …", a `TypeError`) is console diagnostics; show the backend's
  `message` only when `utils/userMessage.ts` says it matches the active locale, else a
  translated fallback.
- `confirmDestructive` resolves `false` on cancel and dismissal — cancelling is an ordinary
  outcome, never an exception a call site has to catch. Use `dismissOpenConfirmation()` when
  the surface that raised a confirmation goes away underneath it.

## 3. Undo, and what it is not

These are different operations with different controls. Conflating them is how a "go back" button
ends up destroying work.

| Intent | Mechanism | Scope |
| :--- | :--- | :--- |
| Reverse a persisted board edit | **Undo** (`Ctrl/Meta+Z`), server journal | Device create/update/rename/delete, Environment Pool edits, rule/spec create/delete, rule reorder, automatic-fix apply |
| Re-apply an undone edit | **Redo** (`Ctrl/Meta+Shift+Z`, `Ctrl+Y`) | Same |
| Stop work that is still running | **Cancel / Stop** on the task | Verification, simulation, exploration, fix search |
| Discard a finished run's record | **Delete** in run history | Completed runs (not reversible) |
| Hide a surface | dialog **close/dismiss** | No data change |
| Move between viewed artifacts | browser **Back/Forward**, `?run=` deep link | No data change |
| Fix a typo in a field | the field's **native** undo | Never intercepted |

### Rules

- **The server journal is the authority.** The client keeps no snapshot stack and never inverts an
  edit locally; every undo response carries the authoritative collections and the remaining
  availability, and a fresh page reads availability from the server.
- **The journal entry commits with the edit it describes.** A journal write that could land without
  its edit (or vice versa) would offer an undo to a state that never existed.
- **Undo never overwrites newer work.** If the affected record changed after the edit was recorded,
  the undo is refused with a conflict and the board is left untouched.
- **A failed undo response is not proof that no write committed.** A non-`409` transport or response-
  contract failure is an unconfirmed outcome. Reconcile the complete authoritative snapshot through
  the board-mutation queue before reporting it; if refresh also fails, say the outcome is unknown
  and do not invite an immediate retry. A `409` proves this request wrote nothing but still requires
  refresh because the conflict proves the local board may be stale.
- **A new edit invalidates redo.** Redoing an abandoned branch would silently overwrite the new
  edit, so the branch is discarded rather than left as a trap.
- **Nothing to undo is a normal outcome**, not an error, which makes repeated presses idempotent.
  A successful undo must make redo available, a successful redo must make undo available, and a
  `NOTHING_TO_APPLY` response must mark the requested direction unavailable; reject a response that
  contradicts these invariants instead of rendering impossible button state.
- **Confirmed scene replacement/clear is a history boundary.** It can also replace template
  snapshots, so an inverse over only the four visible collections would leave hidden catalog
  effects behind. Automatic-fix apply is different: it owns one ordered rule-set transition and is
  reversible as one user action.
- **Async runs are not undoable.** Cancel, stop, and delete-result are separate, and none of them
  is spelled "undo".
- **Never intercept a keystroke in a text field, a `contenteditable` region, or during an IME
  composition.** A user fixing a typo must not resurrect a deleted rule.
- **Undoability follows the user's unit of work, not the storage shape.** Rule reorder changes no
  individual record — only their order — but it is reached through an explicit up/down button, so
  one press is one edit the user expects `Ctrl+Z` to take back. Its journal entry stores the
  previous *ordering* (`RuleOrderSnapshot`) instead of a record snapshot. Device deletion spans a
  device, cascaded rules/specifications, their positions, and Environment Pool changes, but the user
  confirmed one deletion, so it is one compound journal entry. Conversely, a change the
  user never performed as a discrete action is not a candidate just because it is easy to invert.
- **Every ordinary targeted semantic mutation goes through one owner.** `board/semanticCommit.ts` applies the
  authoritative collections and then everything derived from them — canvas edges, dangling focus,
  undo availability, verdict staleness — in a fixed order. Call sites pass the result; they do not
  hand-assemble the follow-ups. That scattering is exactly what let reorder skip undo availability
  and let undo skip the canvas edges, each masked by a later refresh that happened to repair it.
  Reaching the right state "because some later refresh runs" is correct by accident. A server-
  confirmed semantic no-op still reconciles its authoritative collection and availability but does
  not stale a valid verdict. Partial and full refreshes reuse the same focus reconciliation rule, so
  an item removed by another tab or by a response-lost mutation cannot remain selected.
- **Whoever changes the journal must re-read it.** The journal is the authority for what is
  reversible, so a path that changes it without carrying availability in its own response has to
  re-read it. Two mechanisms cover this: scene replace/clear calls
  `notifyUndoJournalCleared()`, while reversible mutations either carry availability in their
  response or explicitly reload it; any wholesale semantic reload
  (`refreshBoardSnapshot`) re-reads availability explicitly at the end. Note that a board
  invalidation does **not** cover the publishing tab: `BroadcastChannel` does not deliver a message
  to the context that posted it, and `publishBoardInvalidation` only calls `postMessage` — other
  tabs reload, the origin tab relies on its own explicit re-read. The assistant relies on that
  explicit path: its device/rule/spec tools use the same journal-recording service methods the UI
  does, so an assistant-created device or rule is exactly as reversible as a user-created one.
  Verified end-to-end
  against the real model in `e2e/live-ai-no-mock.spec.ts`.
- **Clearing unusable history is explicit.** After an undo/redo conflict, the UI may offer to clear
  the journal only after explaining that the current Board stays unchanged and all undo/redo entries
  will be removed. It first reads `/board/edits/clear-preview`; `POST /board/edits/clear` carries that
  opaque impact token, so another tab's edit/undo/redo during confirmation causes `409` instead of
  deleting newly changed history. A successful clear returns empty collections and both availability
  flags false; it is not itself an undoable Board edit.
- **The assistant cannot silently delete.** Destructive AI tool actions are gated behind an explicit
  two-step confirmation token (`AiDestructiveActionGuard`), so a single turn can create a rule but
  not remove one. Do not write tests or features that assume otherwise.
- **Availability is a query.** `GET /board/edits/availability` returns the two booleans and empty
  node, Environment Pool, rule, and specification collections; it must never be treated as an
  authoritative board update. Because this read runs outside the mutation queue, an authoritative
  mutation response invalidates every read already in flight, and only the latest-started concurrent
  read may update the affordance.

## 4. Action emphasis

A user needs to know which control is *the* next step. If several controls claim that role, none of
them holds it.

This was measured, not assumed: on an empty Board, 14 of 38 visible controls carried primary-action
weight, 8 of them in the action dock, because every dock button was an opaque 700-weight fill in its
own hue. The dock already grouped run actions and AI suggestions separately in markup, but both
groups were painted identically, so the grouping was invisible.

### Rules

- **Emphasis follows consequence.** A control that drives the verifier or writes the model is
  primary and may carry a saturated fill. A control that only *proposes* a change — the AI
  suggestion tools — is secondary: card surface, hairline border, no shadow.
- **Demote rather than hide or disable.** A quieter control is still visible, focusable, named, and
  full-size. Hiding it costs discoverability, and a `disabled` element is unreachable for assistive
  technology, so neither is a substitute for lowering emphasis.
- **A category keeps its colour, but not as a fill.** The AI tools each keep their hue on the icon
  and active state. Removing the hue entirely would make four similar buttons harder to tell apart —
  the opposite of the goal. Colour distinguishes *kind*; weight distinguishes *importance*.
- **State never depends on colour alone.** The open-panel state adds an inset border alongside its
  tint, and a running tool keeps its animated halo.
- **Do not spend a new hue on a new category.** Eight saturated hues accumulated one feature at a
  time, each locally reasonable. A new dock entry belongs in an existing group at that group's
  weight.

`views/board/actionDockHierarchy.spec.ts` pins this, including that run actions must *stay* primary:
demoting everything is the same failure as emphasising everything.
