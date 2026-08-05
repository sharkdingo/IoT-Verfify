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

### Three tiers, because the product has three kinds of action

The first pass of this rule separated *run actions* from *AI suggestions* and stopped there, which left a
second flattening inside the run group. Measured on a loaded board, four controls rendered
**byte-identical** — `rgb(37, 99, 235)` fill, 400 weight, 124x44 box, 10.4px radius, same shadow:

| Control | What it returns | Tier |
| :--- | :--- | :--- |
| **Verification** | a formal NuSMV proof or a counterexample | `--primary` — filled |
| **Simulation** | one concrete trace; proves nothing | `--evidence` — tinted + bordered |
| **Explore** | bounded *candidate* counterexamples | `--evidence` — tinted + bordered |
| **Run History** | a read-only view of past results; writes nothing | `--view` — neutral |

This is a product-semantics rule wearing a visual form. `CLAUDE.md` already requires that a fuzz finding
never be dressed as a verdict; painting Explore exactly like the verifier is that same overclaim in the
visual layer. Colour still marks the family — all three are accent, no new hue — and weight now marks the
epistemic claim. `--view` is deliberately *not* `--suggestion`, which means "this proposes a change you may
accept"; Run History proposes nothing, so borrowing that variant would misdescribe it.

**A tier is not enough on its own.** An independent review of the retiered dock ranked the four correctly and
called the hierarchy deliberate, but found a real remaining gap: Simulation and Explore "look like equivalent
run modes, and none indicates what kind of result it produces". A visual tier can say *how important*; it
cannot say *what you will get*. So each tooltip carries a second line naming the outcome — "Returns one
concrete trace — not a proof", "Bounded search for candidate counterexamples — finding none is not safety",
"Formal NuSMV result: a proof or a counterexample" — at the type floor rather than below it, because that
sentence is what stops a bounded search being read as a proof.

**A quiet tier still needs a visible edge, and "too quiet" turned out to be measurable.** Two independent
reviews of the retiered dock — one per theme — both called Run History "too quiet" and "easy to miss". That
reads like taste until you measure it: both quiet tiers have a surface almost indistinguishable from the panel
behind the dock (1.22:1 for `--evidence`, 1.10 for `--view`), so the border alone carries the boundary, and it
was **1.48:1**. WCAG asks 3:1 for a control boundary, so the reviews were describing a real failure — the edge
of the control was effectively invisible. Both borders were raised to clear 3:1 in both themes. Demoting a
control lowers its emphasis; it must not stop it reading as a control.

The measurement also **refuted** three claims from the same reviews, which is why it ran first: radius is not
uniform (5 distinct values, 55 of 115 surfaces at `0px`), elevation is already restrained (103 of 115 have no
shadow), and accent fill is not overspent (7 of 174 controls, all of them run actions or active tabs). A
converging impression is a reason to measure, not a finding.

---

## 5. Ink and paper: a role has two halves

Every semantic role token exists in two jobs, and one value cannot do both.

`--accent`, `--danger`, `--warning`, `--success` are tuned to be legible **as text on the page
ground**, which is why the dark theme *lightens* them. Used as a **fill with light ink on top**, that
tuning inverts. Measured across 60 sites in dark theme:

| Token | Dark value | White ink on it | Light theme | Verdict |
| :--- | :--- | ---: | ---: | :--- |
| `--accent` | `#60a5fa` | **2.54** | 5.17 | fails AA, dark only |
| `--accent-strong` | `#93c5fd` | **1.80** | 6.70 | fails AA, dark only |
| `--warning` | `#fcd34d` | **1.44** | 5.02 | fails AA, dark only |
| `--danger` | `#fca5a5` | **1.90** | 4.83 | fails AA, dark only |
| `--success` | `#6ee7b7` | **1.52** | 3.77 | **fails in both** |

`--accent-strong` is the *hover*, so contrast fell as the user interacted with the control. Light
theme passed almost everywhere because one dark blue happens to serve both jobs there — which is why
this survived several review passes, and why a light-only check will not find it.

### Rules

- **Fill with `--<role>-fill`; write with the bare role.** The fill halves are solved against two
  constraints at once: light ink at ≥ 4.5:1, and the fill against its panel at ≥ 3:1 so the control
  keeps a visible edge.
- **The base fill does not change with the theme; the hover must.** A ground that does not flip means
  one ink is correct everywhere and no markup has to guess. "Darker" and "brighter" swap meaning with
  the ground, so `--accent-fill-hover` is `#1d4ed8` in light and `#2f6fe4` in dark — both above AA,
  which the `--accent-strong` hover they replace was in neither theme.
- **A fill with no ink on it keeps the bare role.** Progress bars, playback rails, pulse rings, 1px
  accent stripes, the selected-step dot: their obligation is 3:1 against a *neighbour*, not against
  text. Retargeting them would darken decoration for no reason. 24 of the 84 fill sites are this case.
- **A theme-flipping ground has no correct ink — fix the ground.** The six panel banners used
  `--accent`, so black ink measured 4.06 light / 8.26 dark and white the reverse. No single markup
  could be right, and one panel title rendered at **1.44:1**. Pinning the banner to `--accent-fill`
  fixed all six at once; forking the ink per theme would have doubled the surface area of the bug.
- **Ink on a fill is measured, not eyeballed.** `text-white/85` on `--accent-fill` is 4.19 — under AA
  by a margin no one sees by looking. `/90` is 4.50.

### Disabled: desaturate, do not fade

`opacity` multiplies whatever it is applied to, including the label. A disabled control still has to
be readable, because it is the thing explaining why the action is unavailable.

Measured: a filled primary button at **2.42:1** while disabled, the exploration panel's "Select all"
at **2.00**, undo/redo at **1.80** — the last disabled on every fresh board, so the first state of
those controls anyone sees. The pre-existing `board-panel-submit:disabled` treatment was also wrong at
**1.75**, because it desaturated toward a *white* card, removing the contrast its ink depended on.

- Filled actions use `board-action-disarmed`, which swaps the fill for a desaturated neutral
  (`--accent-fill-disabled`, white ink 4.76) and leaves the ink opaque.
- Muted text simply stays muted; the cursor and the `disabled` attribute already carry the state.
- **The other 69 opacity-faded controls were measured and left alone.** Opacity is only a defect where
  it multiplies a value already near the floor, so an audit of the declarations would have produced 69
  pointless edits. Measure the rendered state instead.

### Structural neutrals have a floor too

Slate/gray/zinc are legitimate — they are the structural greys, not semantic roles. But `slate-400` is
**2.56:1 on white**, and it was set on 126 text elements. Body text uses the 500 step or darker in
light theme; `dark:text-slate-400` is correct on a dark card, where the same value is 5.71.

Pinned by `styles/__tests__/neutralTextContrast.spec.ts` and
`styles/__tests__/semanticColourOwnership.spec.ts`.

## 6. Text size: the floor is not the target, and headings need a tier

`--iot-font-min` (0.6875rem = 11px) is the smallest size any interface text may be declared at, enforced by
`styles/__tests__/typographyFloor.spec.ts`. Two things that rule does *not* say, both of which produced real
defects:

- **A heading sized just above the floor is not a heading.** The action dock's "Board tools" was `0.72rem` at
  weight 800 against `--iot-font-min`/700 group labels *beneath* it — 0.52px of difference at a heavier
  weight, so two levels of heading rendered as one and a reader saw three rows of small uppercase text with
  nothing marking which named the panel. It passed `typographyFloor` (11.52px over an 11px floor) throughout.
  A panel heading uses `0.875rem` (the tier the side-panel titles use); its subheadings use the 11px floor.
  Leave at least 2px between two levels that appear together.
- **Pick a step on the scale, not a nearby number.** `0.72rem` and `0.78rem` each appeared at multiple sites
  and matched nothing else in the product, sitting a fraction of a pixel from `0.75rem`, which twelve other
  board labels already use. A bespoke value costs a reader the ability to tell two levels apart and costs the
  next contributor a decision that was already made.
- **`text-transform: uppercase` makes text read smaller than it measures.** It costs roughly 15% of apparent
  x-height and removes word shape, so it is a poor choice for anything already near the floor, and for a
  four-character label it is most of why the label looks too small. Reserve it for the smallest
  section labels, where the loss of word shape is the point (they are scanned, not read).

Pinned by `views/board/actionDockHierarchy.spec.ts` for the dock, which is where the tier inversion was.

## 7. Depth is a scale, and it means containment

Elevation says *what kind of thing* something is, the same way the radius scale does. Three steps, and one
distance means one thing:

| Token | Means |
| :--- | :--- |
| `--shadow-raised` | a control lifting off the surface it sits on |
| `--shadow-floating` | a transient chip, popover, or canvas node above content |
| `--shadow-elevated` | a panel floating above the page |

`--shadow-elevated` used to be the only token, so anything needing a different depth wrote its own literal —
eight distinct neutral elevations in the board alone, no two agreeing. Three rules follow:

- **Never hand-write a neutral elevation.** A literal `rgba(15, 23, 42, …)` shadow does not follow the theme,
  and the dark theme's token is both deeper and more opaque for a real reason: a shadow works by darkening its
  ground, and a near-black ground has almost no headroom left, so the light theme's alphas vanish on it.
- **Pick the step that describes the thing.** The dock's hover tooltip carried `--shadow-elevated`, an
  18px/42px panel lift, on a two-line hover chip — so hovering a dock button dropped a panel-sized shadow
  across the canvas. That is not a matter of taste; the depth was making a false claim about the element.
- **Hover raises one step. It does not change hue, ground, or edge.** The canvas node used to swap its resting
  hairline (a dark line at 12% of `--text`) for `rgba(255, 255, 255, 0.72)` on hover, which inverted the edge
  from dark to white in light theme and drew a bright outline on a navy node in dark. A colour change dressed
  as a depth change reads as a glitch rather than a lift. Likewise, a control inside an already-elevated panel
  should not carry its own lift: emphasis between tiers is the fill and the border (§4), not depth — the
  verification button's stray `shadow-lg` made one of eight dock buttons float above the strip it belongs to.

One more thing that is depth-adjacent and caused the same "why is some white and some not" reaction: **two
tiers that mean the same thing sit on the same ground.** Run History and the four AI suggestions are both
"not the primary action", yet sat on `--board-control-bg` and `--board-card-bg` respectively, four rows apart
in one strip. A background change down a vertical list implies a *category* change. When you do move a
control's ground, re-measure its border — the 3:1 component minimum is against the ground, so changing the
ground invalidates the old measurement.

- **Three steps means three, not "three plus whatever else exists."** Two more elevation tokens had grown
  alongside `--shadow-elevated`, and both carried the same bug — which is what a fourth owner buys you.
  `--iot-node-shadow` and `--iot-color-card-shadow` were declared as `rgba(15, 23, 42, 0.9)` in dark theme: the
  *light* palette's navy at 90% opacity, where every dark shadow is `rgba(2, 6, 23, …)`. The node one was worse
  than a wrong colour — the node's resting rule used the scale while its four state rules (focus, focused,
  trace-active, trace-changed) used that token, so highlighting a node silently changed its base depth on top
  of adding the ring. A state should add to a depth, not replace it.
- **An edge-attached bar is not a floating panel.** The board nav is full width, flush to the top, and already
  has a bottom border marking the boundary; a panel lift under something with nowhere to float *to* reads as a
  heavy smear across the viewport. All its shadow has to say is "content scrolls under this."

Pinned by `styles/__tests__/elevationScale.spec.ts`, which covers `base.css` and `board.css`. **Twenty
hand-written elevations remain outside the board** (`ChatView`, `Landing`, `PublicHeader`, the two toggles,
`ToggleSwitch`, `AccountDeleteDialog`, and the `ControlCenter`/`CanvasBoard` scoped blocks). They are the same
defect; each needs its depth chosen and then measured on its own surface.

## 8. A scoped rule outranks a Tailwind utility on the same element

Vue compiles `<style scoped>` selectors with a `[data-v-…]` attribute, so `.foo { max-width: 100% }` is
specificity **0-2-0** while Tailwind's `.max-w-4xl` is **0-1-0**. The scoped rule wins. This is not a rare
edge: it has produced three separate user-visible defects, and each one looked correct in review from both
sides — the template states the intent, the stylesheet states a reasonable-sounding rule, and only the
rendered pixels disagree.

- **`DeviceDialog` filled the screen.** `max-w-4xl` (896px) in the class list, and
  `.device-dialog-surface` in a scoped `max-width: 100%` list whose purpose was containing overflow in the
  dialog *body*. Measured on a 2548×1465 display: **2516×1433, 98.7% × 97.8% of the viewport**, for content
  that needs 896px. It read as the app being replaced by a settings screen rather than a panel opening over
  the board. Removing the surface from that list restored the cap (896px, 35% of the width).
- **An accent icon rendered grey.** `.device-runtime-box span { color: inherit }` — there to neutralise
  Tailwind slate utilities the markup still carries — also matched the one span asking for
  `board-text-accent`. Measured `rgb(148,163,184)` where `--accent` is `rgb(96,165,250)`.
- **A hover state half-applied.** Role-class hover variants declared in `board.css` lost to
  `.iot-board .board-side-panel .text-slate-500`; the fix was source *order*, not specificity, and two
  attempts at raising specificity failed first.

### Rules

- Do not put a `max-width`/`max-height` in a scoped block on an element that also carries a Tailwind
  `max-w-*`/`max-h-*`. Constrain the children that need containment, not the capped element itself.
  `styles/__tests__/scopedWidthOverride.spec.ts` fails on the overlap, per axis.
- A broad scoped selector (`span`, `p`, `button`) must exempt the role classes used inside it —
  `span:not(.board-text-accent)` — or the role has no way to win in that component.
- When a rule that looks right does not apply, read the winner from CDP matched-styles rather than
  reasoning about specificity. At equal specificity, source order decides, and raising specificity is then
  the wrong fix.
- Dialog height caps: the siblings use `85vh`/`88vh`, which leaves visible margin so the surface reads as a
  panel over the board. `calc(100vh - 2rem)` reads as a takeover.
