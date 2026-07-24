# Changelog

All notable changes to IoT-Verify are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/). **Until a formal release/tagging
process exists, changes are recorded under `Unreleased` with dated entries.** When the
first tagged release is cut, the relevant entries will be moved under a version heading
(e.g. `[1.0.0] - 2026-xx-xx`).

These entries were migrated from the implementation-alignment sections
(§13, §14) of the former `backend/NuSMV_Module_Documentation.md`, which mixed change
history into a technical spec. The spec content itself now lives under
`docs/architecture/`.

---

## [Unreleased]

### 2026-07-24

#### Changed
- Made scene-recommendation completion use explicit minimum device, automation-rule,
  and specification targets instead of treating any non-empty category as complete.
  The backend and Board now validate the same target counts, report missing versus
  insufficient content deterministically, and show unmet targets before scene application.
- Removed the development-only login collision reader. Registration keeps phone-shaped
  usernames invalid, and login now classifies an identifier once and queries only the
  phone or username namespace instead of probing both for obsolete conflicting rows.
- Made current development persistence contracts strict at every history boundary. Fuzz
  input envelopes now require all six frozen-snapshot fields with their canonical JSON
  types, and full run reads recompute the same normalized semantic fingerprint used at
  write time instead of trusting a well-formed digest plus matching item counts.
- Made verification, simulation, and counterexample-search task mapping enforce the
  service's actual lifecycle state machine: identity, progress, timestamp ordering,
  processing duration, terminal metadata, failure diagnostics, saved-trace ownership,
  and result fields must agree with the persisted status.
- Made chat-stream completion a persisted protocol fact. The backend now emits a unique final
  `{ turnId, executionStatus }` terminal frame only after saving the matching assistant row;
  clean EOF without it is incomplete, while accepted failures settle to authoritative history
  even when the durable result is a user-only turn. Transport loss before response headers is
  treated as an unknown admission outcome, and failed or inconsistent history reloads keep the
  assistant locked until authoritative reconciliation succeeds.
- Made Device Details retain only still-legal dirty runtime edits when a same-node template
  schema changes. Save remains blocked until the user explicitly adopts the latest runtime or
  continues with the compatible subset; untouched drafts adopt the new schema immediately. State,
  current-state trust, and current-state privacy now reconcile as one context so a refresh cannot
  combine one state's trust/privacy overrides with a different state.

#### Fixed
- Separated chat SSE failures from model-authored text with a structured `error` frame. A
  valid assistant response beginning with the literal text `[ERROR]` is no longer mistaken
  for a server failure by the frontend, and a parsed server error is retained if the transport
  resets before its terminal frame arrives.
- Preserved quoted and code-formatted platform-action text in assistant explanations and
  translations. Sentence buffering now recognizes ASCII and typographic quote pairs, inline
  backticks, and backtick/tilde fences with longer closing delimiters. It ignores punctuation
  inside closed literal spans while final claim checking fails closed on unfinished spans, so
  an unclosed quote or fence cannot hide a later unsupported execution claim.
- Released the assistant interaction lock after an explicit early Stop or reattached remote
  execution is confirmed idle with authoritative user-only history. The frontend now removes
  optimistic output and restores the draft only when the corresponding user turn was not admitted.
- Made local chat Stop requests turn-aware and durable before transport abort. A quick Stop now
  fences a request that has not entered admission yet, cannot target a newer turn, and does not
  begin idle polling until the backend acknowledges the fence. Multiple pre-admission turns retain
  independent bounded fences, with orphan cleanup and database-level session deletion cascades.
  Remote settlement also invalidates stale initial-history reads and clears a recovered
  history-load error.
- Invalidated a coupled-scene recommendation whenever its minimums, maximums, or requirement
  text changes, so a draft generated for earlier criteria can no longer be exported or applied
  as though it satisfied the edited request.
- Made an acknowledged cross-instance chat Stop authoritative inside the terminal-message
  transaction, so the following browser abort cannot downgrade it to `DISCONNECTED` or let a
  previously computed completion/error status win. Server-observed stops now close the SSE after
  the persisted terminal frame instead of leaving the stream allocated until timeout. An explicit
  Stop also cancels the matching same-instance provider request when its database lease has just
  expired. Chat lease
  admission and renewal now also reject slow commits that leave less than one heartbeat interval
  before expiry, and each instance renews all of its active chat leases in one commit so later
  sessions cannot consume an earlier session's remaining heartbeat window. Expired-row cleanup
  now precedes renewal, with a final margin check before the scheduled pass returns.
- Ordered bounded LLM chat context by database message id and used the database clock for
  session-list timestamps, so skewed backend instance clocks cannot reorder later turns.
  A `COMPLETED` chat trace now also requires each tool execution to pair in order with the
  same tool and round's result at both backend persistence and frontend boundaries. A later
  usable result from the same tool may explicitly recover an intermediate partial result;
  unresolved partial, failed, unavailable, or confirmation-required results remain incomplete.
- Kept cross-tab assistant coordination locked when more than one chat session is active.
  Foreground refresh now prioritizes the selected active session regardless of list order,
  switches from an idle selection to authoritative active work, and hands monitoring to any
  remaining active session before Board interactions are released.
- Invalidated pending history-detail and finding-replay requests when the fuzzing-result dialog
  closes, so a delayed response cannot reopen playback after the user dismissed the result.
- Kept every Device Details action at least 44 pixels high (and the icon-only close
  action 44 pixels wide) for touch use, and restored the dedicated Door and Garage Door
  icons that were previously shadowed by the generic sensor-name classifier.
- Rejected non-positive or duplicate non-null rule ids at the shared verification and
  simulation request boundary. Unsaved rules may still omit ids, while persisted ids now
  provide an unambiguous current-canvas correlation key for triggered-rule trace evidence.
- Bound triggered-rule and compromised-link trace evidence to the exact zero-based rule
  position in each immutable run request. Fault localization and automatic-fix replay no
  longer broaden one execution probe to every rule sharing a nullable/duplicate id or label,
  and verification, simulation, and counterexample-search history now rejects missing,
  duplicate, out-of-range, or forged rule snapshots before returning full replay evidence.
  Lightweight fuzz finding summaries no longer claim `dataAvailable` before their LONGTEXT
  evidence and frozen run are loaded and validated. Finding replay now loads the full owning
  run once and selects the requested finding from its validated embedded evidence instead of
  joining independent finding and run responses. The single-finding endpoint verifies the
  run's declared `findingCount` against the actual owned-row count before returning surviving
  detail, and unavailable run summaries carrying findings are rejected. Canvas playback associates validated
  historical evidence with current
  edges only when the persisted rule id identifies one current rule; ambiguous or id-less
  evidence is left unhighlighted instead of guessing from a current list position.
- Made fault-localization conflicts follow the generated multi-mode transition semantics:
  two commands conflict only when they write different values to an overlapping mode;
  simultaneous writes to disjoint modes are reported as independent executions.
- Closed the synchronous formal-operation lease-to-commit window with a monotonically
  increasing database fencing epoch. Each admitted operation claims an epoch before
  expensive work; final history persistence locks that user's epoch row through physical
  commit and rejects a superseded epoch as well as an expired Redis lease. Ownership loss
  remains a service-unavailable failure instead of being downgraded to a usable result
  whose history status is merely unknown.
- Made verification and simulation history summaries validate the complete persisted
  state array, contiguous state indexes, and scalar count before advertising replayable
  evidence. Damaged state JSON now produces an unavailable placeholder and cannot inflate
  `counterexampleCount`.
- Made internal verification/simulation request cloning reject device-count, null-element,
  or token-provenance drift instead of silently returning or substituting `UNKNOWN`.
- Persisted the user turn and session execution lease atomically before chat dispatch, rejected
  reused per-session turn ids, and made queue rejection remove that exact turn before returning
  `503`. Ambiguous commit or cleanup outcomes now return an explicit no-terminal reconciliation
  stream instead of pretending either rejection or execution was confirmed.
- Required lowercase `trusted`/`untrusted` and `public`/`private` literals at the canonical
  device-template JSON boundary, matching the typed scene contract.
- Preserved custom `ruleString` text on rules untouched by an automatic fix; only changed rules
  are regenerated from their updated conditions/actions.
- Kept immediate verification traces replayable when history persistence fails or remains
  unknown, but removed provisional persistence identities after an unconfirmed commit and
  exposed automatic Fix only when the trace belongs to the response's confirmed saved run.

### 2026-07-23

#### Changed
- Added an explicit anti-AI-slop engineering standard to the repository, backend, and
  frontend contributor manuals: generated changes must have a named requirement or defect,
  one authoritative implementation path, boundary and failure-state coverage, synchronized
  contracts and documentation, and a maintainer-readable full-diff review before delivery.
- Codified the active-development compatibility policy in the canonical `AGENTS.md` and the
  root, backend, and frontend `CLAUDE.md` files: change all in-repository callers and tests
  together, reject obsolete or malformed development state, and do not add speculative
  old-format readers, dual writes, aliases, rolling-deployment bridges, or silent fallbacks.
- Removed the obsolete top-level verification/simulation request fields `isAttack` and
  `attackBudget`; model requests now use only the structured `attackScenario`, while the
  derived summary fields remain available in run responses.
- Made the structured attack contract explicit throughout NuSMV generation and automatic
  fix orchestration. Generator, main-module, specification, and fixer entry points no
  longer accept a separate attack boolean and budget; callers supply `AttackScenarioDto`.
  Request DTOs require a non-null scenario and explicit mode, while malformed or absent
  scenarios now fail instead of silently becoming `NONE`.
- Removed implicit `MODEL_CHOICE` provenance for fuzz input events. Current producers and
  persisted findings must carry an explicit event source; missing evidence now fails closed.
- Made the semantic model fingerprint mandatory for every counterexample-search task and
  run, removing the old count-only history comparison for rows with missing fingerprints.
- Removed persisted-trace compatibility readers that invented empty event arrays, unknown
  token provenance, model semantics from scalar columns, or template provenance from an
  unversioned manifest map. Persisted verification and simulation evidence now fails closed
  when any of those current fields or its verification-run owner is missing.
- Made automatic-fix replay require a complete current versioned template snapshot: manifest
  and device-source keys must exactly match the saved verification request, and every device
  source must be explicitly `BUNDLED` or `CUSTOM`. Corrupt persisted context now stops with a
  data-integrity failure instead of assigning `UNKNOWN` provenance.
- Made chat `turnId` a required request field. The frontend transport always supplies one,
  and the backend no longer invents correlation identity for an obsolete request shape.
- Removed legacy local timestamp parsing and the NuSMV trace parser's implicit `device.state`
  interpretation. API `LocalDateTime` requests now require a configured-zone offset, and a
  trace field named `state` is handled only through the current device declaration.
- Removed the API-level `Assignments` template field and invalid state-machine fallback.
  APIs now express only state transitions, while partial stateful templates fail closed and
  stateless templates retain their explicit non-semantic canvas placeholder.
- Made automatic-fix fault localization depend only on frozen per-transition rule-execution
  probes. It no longer reconstructs firings heuristically from current rule conditions or
  coincidental device-state changes, and unexpected device-map failures now propagate instead
  of being mislabeled as an unknown device.

#### Fixed
- Rejected device-type rows whose bundled/custom provenance is missing instead of
  treating a null `defaultTemplate` value as bundled and localizing custom model tokens.
- Rejected contradictory persisted simulation tasks before API mapping, including missing
  lifecycle fields, invalid step counts, failed tasks without an error, completed tasks
  without a saved trace, and non-completed tasks that claim one.
- Locked the specification editor while a create request is unresolved and submitted a
  detached draft snapshot, so a fast next edit cannot mutate the in-flight request or be
  erased by the previous request's success reset.
- Rejected verification and simulation model-context JSON whose required integer or
  boolean fields are missing or encoded as coercible strings/decimals. Persisted enum and
  selected-attack-point scalars must also retain their canonical JSON types instead of
  being silently reinterpreted by Jackson.
- Made Board renames compare-and-set against the name shown when the dialog opened. A stale
  edit or a different device claiming the requested case-insensitive name now returns
  `409 Conflict` before any write; the client refreshes the full semantic snapshot, preserves
  the user's draft for explicit resubmission, recognizes an already-achieved rename, and
  validates the returned old name, new name, and affected-specification count before showing
  success. Open rename dialogs now rebind to external snapshots without discarding a dirty
  draft or its original compare-and-set baseline, adopt an external rename when untouched,
  and close when the device was deleted, including after an in-flight request settles.
- Made Board device nodes theme-aware and responsive to their rendered size, kept the
  canvas camera stable when opening ordinary device details, distinguished stateless
  devices from manifest-defined states, and added pointer- and keyboard-safe move/resize
  behavior. Server snapshots now preserve every pending or active node layout instead of
  rolling back a second drag, pointer cancellation cannot leave canvas/minimap panning
  stuck, pointer resize handles collapse to one corner before disappearing when a low-zoom
  node cannot retain a 44-pixel central drag target while keyboard resize remains available,
  and the dark-theme device context menu stays inside the viewport
  with complete keyboard focus, navigation, and restoration behavior. Runtime and
  private-data badges remain readable in dark mode; hidden, inert, collapsed, or detached
  controls cannot capture modal focus; and device dialogs return focus to the originating
  node or a stable scene control even after failed or completed deletion paths.
- Preserved dirty device-runtime drafts across foreground and cross-tab snapshots with a
  field-level three-way merge: disjoint local/server edits combine automatically, while
  divergent edits to the same field block Save until the user chooses the latest value or
  keeps the local value. Normalized equivalent nullable/omitted runtime values and prevented late save/delete responses from
  reopening a closed dialog or accepting repeated destructive submissions. Stale device
  dialogs and context menus now reconcile to the authoritative node or close when it was
  deleted. A save-start edit revision also preserves input made while a runtime save is in
  flight, including the ambiguous case where the user deliberately returns to the old value;
  the authoritative baseline advances even while that draft is preserved, preventing a later
  refresh from overwriting it. Replacing a same-id device with a different runtime schema
  resets the edit session instead of mixing old fields into the new template. Correctly
  scoped dark-theme selectors now keep the complete device-details surface, runtime editor,
  controls, labels, Markdown code blocks, and information-tooltip triggers readable instead
  of leaving teleported or scoped component surfaces in their light palette.
  Device deletion previews are now single-flight, visibly identify their target, close stale
  details, menus, and confirmations after a cross-tab deletion, report that external removal
  once, restore keyboard focus to the visible Devices tab, and reconcile an already-deleted
  response without showing a contradictory failure. Every entry path now opens a cancellable
  loading confirmation, suspends the underlying details surface without discarding its draft,
  rejects malformed nested preview/delete responses, and serializes preview reads behind
  pending Board writes. Changes to the target or its actual rule/specification/environment
  impact close the stale confirmation while unrelated Board edits do not; repeated final
  confirmation still emits only one delete request.
  Runtime saves now send both the edit baseline and desired complete value; the backend
  compares the baseline under the per-user database write lock and returns an explicit
  `DEVICE_RUNTIME_STALE` conflict before writing when another tab changed the device. Runtime
  template names, runtime values, variable/privacy names, and security labels are now
  canonicalized at every complete device-write boundary. A runtime no-op also repairs a
  non-canonical stored representation instead of reporting an unchanged value that remains dirty.
- Localized bundled model tokens at the display boundary without changing canonical model
  values, completed compact and short-viewport drawer behavior, improved floating-panel
  focus and Escape handling, and added dark-theme surfaces for device, verification,
  simulation, fuzzing, and fix-result dialogs. Scene-import manifest validation now presents
  structured reasons in the selected UI language. Default-template reset previews now enumerate
  exact Environment Pool changes, localize each old/new value only from server-confirmed
  bundled provenance, and warn when verification and simulation must be rerun.
  Device API names and states, recommendation details, and automatic-fix conditions now
  localize bundled model tokens and `in`/`not in` relations while preserving custom model
  tokens verbatim. Every token in the bundled device manifests is covered by a data-driven
  Chinese/English localization regression, while custom `workingState` values remain visibly
  distinct from bundled provenance.
- Made fault-localization and automatic-fix token localization provenance-safe: new traces
  freeze bundled/custom source per device, entries without provenance stay unknown and preserve
  raw text, shared environment values require unanimous source provenance, and parameter,
  condition, action, and end-state labels no longer translate custom tokens that happen to
  collide with bundled names. Counterexample-search tasks now persist frozen model input and
  server-only provenance atomically in one strict, versioned envelope. Unsupported,
  incomplete, or unversioned development data and findings with missing or conflicting
  source fields are rejected instead of inferred from the current template catalog. Findings
  emit the source on device, local-variable, and shared-environment finding states. Canvas
  playback now derives state-machine presence, device
  state, variable labels/values, and security badges only from that frozen trace evidence;
  changing the current template cannot relabel historical nodes. Fuzz domain previews also
  normalize Board and model device ids before applying bundled-token localization, including
  generated UUID ids whose hyphens become NuSMV underscores. Verification, simulation, and
  counterexample-search replay now share nested trace validation for device/variable values,
  triggered-rule snapshots, trust/privacy labels, and token provenance, so malformed evidence
  is rejected before rendering or localization. The shared validator accepts legitimate
  stateless empty state/mode values but rejects duplicate identities, trust/privacy evidence
  in the wrong list, incomplete device or variable membership, local/global provenance
  mismatches, missing/null provenance, and device or environment provenance that changes
  between saved states.
- Stopped chat, verification, simulation, and counterexample-search workers after a full
  lease TTL without database confirmation; enforced stored-run quotas for synchronous
  verification and saved simulation; and bounded verification and simulation history
  summaries by their configured stored-run quotas with bounded result sets. Formal
  and simulation playback now rejects non-contiguous or non-one-based persisted states, and
  trace placeholders that are damaged or do not explicitly confirm availability no longer
  inflate the replayable counterexample count in verification run summaries or details. Task lease renewal now locks each row before
  sampling the database clock, so lock wait cannot revive or locally confirm an expired lease, and
  synchronous result transactions recheck distributed admission immediately before commit.
  Long AI tool transactions no longer block chat lease heartbeats, ordinary AI writes recheck
  ownership immediately before commit, and a heartbeat delayed behind a row lock cannot
  revive a lease that expired while it waited. Redis admission acquisition and renewal now
  measure confirmation from before each round trip, so a delayed response cannot extend the
  local validity window beyond the distributed TTL.
- Bounded process-local authentication rate-limit state with a fail-closed active-window
  ceiling. Capacity exhaustion now has its own `CAPACITY` scope, reports the earliest tracked
  expiry instead of a misleading full-window delay, and shows localized busy feedback instead
  of blaming an account or source. Cross-account custom-template preview/delete lookups now
  return the same not-found response as an absent template.
- Rejected ambiguous legacy phone/username logins when the supplied password matches both
  colliding accounts, instead of selecting the phone-owned account by lookup order.
- Replaced scenario recommendation's model-authored rationale with a deterministic summary
  of the final retained scene, and separated structural verification readiness from
  semantic-coverage warnings for filtered candidates, missing automation rules, and
  devices unused by every retained rule/specification. A submit-ready draft therefore no
  longer implies that it satisfies the user's natural-language requirement or forms a
  closed automation loop.
- Made zero-tool assistant replies explicitly state that no platform tool ran and no current
  Board state was read or changed. Provider prose on every turn is sentence-buffered before
  display; explicit claims of tool evidence or current-platform completion/mutation are replaced
  with exact successful server tool records, or a deterministic warning when none exists,
  instead of being streamed or persisted. All later provider prose is suppressed and an
  otherwise completed turn is downgraded to `PARTIAL`. API documentation, historical
  descriptions, and ordinary sample content are not treated as platform mutations.
  Zero-tool replies
  now persist as the existing `PARTIAL` status and display as "No platform tools ran" only
  when a non-empty trace has no tool execution or result activity; a missing trace or a tool
  that started without a result remains explicitly partial. `COMPLETED` is reserved for turns
  that actually invoked at least one platform tool, without implying that every user objective
  completed. Structurally valid but
  semantically incomplete scenario recommendations
  persist and report `PARTIAL` instead of being presented as fully successful. The
  standalone scenario-recommendation REST
  contract now carries the same objective status and issues, and both backend and frontend
  recompute them from the returned canonical scene instead of trusting inconsistent model
  claims. Chat history and live progress are structurally validated at the frontend boundary;
  malformed roles, content, cursors, counters, stages, outcomes, or execution traces are
  rejected instead of reaching rendering and being mistaken for a verified terminal state.
  Terminal assistant persistence is now single-attempt and fail-visible: trace serialization
  failures or database write failures emit an explicit SSE error instead of normal completion
  or a second misleading disconnect row. Chat history restores only explicit, structurally
  valid persisted traces; a `COMPLETED` row with missing, damaged, guarded, or non-usable trace
  evidence has its status cleared. Empty or malformed AI-tool result objects fail closed rather
  than increasing the successful-step count.
- Kept Board account actions reachable at tablet widths, made the permanent-account
  deletion dialog scroll within short viewports, and stopped Tab or other navigation keys
  from satisfying its deliberate-edit guard. Long canvas labels now expose their full text
  on hover, the mobile brand target remains at least 44 pixels, and the action dock scrolls
  to every command in short landscape viewports while its mode control announces whether
  labels are expanded.
  Refreshed the real browser check to use the current scene-replacement, layered-history,
  simulation, and eight-tool contracts and to fail on page exceptions.

### 2026-07-22

#### Changed
- Added one explicit application time-zone contract (`IOT_VERIFY_TIME_ZONE`, default
  `Asia/Shanghai`): API date-times now include the configured UTC offset, while legacy
  offset-free request values remain accepted and mismatched supplied offsets are rejected.
- Changed chat history to a cursor-paged contract with bounded raw-row scanning and an
  in-panel "load older" workflow. Chat catalogs now retain at most 100 sessions per user,
  while individual requests remain limited to 10,000 characters.
- Added a dedicated 64 MiB authenticated scene-replacement boundary so portable scenes
  can round-trip referenced template snapshots and embedded icons without widening the
  4 MiB limit for unrelated JSON endpoints. Device-type catalogs and manifest arrays now
  have explicit capacity limits.

#### Fixed
- Enforced formal-operation admission at the service boundary for REST and assistant-tool
  callers, including compatibility fix-recomputation paths; cancelled nested solver work on
  interruption, and terminated descendant NuSMV processes so cancelled or lease-lost work cannot
  continue consuming formal capacity.
- Made interactive recommendation and automatic-fix status/cancellation token-fenced and
  observable across backend instances, including renewable cancellation ownership and
  stale-request-id protection; browser stop recovery now tolerates registration races but
  exits with a visible uncertainty warning after bounded status failures. Redis status
  scripts now use single-field `HSET` calls so older development servers keep distributed
  tracking instead of rejecting the registry script and silently falling back to local state.
- Kept asynchronous simulation completion in the user-lock-before-task-lock order used by
  account deletion, preventing completion and deletion from deadlocking or persisting a
  trace for a deleted account.
- Made method/media negotiation errors deterministic (`405`, empty `406`, and `415`),
  separated case-sensitive authentication rate buckets, rejected phone-shaped new
  usernames, resolved legacy phone/username login collisions by the matching password,
  and made invalid-login messages account-neutral for both identifier types.
- Added recoverable chat-history loading and single-flight session creation, atomic
  cross-tab authentication snapshots, account-scoped workspace/assistant remounting, and
  request-token-bound `401` handling so a late response cannot expose or sign out the next
  account; also added explicit account-deletion confirmation typing and bounded
  completed-task/fix/recommendation recovery from transient backend failures.
- Treat account-deletion network failures and `5xx` responses as an unknown commit outcome:
  the client now clears only the matching local session and asks the user to sign in again
  to confirm whether the account still exists, while explicit `4xx` rejections remain
  correctable in the open deletion dialog.
- Sanitized AI Markdown links and disabled raw HTML, blocked automatic third-party image
  requests, removed dynamic template-icon HTML rendering, and added a deployment CSP
  example as defense in depth.
- Made chat stop requests close the active OpenAI stream or cancel a pending planning
  future instead of waiting for another provider chunk or timeout.
- Bounded AI tool calls, UTF-8 result size, and stored messages per conversation; detailed
  template results now exclude UI-only icons and oversized results become structured
  unavailable outcomes.
- Canonicalized usernames across registration, login, account confirmation, and throttling;
  validation now counts Unicode code points and rejects invisible formatting controls.
- Made the documented MySQL username collation case- and accent-sensitive, with an
  idempotent startup migration that changes only `app_user.username`; fresh and upgraded
  databases retain the same schema-level comparison semantics for every other text column.
- Restored standalone scenario recommendations by keeping chat-only draft metadata out of
  the strict REST response, and stopped read-only rule/specification recommendations from
  causing unnecessary cross-tab Board reloads.
- Serialized specification recommendations with one canonical `aConditions` property,
  removing the case-different `aconditions` duplicate that broke case-insensitive JSON
  clients.
- Preserved the original JSON status and error envelope for synchronous chat-stream
  rejections when standards-compliant SSE clients send `Accept: text/event-stream`, instead
  of allowing internal error dispatch to misreport business errors as `401`.
- Excluded credentials, provider keys, private chat payloads, and destructive-action
  capability tokens from automatic string logging; provider failures no longer log external
  response bodies, including cancellation paths, and model-response validation logs retain
  only candidate indexes, stable reason codes, and exception classes rather than generated
  or user-derived values.
- Enforced durable AI workflow-state ownership with a composite chat-session cascade and
  startup orphan repair, and removed inactive NuSMV lock markers left behind after direct
  temporary-directory cleanup.
- Distinguished valid stateless device placeholders from broken stateful-template fallback,
  so no-mode device creation no longer reports a false initialization warning.
- Self-hosted application and Material icon fonts, removing the Google Fonts dependency.
- Removed an unused Bouncy Castle runtime dependency from the backend package.
- Removed unused frontend UI and legacy Markdown dependencies and their inactive resolver.
- Restricted custom template icons to self-contained `data:image` values.
- Corrected nested template/chat controls and completed keyboard focus handling for
  template confirmations and verification results.
- Updated pinned GitHub Actions dependencies to their Node.js 24-based releases, removing
  the hosted-runner deprecation warnings while retaining immutable commit pinning.
- Made missing NuSMV model validation deterministic before artifact locking, keeping the
  Linux and Windows test paths aligned while retaining the post-lock race check. CI and E2E
  account probes now use credentials that match the current registration contract.
- Aligned interactive recommendation and automatic-fix request-id validation across DTOs,
  controllers, and execution services, and preserved accepted chat turns when a successful
  HTTP response later exposes no readable SSE body.
- Added visible feedback when explicit chat-session creation fails or returns an incomplete
  response, kept the mobile session list open on failure, and removed duplicate serialization
  of large portable scenes during export.
- Stopped an old synchronous or assistant worker when its Redis admission lease is lost or
  remains unconfirmed through its TTL, preventing it from overlapping a replacement worker.
- Replaced line-based NuSMV process output reads with fixed-size byte draining, so one
  unterminated output line cannot allocate memory outside the configured retention bound.
- Removed optimistic chat turns when the server rejects a request before SSE acceptance,
  restored ordinary drafts, preserved pending protected confirmations, and added a
  frontend/backend session-id and model-scalar validation boundary.
- Bounded verification/simulation task exclusion lists and interactive fix request ids,
  and aligned the frontend, backend, reverse-proxy example, tests, and API documentation
  with the resulting contracts.

### 2026-07-21

#### Added
- Added server-authoritative protected-action discovery and structured assistant
  confirmation buttons. Destructive, bundled-default reset, and full-scene replacement
  authority can no longer be inferred from model-classified natural language.
- Added bounded HTTP/model collections, browser import sizes, NuSMV output retention and
  diagnostic-directory cleanup, authentication attempt limits, stronger registration
  password bounds, and Redis-coordinated per-user admission for synchronous formal work
  and assistant streams.

#### Changed
- Changed standalone rule and specification recommendation requests from query-bearing
  `GET` calls to typed JSON `POST` bodies, so user requirements are not exposed in URLs.
- Updated the production reverse-proxy example to terminate TLS, redirect HTTP, enable
  HSTS, forward HTTPS metadata, and enforce the same 4 MiB request limit as the backend.

#### Fixed
- Updated the real-backend recommendation journey for JSON `POST` requests; authentication
  throttling now uses low per-account/phone limits plus higher source ceilings, returns
  structured retry data through CORS, and no longer locks ordinary users behind one NAT
  after a handful of unrelated attempts.
- Completed frontend capacity enforcement for drag/drop, recommendation, nested-condition,
  runtime-override, and scene-import paths. Early layout interactions are now persisted after
  hydration and the one-shot protection flags no longer break later responsive restoration.
- Added structured formal/chat admission reason codes and localized conflict feedback, kept
  protected-action controls recoverable after a transient confirmation-state failure, and
  held NuSMV artifact exclusion atomically from cleanup inspection through deletion.
- Prevented delayed Board layout hydration from overwriting zoom or pan changes made while
  the initial layout request was still in flight. Device-template manifests now use a
  `LONGTEXT` column so valid 256 KiB icon payloads fit the persistence schema, and durable
  assistant state is removed inside the account-deletion transaction.
- Moved JSON body buffering behind authentication, applied public authentication throttling
  after bounded DTO validation, and enforced Board-wide device/rule/spec/environment totals in the same transaction as
  targeted creation, and kept legacy over-limit data deletable instead of truncating it.
- Renewed active Redis per-user admission leases with owner-token checks and guaranteed
  chat slot release even when database execution cleanup fails.
- Protected active NuSMV diagnostic directories with cross-process file locks, and moved
  assistant confirmation controls into the normal flex layout so multiple confirmations
  and expanded input cannot cover conversation content.
- Updated the frontend lockfile to patched dependency versions; `npm audit` now reports no
  known vulnerabilities.
- Classified an empty current Board template set as confirmed automatic-fix model drift
  when the verification snapshot contains templates. Apply now rejects with `400` and asks
  for a new verification instead of returning a retryable preflight `503`. The global API
  error map and NuSMV candidate-generation contract are now synchronized with the code.

### 2026-07-20

#### Added
- Added a real-NuSMV three-strategy acceptance matrix and live browser coverage for
  parameter threshold repair, occupancy guard addition, and permanent rule removal. Each
  flow now asserts a complete counterexample model, the exact user-visible edit, signed
  apply, persistence reload, and a complete post-repair verification.
- Added a combined-scene regression where one counterexample yields all three verified
  strategies, plus explicit `UNKNOWN_SPEC` gate coverage and sequential frontend result
  merging across parameter, condition, and removal searches.
- Added real-NuSMV interaction regressions for inverse duplicate boundaries, redundant
  same-command rules requiring coordinated edits or pair removal, environment-only
  counterexamples with no rule root cause, and an unrepairable numeric upper-bound case
  where condition and removal strategies must still complete. Full-stack browser coverage
  now independently applies, reloads, and re-verifies multi-item coordinated suggestions
  for all three strategies through the live REST API and database.
  Signed-token round-trip regressions additionally prove that every hidden locator in a
  multi-item parameter, condition, or removal proposal is restored and applied.

#### Fixed
- Unified asynchronous task creation, progress, lease, and terminal timestamps on the
  microsecond database clock. Progress writes now require the live owning lease, while
  completion and evidence persistence lock the task row before sampling terminal time;
  fast tasks and workers delayed behind a row lock can no longer produce inverted
  timestamps or commit after their lease expires.
- Extended chat execution fencing to verification/simulation task creation, cancellation,
  synchronous verification-history persistence, and trace deletion. Account deletion now
  clears durable AI session state in independent post-commit transactions and isolates each
  cleanup stage so one failure cannot skip the remaining cleanup.
- Added same-user Board invalidation over `BroadcastChannel` for successful semantic
  mutations and assistant refresh commands. Tabs coalesce refreshes through the existing
  mutation queue, retain invalidations received while hidden, and still reconcile on focus
  for browser compatibility.
- Added route and assistant subtree error boundaries with localized retry and page-reload
  recovery, preventing one render failure from replacing the entire application with a
  blank screen.
- Fixed automatic-fix condition search so disabled free-value candidates are excluded by
  semantic assignment, same-shape policy literals share one candidate, and command outcome
  values are pruned without discarding the remaining valid value domain. One-condition
  additions/removals are now tried before unrestricted joint edits.
- Added suggestion-independent numeric parameter targets and accurate preferred-range match
  reporting. The Board can refine ranges after a search finds no suggestion, and unrelated
  same-named device attributes no longer bias the bounded near-value probe.
- Prevented automatic-fix search from certifying parameter or condition edits that would be
  rejected by Board persistence as an identical rule. Integer policy-boundary probes now
  include adjacent values and continue past duplicate boundaries without spending a NuSMV
  attempt, avoiding an unnecessary joint-solver timeout and returning an applicable edit.
- Added bounded coordinated parameter and condition probes for redundant rules issuing the
  same command, avoiding expensive unrestricted Cartesian solving when several thresholds or
  guards must move together. Permanent removal now expands through the violated specification
  so a dormant lower-priority rule cannot take over after the localized rule is deleted.
- Preserved exact device as well as automation-link attack points during every fix candidate
  generation, preventing rule removal from certifying a model after silently disabling a
  selected actuator attack variable.
- Serialized Board mount, retry, and cross-tab semantic snapshot reads through one refresh
  coordinator, so a delayed initial response cannot suppress a queued invalidation refresh.
  Returning from a hidden tab now consumes its deferred invalidation with one snapshot read
  instead of scheduling a redundant second refresh.
- Distinguished NuSMV execution or result-parsing failures and truncated candidate searches
  from a completed automatic-fix search with no verified suggestion. Strategy attempts now
  expose their main-search count and limit, and the Board explains both incomplete outcomes.
- Aligned coordinated parameter/condition grouping with the Board's full command identity,
  including content device and content value, so unrelated payload commands are not repaired
  together. Parameter closest-value refinement now handles the full signed 32-bit domain
  without distance or bound overflow.
- Corrected boundary-effect messaging for parameter repairs: only impossible strict bounds
  are identified as making a rule unreachable, while reachable non-strict endpoints are not
  described as disabled. The fix dialog now shows that consequence directly and renders every
  removal item even when multiple distinct rules have the same display name.
- Cancelled in-flight automatic-fix requests when the dialog is hidden programmatically or
  unmounted, not only when its own close button is used. A failed best-effort server cancellation
  is now contained and logged after the local request is aborted instead of becoming an unhandled
  promise rejection.
- Aligned the frontend automatic-fix types and strict response validator with the backend's
  required condition display snapshots and always-present collection fields.

### 2026-07-19

#### Changed
- Automatic-fix parameter search now spends a bounded first phase on one-threshold,
  near-original repairs before joint tuple solving, and the Board can lock a suggested
  parameter at its original value for the next search. Multi-threshold scenes no longer
  depend entirely on arbitrary Cartesian-product witness order.
- Condition adjustment now models Salus's candidate-clause value `Y` as a NuSMV
  `FROZENVAR` for enum and numeric mode/variable domains. Added conditions carry the
  solver-selected value instead of blindly copying the violated policy's value.
- Automatic-fix parameter and condition discovery now reproduces the complete first
  counterexample state, including concrete attack choices, while final forward verification
  still checks the unconstrained complete model. Condition-search scope also includes shared
  environment domains and positive API-event candidates.
- Automatic-fix strategy attempts now distinguish candidate-model generation failure from a
  completed search with no verified suggestion. First-state replay derives required fields from
  the resolved model and fails closed on every missing device, value, property, environment, or
  attack choice.
- Fix apply UI and responses now distinguish fresh rechecking from reuse of signed verification
  evidence. Confirmed or unavailable template comparison disables apply, and retryable `503`
  preflight failures carry a stable reason code; unclassified infrastructure `503` responses
  remain outcome-uncertain and trigger board reconciliation.
- Chat session-list responses now expose authoritative execution activity. On reload or in
  another tab, the assistant automatically opens a running session, shows a live activity
  marker and reconnected status, retains a working Stop control, and reloads persisted
  history plus Board/run state when execution finishes.
- The assistant now refreshes cross-tab activity whenever its panel opens or the browser
  document returns to the foreground. A session already reported active is locked and
  monitored before history loading, so a history error cannot expose mutation controls.

#### Fixed
- Signed fix tokens now carry every hidden operation locator required by apply, including
  nonzero parameter/condition indices and condition-add device references. Public JSON
  round-trips can no longer collapse an applicable suggestion onto rule 0/condition 0.
- Parameterized fix generation now fails closed when a rule/specification is omitted or the
  negated specification cannot be translated, instead of silently searching a reduced model or
  substituting a trivially true property.
- Replaced the fixed two-hour chat execution lease with a configurable 30-second renewable
  lease, a 10-second execution-id-guarded heartbeat, and scheduled expired-row cleanup.
  Backend crashes no longer leave sessions busy for hours, while healthy long-running tool
  workflows renew their lease instead of aborting when the original deadline passes.
- Bound chat workers and controller cleanup to the exact acquired execution id and moved
  every lease comparison to the database clock. A delayed queued worker or older request
  cleanup can no longer start without ownership or clear a replacement execution lease.
- Reloaded terminal assistant history even when the separate Board/run reconciliation
  fails, while retaining the visible locked retry state for the failed reconciliation.
- Replaced verification/simulation startup-wide active-task failure with renewable
  per-instance database leases covering queued and running work. Rolling deployments now
  preserve healthy work on other instances, expired work is recovered as failed, and a
  queued task that loses ownership cannot later start. Counterexample-search start and
  renewal now also reject an already-expired lease instead of reviving abandoned work.
- Fenced verification, simulation, and counterexample-search success/failure commits by the
  current worker id and unexpired database-clock lease. An expired worker can no longer publish
  a terminal result before recovery maintenance runs; user cancellation remains authoritative.
- Fenced AI-originated Board transactions, chat messages, confirmation state, scene drafts,
  and task continuations by the exact live chat execution id. A replaced or expired worker can
  no longer mutate shared state or append terminal history after ownership changes.
- The Board now refreshes its full semantic snapshot through the mutation queue whenever its
  tab becomes visible or its window regains focus, reconciling changes made in another tab.

### 2026-07-18

#### Changed
- Separated persistent trust labels from per-run attack selection. Device templates now
  remain the default trust/privacy authority, ordinary device creation omits instance
  label overrides, and users can override or restore template defaults only from
  advanced device settings.
- Replaced the verification/simulation attack switch with structured run scenarios.
  Verification can either fix explicit device/rule-link points or exhaust every
  combination up to a budget; simulation requires explicit points and no longer chooses
  compromised points randomly. Results and histories persist and display the exact
  selection policy and selected points.
- Updated `verify_model*` and `simulate_model*` AI tools to use `attackMode`,
  `attackPoints`, and verification-only `attackBudget`, matching the Board workflow.
- Expanded the shared AI recommendation capability view with explicit per-mode values,
  API triggers, and behavior-derived descriptions for otherwise blank manifests,
  states, variables, transitions, APIs, and content. Each description now identifies
  whether it was declared by the template or derived from modeled facts.
- Made chat execution records durable across reloads. Assistant rows persist the exact
  emitted activity trace and elapsed time, including task resumption and execution-guard
  stops; missing execution evidence remains unavailable. Visible summaries are
  operation-aware and omit raw internal identifiers and provider exception text.
- Added ReAct-style user-visible reasoning summaries before tool actions. The summaries
  explain the current goal, observed facts, next action, and remaining work, are sanitized
  before streaming/persistence, retain enough context to explain multi-step decisions, and
  do not expose private hidden chain-of-thought.
- Persisted expiring AI continuation, scene-draft, and protected-action confirmation
  state in the shared database with scheduled cleanup and atomic single-use consumption.
  Normal backend restarts and load-balanced follow-up turns now preserve live pending work.
- Added explicit `COMPLETED`, `AWAITING_CONFIRMATION`, `PARTIAL`, `STOPPED`,
  `DISCONNECTED`, and `FAILED` chat terminal outcomes. Results now reflect failed,
  uncertain, guarded, and confirmation-pending tool work instead of treating every
  normally closed stream as completed. Explicit user stops are distinguished from transport
  failures, and history reconciliation keeps the local response when no matching terminal
  assistant record has reached persistence.
- Serialized chat execution across backend instances with an expiring database lease and
  distributed stop flags. Stopping now preserves the authoritative result of a tool that
  already returned, and per-turn ids prevent an older terminal reply from replacing the
  current local conversation.

#### Added
- Added the `reset_default_templates` AI tool. It previews the exact bundled-template and
  Environment Pool impact, requires a later action-specific confirmation, then uses the
  same atomic refresh authority as the Board UI while preserving custom templates.

#### Fixed
- Bounded isolated in-memory AI-state fallbacks, replaced unbounded per-session chat locks
  with fixed lock stripes, and made empty/invalid scenario recommendations report whether
  the previous valid draft remains active.
- Added compatible-provider support for explicitly safe reasoning-summary fields while
  continuing to ignore raw `reasoning_content` and other hidden-reasoning fields.
- Kept left-panel single-device creation on template-owned trust/privacy defaults unless
  the user explicitly selects an advanced override, and added a restore-to-template option
  for each state and local-variable label.
- Preserved an explicitly selected state trust/privacy override when the user changes the
  initial state; switching the state no longer silently discards an advanced setting, and
  the user can deliberately choose the template-default option when desired.
- Aligned the canvas exact-attack-point limit with the backend contract: selections above
  50 points are rejected before a run request is sent, with localized guidance.
- Rejected automatic-fix candidates that remove or duplicate an explicitly selected
  automation-link attack point, preventing forward verification from silently changing
  the counterexample's fixed attack scenario.
- Kept the in-flight assistant status compact even when it already contains execution
  activity; completed execution records remain full-width for review.
- Synchronized the climate-conflict example's Air Conditioner template snapshot with the
  corrected bundled public privacy labels, so strict full-scene import no longer rejects it.
- Added deterministic conjunction checks for AI-authored rules and specifications.
  Direct AI mutations, standalone recommendations, and full-scene recommendations now
  reject condition groups with no common legal state/value and rules whose target
  conditions cannot satisfy an action API's declared `StartState`. Ordinary user Board
  editing remains governed by the existing structural contract.
- Filtered AI recommendation conditions and command prestates that are provably unreachable
  from current runtime plus declared APIs, transitions, dynamics, and natural change, while
  retaining uncertain/open candidates through conservative over-approximation.
- Made deletion, default-template reset, and scene-replacement confirmations authorize only
  their matching protected action, with semantic classification performed by the configured
  model instead of fixed natural-language phrase matching.
- Made the AI default-template reset preview enumerate each Environment Pool change with
  its previous and current value, trust, and privacy instead of exposing only a count.
- Interpreted `_` and empty segments consistently as per-mode wildcards in authored state
  conditions across NuSMV generation, fault localization, and fix validation.
- Kept relation-free API event input valid across scenario recommendation and confirmed
  atomic Board replacement by canonicalizing omitted relation/value to explicit `= TRUE`
  before the strict persistence contract, matching standalone specification authoring.
- Completed scenario recommendation readiness propagation through the REST DTO and
  frontend parser. The controller now rejects a payload whose `verificationReady` or
  ordered `readinessIssues` disagree with the returned canonical scene.
- Corrected remaining built-in privacy labels for social posting, phone photo/upload
  activity, and door/window/garage contact or open-state facts, keeping routine idle and
  ordinary appliance states public.

### 2026-07-17

#### Changed
- Enabled the chat assistant to apply its latest validated full-scene recommendation
  through the same confirmed atomic Board replacement authority as UI scene import,
  rather than decomposing replacement into per-device deletions and additions.
- Replaced deterministic chat intent routing and keyword-selected tool subsets with
  model-driven planning over the complete AI tool catalog. The assistant can now answer
  current-scene count questions from `board_overview` and compose targeted device,
  environment, rule, and specification tools to complete an existing scene without
  turning it into a full-replacement draft.
- Made chat planning objective-oriented across confirmation boundaries. A destructive
  preview now pauses only its protected step; after explicit confirmation the assistant
  resumes the original multi-step task and can continue composing deletion, creation,
  rule, specification, simulation, and verification tools until another real boundary.
- Replaced the assistant's normal five-round planning cutoff with progress-aware
  continuation, exact repeated-call/result stagnation detection, and a configurable
  high emergency runaway guard. Long requests now retain full tool capability and still
  receive a model-written final explanation if a guard stops duplicate execution.
- Extended the default chat SSE lifetime to 60 minutes and added structured tool-result
  and execution-guard progress events with cumulative success, failure, and unconfirmed
  counts.
- Reworked the assistant trace into a full-width activity record with localized action
  names, visible confirmation points, per-step outcomes, cumulative result counts, and
  responsive desktop/mobile layouts instead of a narrow abstract text column.
- Defaulted Board verification and simulation to background execution while retaining
  the synchronous options, so users can leave the submit panel, observe progress, and
  cancel long work without reducing formal-analysis capability.

#### Added
- Added the `apply_scenario` AI tool and a server-side per-chat draft lifecycle. The
  assistant now previews current/replacement counts, waits for explicit confirmation,
  and then commits devices, shared environment values, rules, specifications, and
  required template snapshots in one transaction.
- Added an accumulating, bilingual execution trace inside the active assistant message.
  It shows context loading, planning rounds, tool starts and outcomes, retry decisions,
  and response generation, then remains available as a collapsible record after the
  response completes without presenting private model chain-of-thought.
- Added a 15-minute per-user, per-session task-continuation store and `TASK_RESUMED` SSE
  progress event carrying a bounded summary of the original user-authored objective.
- Added server-observed phase reporting for standalone AI recommendations, automatic-fix
  searches, and persisted verification/simulation/exploration tasks. The frontend now
  displays these real phases instead of guessing from elapsed time or showing an
  indefinite generic spinner.

#### Fixed
- Unified recommendation capability context across scenario, rule, specification, and
  related-device tools. Models now receive falsifiability, domains, natural change rates,
  working-state dynamics, autonomous transitions, API content/state behavior, content
  descriptions, and the current shared Environment Pool.
- Corrected AI-facing specification semantics to use the formal `AG`/`AF`/`AX`/`GF`
  definitions, including `AF` (not `EF`) for Eventually. Scenario recommendation results
  now expose `verificationReady` and structured `readinessIssues`; empty-spec drafts remain
  user-applicable but are clearly marked as not ready for verification.
- Made specification persistence canonicalize `propertyScope` and trust/privacy literals,
  including set-valued conditions, and stopped failed/empty scenario recommendations from
  deleting the previous valid draft.
- Added optional template content descriptions and aligned the built-in privacy defaults:
  routine appliance/environment facts are public, while location, activity, access,
  communication, financial, health, and personal-content facts remain private.
- Made pending AI confirmations follow the user's latest instruction instead of requiring
  an immediately adjacent one-word reply. Ordinary questions and task changes now preserve
  the preview, action-specific confirmations may include follow-up work, and a generic
  confirmation is rejected as ambiguous when several action kinds are pending.
- Replaced fixed confirmation phrase matching with model-based semantic interpretation
  scoped to the server-known pending action kinds; invalid or unavailable classification
  fails closed without authorizing a protected mutation.
- Preserved bounded user-authored task updates and sanitized pending tool output across a
  confirmation pause, allowing the assistant to resume the revised objective without
  exposing model reasoning or repeating a completed preview.
- Kept destructive confirmation executable when detailed tool results exceed the chat
  history character window by injecting the pending tool, target, and opaque token from
  server-side confirmation state. Scene application likewise keeps its draft and Board
  impact token outside model history, preventing repeated no-write preview loops.
- Corrected `add_device` planning guidance to use the authoritative `list_templates`
  catalog instead of claiming that `board_overview` lists available device types. Scene
  completion now obtains an exact template name before targeted creation rather than
  guessing or silently degrading the requested composition.
- Kept ordinary continuation requests distinct from protected-action authorization through
  the model's pending-action semantic classification rather than keyword routing.
- Repaired blank or repeated tool-call correlation ids returned by OpenAI-compatible
  providers before persistence and execution, keeping assistant calls and tool results
  protocol-complete instead of failing after a tool may already have run.
- Kept multi-call AI conversations provider-valid when an earlier call requires user
  confirmation or returns an unavailable result. Remaining same-round calls are now
  explicitly recorded as skipped without execution, so the final explanation no longer
  fails with a missing tool-output protocol error. History loading also omits older
  incomplete tool-call blocks so affected sessions recover on their next request.
- Made terminal background tasks display their completed, failed, or cancelled status
  instead of a stale last active phase, and prevented a closing automatic-fix request
  from stopping progress updates for a newly opened request.
- Retained completed interactive-operation status briefly so final progress polling no
  longer produces a spurious 404.

### 2026-07-16

#### Added
- Added a canonical current-Board exploration fingerprint endpoint and stored that
  fingerprint with completed exploration snapshots so history detects same-count model
  edits before replay or formal-verification handoff.
- Added atomic per-user active and stored task quotas for async verification and
  simulation, with configurable limits and structured HTTP 429 reason data.
- Added atomic `GET /api/board/snapshot` hydration so the first Board screen receives
  devices, templates, environment, rules, and specifications as one authoritative model
  snapshot while layout and task history load in parallel.
- Added request-scoped cancellation for standalone AI recommendations and automatic-fix
  searches, backed by bounded executors, server-side task interruption, and explicit progress
  displays with elapsed time and observable processing phases.
- Added non-persisted chat SSE progress frames for context loading, tool planning, tool
  execution, and visible-response generation.
- Added a contextual empty-canvas start state with direct device, AI-scene, and scene-import
  actions for newly registered users.

#### Changed
- Made narrow-screen Board layout transient and task-focused: side panels collapse,
  existing devices fit into view, scene commands move into a compact menu, touch targets
  remain at least 44px, and the saved wide-screen workspace is restored on expansion.
- Registration now returns `AuthResponseDto` with a JWT and the frontend enters the Board
  directly. Bundled default device definitions are parsed and schema-validated once per backend
  process before per-user transactional insertion.
- Signed each verified automatic-fix suggestion and changed apply to persist the exact proposal
  the user reviewed after atomic model-drift checks. Apply no longer repeats the full strategy
  search or silently substitutes a newly recomputed suggestion.
- Added an optional recommendation-specific LLM model, compacted scenario template prompts to
  capability projections, and logged prompt size, output size, and model latency.
- Revised authentication and recommendation wait states using Nielsen-style status visibility:
  action-specific loading text, persistent recoverable errors, explicit panel exit, and progress
  copy that does not guess private model phases from elapsed time.

#### Fixed
- Made rule creation, inspector device cards, delete actions, and copy controls keyboard-operable;
  copy failures now remain visible and recoverable. Rename and simulation dialogs have named
  controls, focus trapping, and Escape handling; reduced-motion mode now suppresses landing
  animation and video playback.
- Kept chat sessions locked when backend activity could not be confirmed, preventing a second
  interaction from starting while an earlier tool might still be running.
- Made AI rule/specification deletion compare the confirmed entity snapshot inside the same
  user-level transaction as deletion, closing the confirmation-to-delete race.
- Stopped blocked template-deletion conflicts from incorrectly requesting confirmation when no
  fresh confirmation token can be issued.
- Rejected expired or malformed JWTs before routing to the Board, avoiding a burst of initial
  authenticated requests that can only return `401`.
- Fixed a recommendation-state initialization order that could leave the Board completely blank
  immediately after registration, and restored parent read-only styling on the teleported Control
  Center component.
- Added accessible names to icon-only recommendation, simulation, and verification-result close
  controls and focused the first invalid authentication field after validation.
- Mapped missing required query parameters to structured `400 Bad Request` responses instead of
  reporting them as internal server failures, and aligned full-stack repair tests with request ids
  and exact signed-suggestion application.
- Removed a duplicate first-round chat planning progress event observed in the live SSE path.
- Restricted public security access to registration and login only, removed Spring Boot's
  generated default user from the JWT-only service, disabled Open Session in View, and updated
  Hibernate to detect its supported MySQL dialect from the live JDBC connection.
- Kept cancelled recommendation and automatic-fix request slots reserved until the underlying
  provider or checker call actually exits, and stopped a successful fuzz-run deletion from being
  misreported as failed when only the follow-up history refresh fails.
- Preserved the active recommendation request id when a stop call cannot reach the server, so the
  interface remains locked to the real operation and the user can retry stopping it.
- Disabled rule creation and similarity checks until an IF condition is explicitly added and the
  THEN action and optional content payload are complete, with a persistent inline reason.

### 2026-07-15

#### Added
- Added `POST /api/fuzz/workload/preview`, which calculates the same frozen-model
  complexity and 12,500,000-unit ceiling used at submission. The search panel now waits
  for this authoritative check, refreshes it when the Board or budget changes, and shows
  a retryable status instead of estimating from visible item counts.
- Added a server-authoritative semantic fingerprint to paper-domain previews and
  submissions. Paper runs now fail before task creation when devices, environment,
  rules, specifications, or referenced manifests changed after preview; canvas-only
  layout changes do not invalidate it.
- Added paper-mode device-local initial-value domains to preflight and frozen eligible
  specification labels to result history, so both upcoming randomization and historical
  no-finding targets remain understandable without relying on the current Board.
- Added inclusive numeric bounds to paper-domain preflight so large device-local and
  environment integer domains remain complete without expanding thousands of values.

#### Changed
- Bound every AI-assisted destructive deletion confirmation to one authenticated chat
  session, tool, target, and canonical preview digest through a 15-minute opaque token.
  Tokens are single-use, only one deletion can be pending per session, and device/template,
  rule/specification, and saved verification/simulation trace deletion now reject target
  drift, wrong-session use, and replay without writing.
- Added a full-stack CI suite with real MySQL, Redis, NuSMV, backend, and Chromium
  services. It now runs every Chromium E2E workflow, including account deletion, chat,
  portable-scene import, authority boundaries, counterexample search/replay, and formal
  verification, rather than only the counterexample journey.
- Deferred conditionally opened Board dialogs and overlays, including account actions,
  device/rule editors, simulation/fix views, counterexample search, results, history, and
  playback, until first use instead of including them in the initial Board route chunk.
- Replaced research-paper and internal algorithm terminology in counterexample-search
  screens with user-facing choices: Board initial state or random initial state with
  reproducible inputs. Capability disclosures now explain behavior and safety boundaries
  without exposing FSM/BFS/predecessor implementation names or the underlying verifier
  brand in the ordinary exploration workflow.
- Aligned paper-compatible mutation with the paper's position-first selection and the
  reference artifact's mutable initial vector. The 95% local branch can now modify one
  device state, device-local variable, or environment initial value without resampling
  unrelated initial targets; sparse overrides remain reproducible, while only the 5%
  fresh-random branch replaces the nonce. Mutation counts now use the artifact's rounded
  1%-10% formula with the existing 128-operation safety cap.
- Made the three-level, rule-produced state/mode/API scope of `GetPrevConditions`
  explicit as a stable limitation code instead of implying a general variable-producer
  graph.
- Exposed multi-specification per-target guidance as a localized paper-mode product
  extension instead of leaving the single-monitor difference only in architecture docs.

#### Fixed
- Made AI-tool refresh commands completion-aware across `ChatView`, `App`, and the
  current Board. Failed targeted refreshes now fall back to full Board/run-history
  reconciliation; a second failure presents a bilingual retry state and keeps assistant,
  scene-replacement, and trace-playback interactions locked instead of exposing stale UI.
- Bounded failed chat-activity checks with a dedicated 2.5-second timeout, settled active
  assistant work before sign-out (with explicit confirmation for unknown outcomes), and
  aligned SSE authentication handling with the REST client: `401` returns to login while
  `403` no longer logs out an authorized session.
- Stopped trace playback from rendering an empty automation card on every state. The
  summary now distinguishes observable device/environment changes from user automations,
  and the automation section appears only when the backend reports a rule that actually
  ran in that step.
- Preserved complete AI tool JSON Schemas when adapting vendor-neutral definitions to
  the OpenAI SDK. Root and nested `additionalProperties`, required fields, array-item
  schemas, and nested property constraints are no longer dropped before model calls.
- Prevented account deletion from leaving or recreating AI-chat rows: counterexample bulk
  cleanup now flushes earlier derived deletes before clearing JPA state, every chat write
  locks the active user and revalidates session ownership, and committed deletion stops local
  queued or in-flight SSE chat work. Idempotent startup integrity repair removes legacy orphan
  rows and installs cascade ownership constraints, so writes committed first are deleted with
  the account and writes arriving after deletion are rejected by the database.
- Kept keyboard focus inside the active workflow when opening a saved counterexample
  result from history, exposed selected history layers and filters to assistive technology,
  and removed per-user counterexample notification state after account deletion without
  allowing browser-storage failures to override a successful server deletion.
- Made counterexample response handling fail closed when finding evidence belongs to a
  different run or contradicts the frozen run budget, eligible targets, effective seed,
  trace length, uniqueness, model counts, or exact safe-integer workload product.
- Rejected impossible counterexample execution statistics across engine output,
  persistence/history mapping, and frontend responses, and enforced causal replay-event
  ordering by step and provenance before evidence can be stored or displayed.
- Restored portable-scene duplicate-name rejection for device-local variables, privacy
  overrides, and shared environment variables before any replacement preview is opened.
- Matched the HAFuzz reference aggregation for mixed direct conjunctions: a direct
  condition without a rule predecessor now contributes zero at the first predecessor
  level, while absent branches deeper in the rule chain remain omitted.
- Made paper-compatible environment Event interpretation domain-aware, so discrete
  direct values beginning with `rate:` are no longer misread as numeric deltas.
- Rejected engine and persisted finding prefixes whose state count exceeds the owning
  run's captured `pathLength`, including lightweight history projections.
- Made accepted background-task cancellation conservative across process boundaries:
  only work definitively removed from the local queue reports that no execution remains,
  while remote, racing, or already-running execution reports that it may still be stopping.
- Strengthened the counterexample-search workload guard with the engine's key operational
  cross-products, including environment/device traversal, device transition/API lookup,
  same-target rule arbitration, and specification predecessor search. High-interaction
  Boards are now rejected consistently by preflight and submission before they can monopolize
  the bounded executor.
- Rotated paper-compatible multi-target guidance parents across generations when the
  unresolved target count exceeds the population size, so later targets are not permanently
  excluded from mutation while preserving the per-offspring parent/fresh-random policy.
- Prevented Board teardown and logout races from issuing unauthenticated or user-visible
  late requests: pending layout saves are serialized, coalesced to the latest layout, and
  given a bounded best-effort flush while authenticated,
  recommendation requests are aborted on unmount, and task/history refreshes stop with the
  disposed workspace. Historical result and replay actions now honor the latest user choice,
  unread updates clear only for the history view the user still has open, and task-box
  cancel/dismiss actions are single-flight with consistent failure feedback.
- Preserved unrelated exploration errors when random-input preflight succeeds, made history
  and exploration controls meet touch-target sizing, exposed task progress semantics to
  assistive technology, and formatted result timestamps and workload counts in the selected
  application language.
- Disabled verification and simulation submission while Board collections are still loading,
  failed, or being replaced, and exposed the loading state directly on the primary action so
  an early click cannot be silently rejected before the run request is created.
- Stopped empty or ineligible Boards from being presented as counterexample-service failures:
  workload and random-input preflight now wait for a loaded device model and an eligible target,
  and the frontend accepts the backend's valid zero complexity for a structurally empty Board.
- Separated completed-run detail from list-only availability markers in the frontend contract
  and now reject a summary-only `dataAvailable` field on detail responses instead of hiding
  backend drift with a type assertion.
- Pinned the NuSMV archive checksum directly in both CI installation paths so the artifact and
  its integrity value are not fetched from the same mutable origin.
- Preserved precise, localized client-side scene-import validation messages for unknown
  and internal fields regardless of identifier language, mapped malformed JSON to a
  stable localized error, and continued to reduce backend diagnostics to safe item-level
  coordinates so users can identify and correct rejected portable-scene fields.
- Prevented stale task-inbox and verification, simulation, and counterexample-history
  responses from overwriting newer local or remote state or re-inserting deleted items,
  while keeping counterexample-history page append requests single-flight.
- Scoped specification persistence identity by `(id, user_id)` and added an idempotent
  startup migration for the legacy global primary key, preventing concurrent users who
  import the same scene from overwriting or losing each other's specifications.
- Unmounted cached workspace routes when users navigate away, so Board polling, task
  refresh, and global keyboard/resize listeners stop immediately after logout or route changes.
- Prevented the asynchronous Board startup sequence from installing polling or global
  listeners after users leave during initial loading.
- Kept counterexample-search panels to one scroll region, added an explicit retry for
  unavailable random-state input ranges, kept history headers/actions fixed above one
  scrolling body, restored launcher focus on close, labelled task progress/cancel controls,
  and enlarged primary controls for touch use.
- Added counterexample-search admission guards before large frozen-snapshot
  serialization: cross-instance atomic per-user active and total stored-task quotas
  (HTTP 429 with stable reason payloads) and a process-wide executor-capacity permit.
  Stored evidence is never silently evicted; users at the configured total must delete
  old history or failed/cancelled tasks. A final executor rejection now deletes the
  never-dispatched pending row instead of retaining an unreachable failed task with its
  snapshot.
- Removed every persisted-but-undispatched fuzz task when status rechecks or executor
  dispatch fail, instead of leaving an unknown `PENDING` row until lease expiry.
- Reclaimed local executor queue slots and capacity permits immediately when a queued
  counterexample search is cancelled, including account deletion, while retaining the
  permit until a running worker has actually stopped. Lease reconciliation now performs
  the same cleanup when cancellation was accepted by another backend instance.
- Kept the account-deletion task-stop hook proxyable so Spring transactional service
  proxies actually interrupt or dequeue local verification, simulation, and fuzz work.
- Added renewable per-instance leases for fuzz tasks, so startup and rolling deployments
  recover only expired work instead of failing another healthy instance's tasks. Lease
  decisions now use the database clock rather than each JVM's timezone or clock; worker
  initialization failures fail by task ID and always release local lifecycle state.
- Made account deletion defer token revocation and worker interruption until after the
  deletion transaction commits, preventing rollback from leaving a valid account with
  cancelled work or a revoked session.
- Bounded frozen snapshots and persisted finding evidence, counted every captured
  specification even under explicit target selection, and changed history lists to use
  lightweight finding projections while preserving full run-context validation on detail.
- Applied the frozen-snapshot byte ceiling to workload and paper-domain previews, rebuilt
  queued engine inputs from their persisted snapshots instead of retaining duplicate Board object graphs,
  and persisted async progress only when its visible percentage changes.
- Bounded eligibility labels and diagnostics before persistence, capped combined run metadata,
  and removed frozen finding specifications from list projections; history summaries now use
  an explicit label/count shape while full detail remains snapshot-validated.
- Made exploration eligibility structural and visible before submission: trust/privacy
  predicates are marked formal-only in the panel, while ordinary identifiers containing words
  such as `attack` or `privacy` no longer trigger unsupported semantics. Missing persisted
  exploration modes or required limitation disclosures now fail closed instead of being
  synthesized during history reads.
- Kept ineligible-target explanations on stable localized reason categories and stopped
  rendering backend diagnostic prose in the ordinary result dialog; persisted diagnostics
  remain available to authenticated API clients for development and support tooling.
- Enforced the finding-prefix invariant across engine output, persistence mapping, list
  summaries, and frontend response validation: every replay now ends exactly at its first
  violating state instead of accepting unexplained trailing states.
- Excluded presentation-only labels, descriptions, icons, formula previews, and rule text
  from paper-domain fingerprints while retaining executable Board semantics, including
  device and rule order where first-match transition priority depends on it.
- Restored the paper's binary atomic satisfaction rule, flattened nested
  conjunction/disjunction guards before aggregation, fixed negative API predecessor
  polarity and state-change guards, and prevented integer-range overflow in the
  remaining product-mode distance calculations.
- Made completed fuzz-result recovery single-flight and retry transient network,
  `408`/`425`/`429`, and server failures with bounded exponential backoff instead of
  marking the task failed. Inline result recovery now hands off after three failed reads
  so the main workflow cannot remain locked for hours; tracked background reconciliation
  continues independently. Historical target restoration now preserves the frozen scope,
  and unavailable explicit targets require a visible user decision rather than silently
  broadening the next run.
- Corrected paper trace formation so an environment rate affects its own Event position,
  replaces that step's free natural-rate choice, combines device impact once, and yields
  to explicit formal transition assignments. Discrete paper environments now remain
  stable without an Event or formal effect, and replay preserves causal Event/model-choice
  order.
- Separated the previous transition source from the Event-modified target state, so
  rules and formal guards read `s(i-1)` while writing `s(i)`, and advanced paper monitor
  FSMs online so violating prefixes stop path formation immediately.
- Corrected `GetPrevConditions` priority guidance: only explicitly written modes count
  as action outputs, earlier overlapping rule guards block lower actions, and synthetic
  arbitration guards no longer recurse as if they were model-produced conditions.
- Removed the 1,000-value sampling loss from numeric paper domains and fixed direct-value
  numeric mutation at single-value bounds.
- Canonicalized enum-backed environment rates to `rate:<integer>` before seed formation,
  preventing a valid rate from being applied as an absolute value, and made enum-backed
  mutation uniform across all legal alternatives after excluding the current value.
- Invalidated stale paper previews across semantic and path changes, blocked submission
  without a current preview, validated the complete limitation-code contract, displayed
  local domains and device labels, and preserved an historical implicit-all target set
  when restoring settings.
- Stopped retrying permanently unavailable fuzz tasks: response-contract failures and
  explicit 4xx responses are now untracked and surfaced in result history, while only
  network failures and 5xx responses remain retryable. Stale-fingerprint rejection now
  refreshes inline without leaving a covered or persistent error.

### 2026-07-14

#### Added
- Added a clean-room, HAFuzz-inspired bounded counterexample exploration module as a
  supporting workflow before formal verification. It captures an immutable Board
  snapshot, runs deterministic seed-based finite-path search in a dedicated background
  pool, and persists independent task/run/finding history with replayable candidate paths.
- Added Board controls, global task status, combined history, bilingual result surfaces,
  eligibility/limitation reporting, reproducible seeds, cancellation, lazy finding
  playback, and a formal-verification handoff for exploration results.
- Added `/api/fuzz` task, run, and finding endpoints plus dedicated API and architecture
  documentation. The finite monitor supports specification templates 1, 3, and 4; other
  templates and attack/trust/privacy/content semantics fail closed as ineligible.
- Added a persisted `explorationMode` contract for bounded exploration. `BOARD_SNAPSHOT`
  remains the default product workflow; optional `PAPER_COMPATIBLE` uses HAFuzz-style
  event tuples, random legal initial states, explicit monitor FSM/BFS guidance,
  predecessor-condition weighting, and the paper's 95% mutation / 5% random-seed split.
  The mode is returned by task and run history and remains a templates 1/3/4,
  integer-domain subset rather than a complete paper reproduction.
- Added a read-only paper-mode input-domain preview backed by the executable server
  model. It exposes legal device initial states, environment initial values, Event
  values, and the per-seed initialization policy without creating a task or pretending
  that one concrete random initial state exists before candidate generation.
- Added explicit `historyPersistence` metadata to synchronous verification and
  simulation responses, separating a completed formal/model result from whether its
  run-history write was saved, failed, not requested, or has an unknown outcome.
- Added lightweight counterexample summaries under verification-run history and
  unavailable-row placeholders, so one damaged persisted result no longer prevents the
  user from loading other history.
- Added per-session Smart Assistant activity status and busy conflicts. Stopped browser
  streams now wait for server work to settle before conversation switching, deletion,
  or another assistant mutation.
- Added token-bound device-template deletion previews with itemized device-instance
  blockers for REST, frontend, and AI-tool callers.

#### Changed
- Kept NuSMV verification as the only proof and automatic-fix authority. Exploration
  budget exhaustion is presented neutrally rather than as satisfaction, and heuristic
  findings remain separate from formal counterexample `trace` rows.
- Bounded exploration now applies one server-authoritative workload cap across path
  budgets, frozen device/rule counts, and effective target specifications; task and run
  history reads are paged so persisted evidence cannot create unbounded list queries.
- Made persisted model-bearing JSON fail closed. Missing, blank, malformed, or unknown
  rule/spec/template/trace/task fields are no longer reinterpreted as empty/default
  semantics, and a database template name cannot silently overwrite a different
  `manifest.Name`.
- Moved full verification traces and simulation states behind on-demand history detail
  loading. History lists now carry only the fields needed to explain and select a run.
- Made async task progress reach 100 only with the atomic final-result persistence
  operation, preventing a visible 100% state without a committed result.

#### Fixed
- Hardened bounded counterexample exploration after the paper and interaction review:
  search guidance now preserves a best candidate per unresolved specification instead
  of averaging opposing goals, mutates only choices that affected the generated path,
  periodically restarts even a single-member population, and responds to cancellation
  during path simulation.
- Bound exploration work to the frozen model's structural complexity and validate
  persisted run eligibility and findings against that same frozen input. Malformed,
  unsupported, or cross-snapshot evidence now fails closed instead of appearing
  replayable.
- Made exploration results causally inspectable and keyboard accessible. User-facing
  steps are consistently one-based, replay distinguishes injected inputs from rule and
  state changes, and paper-mode replay identifies random initialization, seed Events,
  device states, environment rates, and ordinary model choices separately. Dialogs trap
  and restore focus, unsupported targets are identified
  before submission, budget fields report validation errors without silent rewriting,
  and completed background results remain visible until reviewed.
- Closed the exploration-to-verification workflow gaps: all stable paper limitation
  codes are localized, multi-target results remain itemized, reproduction settings can
  be restored without auto-running or broadening targets, and the verification handoff
  persistently states that NuSMV checks the complete current Board rather than the
  historical random state, Event sequence, or snapshot. Budget-exhausted completion is
  no longer shown as a green success.
- Made paper-domain preview capture compatible with MySQL's locking rules and suppressed
  late background-completion notices when that same run is already open, preventing a
  database error in preflight and a notification from covering the result title.
- Disabled the exploration entry while an atomic scene replacement or clear is still
  committing, preventing a late import-success message from covering the newly opened
  exploration panel.
- Preserved completed verification conclusions and playable simulation trajectories
  when their separate history save cannot be confirmed, while showing an explicit
  outcome-unknown warning and reconciling history instead of claiming success.
- Returned the current structured template-deletion preview from AI-tool stale/blocked
  conflicts instead of collapsing the reason into a generic business error.
- Bounded Smart Assistant activity-query failures so a network outage cannot leave the
  interface locked for the full stream timeout.

### 2026-07-13

#### Added
- Added three self-contained standard-scene examples generated from bundled default
  templates: fire evacuation, conflicting climate control, and RFID access. Real NuSMV
  and Playwright regressions lock their importability, baseline/attack outcomes,
  animatable simulations, and the verified removals for the two intentionally unsafe
  scenes.
- Added `docs/examples/multi-violation-repair-scene.json`, a self-contained default-template
  scene with two baseline violations sharing one root automation and a verified single-rule
  repair path.

#### Changed
- Mapped the persisted environment-variable value to the non-reserved
  `variable_value` database column and added an H2 repository regression test, so schema
  creation can no longer log a hidden failure while the broader application-context test
  still reports success.
- Renamed the physical authentication table from the reserved identifier `user` to
  `app_user` and added a repository write/read regression test. The REST authentication
  contract and user-facing account model are unchanged.
- Kept raw model-checker execution logs in simulation run details when a run produces no
  states; the primary failure notice now uses a localized user-facing explanation instead
  of exposing the final technical log line.
- Replaced the three peer run-history tabs with a two-layer model: Task Status now
  contains only active, failed, or cancelled background work, while History Results
  contains one entry per completed verification or saved simulation. Verification
  counterexamples are nested under their owning result, with violated-property and
  replayable-counterexample counts shown separately.
- Added completed verification-run DTOs and `/api/verify/runs` endpoints. Synchronous
  verification now persists its complete conclusion and counterexamples atomically;
  deleting a verification result removes its linked counterexamples, and failed or
  cancelled no-result tasks can be dismissed explicitly.
- Increased AI recommendation `userRequirement` inputs from 500 to 2,000 characters
  across REST DTOs, AI tool schemas, Board controls, tests, and documentation. Detailed
  coupled-scene requests no longer need compressed shorthand, while the input remains
  bounded and is never silently truncated.
- Relaxed only the semantically equivalent rule-event edge case in AI full-scene
  validation: `api = TRUE` is retained as an API event source, normalized by removing
  redundant relation/value fields, and disclosed through `adjustedItems`. `FALSE`,
  partial fields, and other relations remain rejected instead of changing rule meaning.
- Applied the same transparent API-event normalization to standalone AI rule
  recommendations. Equivalent `= TRUE` candidates are kept with an itemized adjustment
  shown by the Board; ambiguous, false, or non-equality comparisons are now filtered
  with an explicit reason instead of having their comparison fields silently erased.
- Restored complete automatic-fix strategy regression coverage against the production
  snapshot-aware model-generation entry points, and made missing fix-context environment
  values explicitly default to an empty pool. `SpecificationDto.devices` now also
  recursively rejects null bindings, missing device ids, and null selected-API entries.

#### Fixed
- Added stable model-generation omission reason codes across verification, simulation,
  history, and automatic-fix contracts. Ordinary UI now localizes disabled-rule and
  skipped-specification explanations instead of exposing English generator diagnostics;
  the original diagnostic remains available only for technical logs and advanced detail.
- Failed background tasks now show a localized no-result explanation first. The raw
  executor error remains available only in a collapsed Technical Details disclosure,
  instead of appearing as the task's primary user-facing status.
- Automatic-fix template drift now has a stable `templateSnapshotComparison` contract.
  The dialog derives source-model and template-snapshot limitations from structured
  fields, while English fix diagnostics remain behind a collapsed technical disclosure.
- Rule duplicate and AI similarity checks now return stable reason codes; AI similarity
  also returns the authoritative `requiresReview` decision. Rule creation and
  recommendation application localize these codes instead of inserting deterministic or
  LLM-generated English prose into Chinese confirmation dialogs.
- Historical counterexample titles now format specification templates through i18n.
  Chinese history and playback surfaces no longer fall back to hard-coded English
  `Always`, `Never`, `Response`, `IF`, or `THEN` wording when rebuilding a trace label.
- Trace-playback mutual-exclusion guards now return reason codes rather than English UI
  sentences, so blocked playback uses the existing localized simulation/recommendation
  guidance.
- Default-device-type reset blockers now include stable reason codes. The reset preview
  localizes device/rule/spec/environment incompatibilities and moves the original
  validation sentence into a collapsed technical disclosure.
- Added a shared locale guard for backend free text and applied it to Board mutation
  errors. Scene-import validation now presents localized item coordinates and keeps raw
  field diagnostics behind Technical Details instead of mixing English exceptions into
  Chinese dialogs.
- Applied the same locale guard to AI recommendation summaries, rationales, filtered
  reasons, intended-use notes, and placements. A provider response in the wrong language
  now falls back to localized advisory copy rather than silently mixing languages.
- Localized deterministic Smart Assistant safety notices and fallback explanations from
  the current user message. Chinese destructive-action previews no longer start with an
  English no-write control sentence, while confirmation, partial execution, uncertain
  mutation, planning-limit, missing-reply, and stream-error safeguards remain explicit.
- Stopped exposing chat implementation placeholders and parser errors as display text.
  Untitled sessions now return `title=null` so the client renders a localized label, the
  final AI reply is explicitly instructed to follow the latest user-message language,
  and client-detected SSE failures use stable error kinds mapped through frontend i18n.
- Fixed two Smart Assistant lifecycle regressions. An empty streamed response placeholder
  now contains the "replying" status inside one compact assistant bubble, and reopening
  the assistant no longer leaves conversation history blank until the user creates or
  sends another chat. The history sidebar now exposes loading, empty, retryable-failure,
  and loaded states explicitly while panel close preserves the mounted conversation.
- Prevented automatic condition fixes from using a rule command's resulting device state as that
  same rule's trigger or adding a condition that contradicts the command API's concrete start state.
  Both cases could make an automation unreachable while falsely looking like a useful repair.
  Fixed apply-time mapping from normalized NuSMV device names back to raw canvas node ids, and
  replaced the leaked internal-reference error with a no-write, user-facing message.
- Raised the automatic-fix dialog above the verification-result modal. Opening
  "Fix" from a violation now exposes the strategy controls and apply workflow instead
  of rendering an interactive dialog behind the still-open verification result.
- Made automatic-fix response collections stable JSON arrays. Strategy-specific details
  and unused preferred-range selections now serialize as `[]` when not applicable,
  preventing a valid verified suggestion from being rejected as an incomplete contract.
- Clarified the automatic-fix empty state: a completed condition-adjustment search now tells
  the user that no condition change passed full-model rechecking, instead of implying that
  the strategy was not run or that suggestions failed to load.
- Clarified the boundary between condition adjustment and permanent rule removal. Condition
  adjustment now describes changing trigger timing while retaining the rule and command;
  removal remains an explicit rule-set deletion rather than an empty-condition workaround.
- Replaced the generic run-history load failure with a source-specific partial-load
  message. If verification results or simulation results fail independently, the Board
  now names the unavailable source and keeps any successfully loaded history visible.
- Restored the canvas device context menu for mouse right-click and added a persistent
  Rename action to device details. Renaming is now discoverable without a keyboard-only
  Context Menu shortcut while retaining the same targeted, identity-preserving API.
- Kept canvas rule labels hidden when a rule is merely selected or newly created. The
  readable label now appears only while its connection is hovered or keyboard-focused,
  preventing persistent rule text from covering devices and nearby links.
- Replaced decorative simulation-step arrows with real decrement/increment controls and
  added direct numeric entry alongside the range slider. All three inputs stay aligned
  to the backend-supported integer range of `1..100`.
- Moved long attack-budget, privacy-propagation, and Environment Pool explanations into
  reusable accessible info tooltips across simulation, verification, and inspector
  panels. Active limits, invalid input, required privacy modeling, and incomplete-model
  warnings remain visible rather than being hidden as optional help.
- Reworked simulation playback around the user's review task. State navigation, playback,
  and selected-state deltas now stay in the first visible layer; frozen run scope is
  collapsible; the run-details action lives in the timeline header instead of covering
  the bottom controls; and diagnostic logs, state tables, and raw NuSMV output are
  collapsed behind a compact run summary.
- Corrected simulation result counting to show actual model states, actual parsed
  transitions, and requested steps as separate concepts. A trajectory shorter than the
  requested horizon now remains visibly qualified in both run details and playback.
- Localized playback changes on the canvas: only devices changed by the selected model
  transition receive motion/emphasis, and backend-reported triggered rules retain
  command-flow emphasis on their edges.
  Current Board ids are normalized with the same NuSMV device-name rule as saved trace
  ids, preventing live devices from being mislabeled as historical.
- Moved playback before/after explanations out of compact device nodes into a bounded,
  draggable change panel. Simulation and counterexample timelines now keep state
  navigation and the timeline in the primary layer; verbose state details remain
  collapsed, and the panel position is constrained to the viewport.
- Reworked model playback motion so device icons and state labels cross-fade to the new
  state, every semantic device delta can retrigger a short settle highlight, and delivered
  command flow completes within one playback step. Change-panel content now transitions
  between steps, and reduced-motion preferences suppress non-essential movement.
- Kept the draggable playback-change panel present for initial and no-delta states, added
  environment-value and automation-cause summaries, and explained why rule edges remain
  still. Delivered-rule edge flow now restarts once per selected transition, including
  consecutive transitions driven by the same rule, instead of continuing an unrelated
  infinite animation.
- Moved the long counterexample model-scope explanation behind an accessible info tooltip.
  The playback header keeps only compact attack, privacy, and completeness status labels,
  while the full interpretation remains available on hover, focus, or click.
- Fixed verification, simulation, and automatic-fix modal headers being compressed by long
  scrollable content. Headers now remain fully visible while only the body scrolls;
  localized the default fault-localization and strategy-attempt explanations so Chinese UI
  does not display backend English summaries.

### 2026-07-12

#### Fixed
- Removed duplicate `aconditions`/`aConditions` keys from typed AI scene responses.
  Portable specifications now serialize exactly the canonical standard-scene field, so
  strict JSON clients can parse and import the recommended draft.
- Aligned the AI full-scene prompt with its rule validator: observable API event sources
  now explicitly omit `relation`/`value`, while specification API conditions retain
  `= TRUE`. The previous example instructed the model to emit a shape that the backend
  would then itemize and filter, commonly breaking otherwise valid event chains.
- Restored the documented `isDuplicate` and `isSimilar` JSON field names on typed rule
  check responses. Manual rule creation no longer treats a successful deterministic
  duplicate check as a broken response and unnecessarily asks the user to bypass it.
- Prevented automatic-fix apply from falsely reporting default-template drift after a
  verification snapshot round trip. Drift checks now compare the persisted manifest
  projection and exact template-name set, so an omitted versus empty legacy API
  `Assignments` list is treated as the same model while real template changes still
  block stale repairs.
- Removed literal wrapper quotes from automatic-removal rule descriptions, so the fix
  dialog names the affected automation exactly as the user authored it.
- Made the long full-scene import/clear confirmation usable on short viewports. The
  Element Plus message-box style is now loaded explicitly, its warning icon is bounded,
  and the consequence text scrolls while the destructive action buttons remain
  reachable.
- Kept `TraceDeviceDto.variables` as an explicit array for state-only devices. Saved
  simulation responses no longer omit the field and get rejected by the frontend's
  completeness guard before an otherwise valid model trajectory can be animated; old
  persisted traces without the field also deserialize to an empty array.
- Fixed full-scene replacement for ordinary API-event rule triggers, whose comparison
  relation is intentionally absent. Generated-namespace validation now classifies those
  triggers as non-parameterizable instead of throwing an internal error before the
  atomic scene write.
- Added a canonical acceptance-demo scene and real-NuSMV regression covering standard
  scene JSON, a four-device event chain, complete mixed verification results, animatable
  simulation/counterexample traces, budget-one trust/privacy/automation-link attack
  behavior, single-rule fault localization, forward-verified permanent removal, and
  all-properties-pass post-repair verification. The accompanying runbook defines manual,
  AI-assisted, and JSON construction paths without treating AI generation as atomic or
  already verified; its exact default-template AI scene prompt fits the public
  500-character requirement limit.
- Applied the same user-semantic projection to saved simulation AI tools: list results
  name the operational handle `simulationId`, detail states omit device/rule model ids,
  and every success explains that a simulation is one possible model trajectory. The AI
  tool no longer exposes an `includeRaw` escape hatch for NuSMV output or internal request
  snapshots; REST technical diagnostics remain separate.
- Removed persistence/model identities from ordinary AI counterexample and fix-analysis
  output. Trace tools now expose only the operational `traceId`, user-facing
  specification/device/rule context, completeness evidence, and projected states;
  automatic fix no longer accepts a numeric specification reference as a hidden list
  index or prints an unresolved internal id in its summary.
- Made rule-trigger authoring commit only on an explicit Add-source action (or Enter from
  the value field). Selecting an event API or leaving a value input no longer silently
  inserts a trigger while the visible Add button suggests the row is still a draft.
- Stopped the verification/simulation forms from silently reducing an attack budget or
  turning attack modeling off when Board edits shrink the modeled attack surface. The
  original selection remains visible, receives an explicit invalid-state explanation,
  and must be revised or disabled before a run can start.
- Made Board-backed AI verification and simulation consume one atomic semantic snapshot
  across devices, the Environment Pool, rules, specifications, and exact template
  manifests. Automatic-fix apply now performs every final drift check against the same
  complete snapshot inside the rule-write transaction. Chat verification results also
  use user-facing specification labels and previews instead of exposing `specId`, while
  retaining the actual checked expression as explicitly named technical evidence.
- Made the low-level NuSMV generator enforce the same exact attack-option contract as
  REST and AI callers. It now rejects out-of-range budgets, enabled attack mode with a
  zero budget, and disabled attack mode with a positive budget instead of silently
  clamping or discarding the caller's meaning. Specification-template 7 copy now also
  distinguishes a protected condition's propagated untrusted label from the individual
  trigger sources that produced it, and rule previews describe target APIs as commands
  being executed rather than new trigger events.
- Qualified automatic-fix evidence in the ordinary UI. Suggestions are now labelled as
  having passed recomputation in the current complete formal model; apply success states
  that every submitted specification passed before the write and that unmodelled reality
  is outside that claim. The UI no longer presents a raw English backend message as an
  unconditional "verified solution", and rule-drift errors identify the readable
  automation plus a one-based position instead of exposing `Rule #0`.
- Made every AI tool enforce its declared exact argument object at execution time,
  including recommendation, search/list, task/status, trace, and no-argument tools.
  Unknown fields and wrongly typed scalars can no longer be ignored after a permissive
  caller bypasses the model-facing schema. Duplicate/similarity checks now accept an
  exact rule-candidate shape rather than silently coercing a full persistence DTO.
- Made standalone recommendation REST payloads preserve omission semantics. Optional
  fields are no longer reintroduced as explicit `null`, specification conditions no
  longer expose derived `side` or persistence `id`, and the Board validates kept
  candidates before display/application without inventing relations or coercing values.
  The assistant response contract now also distinguishes candidates from applied or
  verified state and requires complete kept/filtered/truncated disclosure.
- Added a source-wide check that every literal frontend translation call resolves in
  both supported languages, and fixed the rule-similarity clear result so it explains
  that an AI non-match is not proof of conflict freedom or safe behavior instead of
  exposing a missing translation key.
- Removed the browser manifest cache as a device-detail authority. When a device type
  cannot be resolved from the current backend catalog, the detail dialog now fails
  closed, keeps only instance identity visible, and does not present stale states,
  variables, APIs, trust/privacy labels, or related formula previews as current facts.
- Stopped the Board's local duplicate-rule key from inventing `=` when a value-based
  condition has no relation. Missing relation remains distinguishable and is rejected
  by the authoritative rule contract instead of being compared as equality.
- Closed the remaining playback overlay entry points. Run History and the task inbox now
  share the same model-trace lock as simulation, verification, and recommendations, so a
  user must close the current timeline before selecting another run or task surface.
- Made strict REST rejection actionable. Unknown JSON fields and DTO type mismatches now
  return a safe field path in `message` and `data.errors`, without echoing values or Java
  types, instead of collapsing every deserialization failure into an unexplained
  `Malformed request body` response.
- Removed generator-level silent changes to explicit model values. Invalid local or shared
  enum/numeric initial values, unknown environment entries, duplicate entries, and
  undeclared domains now fail model generation; malformed natural-change rates and
  signal APIs without a representable state transition fail as well. Only an omitted
  valid initial value may use the template's intentional default or nondeterministic
  behavior.
- Made AI board-mutation arguments exact instead of best-effort. Tool JSON schemas now
  disallow extra root fields, and device/rule/specification/environment/template/fix
  tools reject unknown, action-irrelevant, or wrongly typed fields before writing.
  `manage_spec` no longer turns a malformed condition collection into an empty side or
  invents equality for a non-API condition with only a value; API signal checks retain
  their documented `= TRUE` authoring default.
- Changed manual and recommendation rule/specification creation feedback to state that
  persistence succeeded but formal verification has not run, matching the existing AI
  tool response contract instead of letting a save toast imply a checked property.
- Made attack toggle/budget combinations exact across REST and AI verification and
  simulation entry points. Non-attack requests now use the DTO default `0` and reject a
  positive budget instead of silently discarding it; enabled runs require `1..50`.
  Unknown AI run options fail before board loading, and async start responses now echo
  the task's effective attack/privacy context alongside its frozen model scope.
- Made standard scene v4 scalar handling lossless and fail-fast. Import no longer turns
  JSON numbers/booleans into text fields, while export no longer filters incomplete
  environment entries or rule sources or invents a missing relation; malformed semantic
  state is rejected instead of being presented as a successful but changed scene.
- Made targeted device-list JSON import equally explicit about input interpretation.
  Runtime/template/name values no longer coerce non-string scalars, competing aliases
  such as `template` plus `type` are rejected instead of silently prioritized, and the
  preview now exposes every error and planned duplicate-name rename in a scrollable list.
- Stopped silently clamping manual batch-device counts. Values outside the displayed
  `1..50` range now keep the create action disabled with an inline error, so the preview
  and persisted count cannot differ from what the user entered.
- Made automatic-fix strategy selection exact across REST, AI tools, DTO validation, and
  the service boundary. Defaults now apply only when `strategies` is omitted; explicit
  empty, malformed, unknown, or duplicate lists are rejected instead of unexpectedly
  restoring the default chain that includes permanent rule removal.
- Made recommendation controls strict across REST and AI tools. Unsupported language or
  category values, non-string requirements, and requirements over 500 characters now
  return validation errors instead of silently switching to English/all categories or
  truncating the user's scenario before it reaches the model.
- Rejected null device-local value/sensitivity override items at the model-service boundary
  instead of allowing lower-level expansion to discard them. Shared environment trust and
  privacy documentation now distinguishes intentional omission/default inheritance from
  explicit blank or invalid labels, which are rejected before model generation.
- Made assistant `add_device` honor explicitly requested instance names exactly. Name
  conflicts are now detected inside the atomic create operation and return a structured
  no-write `409` with the requested and available suggested names; only omitted names may
  be generated with a suffix. The obsolete successful `nameAdjusted` contract was removed,
  and the chat loop stops at the alternative-name prompt instead of accepting its own
  suggestion in a later tool round.
- Closed the cross-tab/external-writer gap in destructive scene replacement. Import and
  clear now preview authoritative server counts and bind confirmation to an opaque
  current-board impact token; the server rechecks it under the database user-row lock
  before any template or scene write, returns an itemized fresh preview on drift, and the
  frontend refreshes without retrying or claiming success. `/board/batch` no longer
  supports the contradictory `null = preserve this collection` behavior: all four scene
  collections and the exact template snapshot set are required complete inputs.
- Aligned AI device creation with manual and JSON-import name semantics. A colliding AI
  suggestion now shows the exact available instance name before writing and requires
  explicit confirmation; a second collision while the mutation is queued aborts instead
  of silently adding another suffix after confirmation.
- Removed a nonexistent priority concept from AI rule/specification candidates. Rule
  recommendations now return `name`, which is the exact name persisted on apply;
  specification recommendations return an advisory `rationale`, while the UI states that
  only the template and structured conditions enter the formal property. Missing names or
  rationales are itemized filters, and recommendation order carries relevance without
  pretending to alter rule execution order or specification checking order.
- Stopped presenting AI recommendation attempts as completed Board changes. Rule,
  device, and specification candidates now have separate processing and committed states,
  remain tied to the response epoch that produced them, and show "Added" only after an
  authoritative response or reconciliation confirms persistence.
- Serialized all Board semantic writes, device-type mutations, automatic-fix refreshes,
  and assistant-triggered collection refreshes before applying authoritative snapshots.
  Verification/simulation now wait for pending writes before capturing their immutable
  requests. Scene replacement locks live editing from a stable confirmation preview
  through reconciliation and cannot start while an assistant tool stream may still be
  mutating the Board; playback likewise blocks new assistant requests.
- Split device edits into complete, intent-owned layout and runtime subresources and
  removed the ambiguous whole-device update contract. Canvas moves/resizes can no longer
  overwrite modeled runtime fields, runtime saves cannot change identity/label/layout,
  dimensions stay inside the backend's integer domain, and each update returns validated
  before/after snapshots plus itemized changed fields. The Board now serializes create,
  layout, runtime, rename, and confirmed-delete snapshots to prevent late responses from
  overwriting newer state.
- Unified portable geometry across saved canvases, standard scene JSON, and AI scene
  drafts. All paths now accept finite coordinates in `-1000000..1000000`, integer widths
  in `80..2000`, and integer heights in `60..2000`; service-layer validation prevents AI
  or batch callers from bypassing the REST contract, and invalid AI candidates are
  reported as itemized filters instead of failing only during application.
- Replaced AI scene REST reuse of full template/device/specification DTOs with exact
  portable nested DTOs. Serialization can no longer add null template ids/flags,
  condition ids/sides/display labels, or stateless-device label fields that make a tool-
  validated scene fail the standard importer. Frontend types now model that portable
  contract directly, exports self-check against their own importer, and missing optional
  AI rule titles no longer discard otherwise valid trigger/action semantics.
- Made the shared file/AI scene confirmation describe the selected scene and its full
  replacement consequence, rather than incorrectly referring to a file when the user
  entered from an AI draft. Shared success and validation-result messages now use the
  same source-neutral scene language.
- Aligned manual, batch, and device-list import name handling with the backend's
  case-insensitive device-instance uniqueness rule. Single creation now blocks and keeps
  the user's typed name instead of committing an unconfirmed suffix; batch/JSON previews
  show the exact case-insensitive rename plan, rename prechecks use the same rule, and
  submission still aborts on drift.
- Clarified the destructive Clear Scene boundary: it atomically removes devices, the
  Environment Pool, rules, and specifications, while preserving device types, run
  history, and AI conversations.
- Moved standard-scene relation and specification-template shape checks before the
  destructive replacement confirmation. Unsupported operators and missing/unexpected
  condition sections are now identified in the JSON instead of asking for confirmation
  and only then relying on backend rejection.
- Added one-based user coordinates to local and single-item scene validation feedback
  while retaining the exact zero-based JSON field path as technical editing detail.
- Made each verification property result self-contained at submission time. `specResults`
  now carry the submitted template semantics, user-facing label, rebuilt formula preview,
  and CTL/LTL kind beside the actual checked expression. Async/history UI no longer joins
  a technical `specId` to the mutable current Board, and generated NuSMV expressions and
  ids moved into expandable technical details instead of the ordinary result row.
- Made Environment Pool editing genuinely field-level. A value, source-label, or
  sensitivity-label edit now preserves every omitted field instead of resetting it to a
  template default. The REST response itemizes supplied, changed, and preserved fields
  with before/after values and the authoritative pool; the Board validates and presents
  that outcome before claiming success. Device-create environment patches use the same
  semantics, while complete scene replacement and explicit internal default reset remain
  separate contracts.
- Made Stop/close/regenerate authoritative for all four AI recommendation flows. Each
  request now owns an epoch and abort controller, so a late canceled response cannot
  clear or overwrite a newer request. Device panels also show every backend-kept
  candidate instead of silently re-slicing results when the next-request count input is
  edited.
- Made AI-assistant interruption and conversation switching request-owned. Aborted
  streams no longer fire the normal-completion callback, late chunks/tool commands and
  stale history responses are ignored, and old callbacks cannot clear a newly started
  stream. Conversation-history loading now has its own status instead of showing a Stop
  control that could not cancel it.
- Reclassified AI device `role`/`location` output as advisory `intendedUse` and
  `suggestedPlacement`. The Board states that this context is not persisted or modeled,
  and both manual and AI device creation now preview currently missing shared
  Environment Pool names that creation will initialize; final server-reported changes
  remain authoritative.
- Persisted specification list order explicitly in the internal
  `specification.list_order` column and ordered all reads by it. Multi-spec scene
  import/export can no longer depend on incidental database row order while claiming a
  stable, byte-identical portable round trip.
- Made specification writes semantic-only across manual, AI, and scene paths. Clients no
  longer submit template labels, formula text, device summaries, or condition display
  fields as authority; board storage rebuilds those caches from current nodes and
  structured conditions. AI list/create and board-overview previews now use current
  device/template context, show shared values as Environment concepts, and cannot leak a
  stale persisted NuSMV expression. Scene replacement also checks the authoritative 200
  response for semantic equivalence before reporting a complete import.
- Closed a portable-scene defaulting gap: v4 import/export now requires every shared
  Environment value to be explicit and non-blank, so `null` cannot silently mean
  "restore the template default" in a supposedly lossless round trip. AI prompts now call
  their output a self-contained full-replacement draft and explicitly avoid claims that
  it is complete, safe, verified, or already applied.
- Made the MEDIC label-propagation boundary machine-readable and visible in results.
  Runs now return `labelPropagationScope=AUTOMATION_RULE_COMMANDS_ONLY`; frontend
  contract checks and trace/verification assumptions explain that template-internal
  transitions and natural dynamics do not relabel their outputs.
- Aligned the remaining built-in external-input defaults with MEDIC origin semantics.
  Inbound email, vehicle/mobile location, step counts, exterior RFID events, and
  door/window contact readings now start as `untrusted`; this avoids treating a sensor
  observation or outside-house event as retained in-house user control.
- Closed the model-trace animation/current-Board identity gap. Playback now uses only
  saved trace state, dims and labels current devices absent from that trace, blocks live
  device-detail editing while playback is open, and defers background playback instead
  of interrupting an active editor. Chinese locale timestamps now use `zh-CN` formatting.
- Distinguished the scene's full attack surface from the 50-point per-run input cap.
  Verification and simulation controls no longer describe a capped slider maximum as the
  number of modeled points, and explicitly disclose the branches a capped run excludes.
- Added an explicit `API.AcceptsContent` capability for privacy-label flows. Manual rules,
  Board/model validation, AI recommendations, and scene recommendations now reject
  attaching content sensitivity to ordinary actions; built-in mail, social-post, photo
  send, and cloud-upload actions declare the capability and the UI only offers content
  selection for those actions.
- Removed remaining internal-position and certainty leakage from user-facing AI paths.
  Rule/specification condition errors now use one-based display positions, chat presets
  no longer fall back to persistence ids or call preview text a raw formula, and
  violation-oriented prompts require simulation/formal verification instead of promising
  a counterexample. Attack-budget help now states that each submitted rule contributes
  one logical delivery point regardless of how many trigger edges the canvas renders.
- Corrected built-in Clock and Calendar control-source defaults to `untrusted`. MEDIC
  treats environment-driven time/date events as outside direct in-house user control;
  leaving them `trusted` could hide unauthorized-control findings for scheduled rules.
- Separated AI tool success, failure, and unavailable-result outcomes. A serialization
  failure now stops the tool loop, is never counted as success, refreshes authoritative
  state only when a mutation may already have committed, and blocks automatic retry until
  the user can inspect that state.
- Unified AI rule identity with board/recommendation contracts: `manage_rule` now accepts
  `deviceId` plus display-only labels, while rule/spec list and mutation results expose
  semantic views instead of raw persistence DTO names. Created rules and specifications
  explicitly return `verificationStatus=NOT_VERIFIED`; specification tool views call
  cached formula text `formulaPreview`.
- Split background-task lifecycle from result meaning in Run History. A completed task is
  now neutral, with a separate verification-outcome or generated-model-completeness badge,
  so a completed violated verification can no longer look like a green safety result.
- Stopped the Board from inferring `modelComplete=true` when a run omitted that required
  field. Only an explicit backend `true` can produce a complete-model result state.
- Made `board_overview` usable as semantic AI context instead of an internal-id summary.
  Rules and specifications now expose typed conditions with separate stable device refs
  and current display labels; generated summaries use labels, content-flow commands stay
  visible, and specification formula text is explicitly named `formulaPreview`.
- Removed the remaining "complete scenario" claim from AI scene tool definitions and
  success/error messages. The backend now calls the output an importable scene draft,
  states that it passed structure/capability checks only, and explicitly says it has not
  been formally verified or applied to the Board.
- Froze every referenced device-template manifest at the verification/simulation model
  boundary and returned a user-facing `modelSnapshot` on results, tasks, and traces.
  Queued runs can no longer validate one template version and execute another. The Board
  now shows the exact submitted item counts and distinguishes same-tab unchanged input,
  changed input, unavailable comparison, and historical results that were not compared
  with the current Board.
- Replaced bare async verification/simulation submit ids with authoritative accepted-task
  DTOs carrying status, progress, model semantics, and the frozen model scope. REST, AI,
  TypeScript, polling code, and documentation now state that acceptance is not completion.
- Made automatic-fix template replay exact and template comparison three-state. Suggestions
  run against the counterexample's saved manifests; confirmed drift is explained, an
  unavailable comparison is warned rather than hidden, and apply blocks the latter with
  retryable `503` instead of falsely claiming templates changed.
- Replaced the bare fault-localization rule array with an explanatory result carrying
  source-model completeness, itemized generation issues, warnings, and a causally
  conservative summary. The automatic-fix UI and AI contract now describe localized
  automations as involved in counterexample transitions rather than proven independent
  root causes. Missing source completeness metadata fails closed, and fix apply rejects
  it before template checks or NuSMV recomputation.
- Corrected AI-assistant interruption semantics. Stopping or losing the SSE response no
  longer implies that an already-started tool transaction was cancelled: the UI explains
  the uncertainty and reconciles all board collections plus run history. Async task and
  trace tools now refresh run history, pending mutation refreshes are still sent when a
  later AI step fails, and max-round/missing-reply fallbacks report usable and failed
  tool-step counts without claiming the whole request completed.
- Renamed the AI scene action to generate an importable, unverified scene draft rather
  than a "complete scene". Browser JSON exports now report that a download was requested,
  not that the browser or file system definitely saved it.
- Model request construction now rejects a nameless shared-environment entry instead of
  silently filtering it out and verifying or simulating a different input than the Board
  displayed.

### 2026-07-11

#### Fixed
- Distinguished automation **Action Event** from **Action** in rule and specification
  authoring. Only a template action explicitly marked `Signal=true` is selectable as an
  IF event; all valid template actions remain selectable as a THEN command. This avoids
  presenting a model event pulse and a device command as the same user concept.
- Removed the obsolete internal preferred-range locator map from the public automatic-fix
  request DTOs. REST and AI callers now have one contract only: select an opaque
  `ParameterAdjustment.targetId` and submit `preferredRangeSelections`; extra locator
  fields are rejected by strict request parsing.
- Made device-driven Environment Pool changes explicit. Device mutation DTOs now return
  itemized added/updated/removed shared values. Device deletion has an authoritative REST
  preview used by the Board and AI, displays environment removals before confirmation,
  and rechecks rule, specification, and environment impact sets in the same locked
  transaction; any drift returns `409` without a partial delete. AI `add_device` now
  returns the authoritative pool and the same itemized transaction changes instead of
  reporting only the created device while shared values changed silently. Chat-driven
  device creation/deletion and environment edits now also refresh the Board Environment
  Pool rather than leaving its displayed model inputs stale.
- Made Board write responses authoritative at the frontend boundary. Device, rule,
  specification, Environment Pool, and complete-scene operations now reject missing
  snapshots, mismatched affected sets, wrong operations, and inconsistent counts instead
  of substituting local drafts or empty arrays and showing success. Unknown device-delete
  and environment-edit outcomes refresh from the server and remain visibly unconfirmed.
- Reconciled rule-order and device-type catalog writes after lost or incomplete
  responses. The UI now compares the refreshed rule order, reloads templates after
  import/delete/reset uncertainty, and never retries a destructive request implicitly.
- Closed the automatic-fix apply response loop. The frontend now validates the
  server-recomputed verified suggestion, strategy, before/after counts, and full
  persisted rule snapshot, then updates the Board directly from that response instead
  of creating a second refresh-failure window.
- Made AI recommendation candidate accounting end to end. All four panels now show raw,
  inspected, kept, rejected, and limit-truncated counts; inconsistent/missing counters or
  per-item reasons reject the response. Backend messages also distinguish an AI model
  returning zero candidates from candidates rejected by capability validation.
- Corrected scenario-recommendation accounting when the backend synthesizes a required
  Environment Pool entry. The frontend now checks final `count` against the four scene
  collections while keeping `validatedCount` tied to inspected raw AI candidates, and it
  validates every filtered/adjusted item rather than accepting empty reason objects.
- Replaced all four untyped AI recommendation REST maps and the two POST request maps
  with explicit Java DTOs, including strong candidate and portable-scene shapes. The
  controller now revalidates candidate accounting and explanation rows before returning
  HTTP 200, so tool/DTO drift becomes an explicit 502 instead of a partial success.
- Removed the permanently empty `warnings` field from REST device-mutation results and
  blocked batch device creation when names would change after the displayed preview. The
  Board now shows the proposed changes and submits no devices instead of silently renaming
  them behind a generic count-only success message.
- Replaced untyped rule duplicate/similarity REST maps with explicit result DTOs and
  matching frontend runtime validation. Missing booleans or explanations, out-of-range
  similarity scores, and contradictory AI duplicate results now fail the check instead
  of being interpreted as evidence that no conflict was found.
- Added runtime conclusion contracts for verification, counterexamples, simulation, and
  persisted simulation history. The Board now requires explicit completeness, matching
  itemized generation issues, consistent model semantics, and structurally playable
  states; completed async verification tasks can no longer infer a conclusion from
  missing fields.
- Extended those contracts across asynchronous task creation, inbox/status polling,
  progress, completed simulation trace references, and cancellation outcomes. Malformed
  200 responses now fail explicitly instead of becoming a false timeout or success, and
  opening a pending, failed, or cancelled simulation task no longer says that a completed
  task merely lost its trace. Cancellation documentation now matches the explanatory DTO.
- Replaced the count-only default-template reload with an impact-token preview and an
  atomic reset result containing every type change, affected device label, blocker,
  Environment Pool change, and final type/environment snapshot. Ordinary catalog GETs
  no longer resurrect deleted defaults, malformed bundled resources fail the whole
  import instead of being skipped, and registration now rolls back when its initial
  default catalog cannot be created.
- Restored the unavailable-attack explanation to the verification and simulation panels.
  The previous condition hid it exactly when the effective attack surface was zero, and
  the simulation copy had been rendered inside the unrelated rename-device dialog.
- Made the attack-effect contract scene-exact. `attackEffects` no longer claims reading
  falsification for scenes without a falsifiable reading, or command loss for scenes
  without rules. The immutable run snapshot now also carries and persists the
  falsifiable-reading device subset count; backend analysis deduplicates by canonical
  device instance identity, and the Board explains the exact mechanism counts.
- Made canvas motion truthful to the saved model trace. Ordinary topology edges and
  idle rules are now static; command-flow particles appear only when the backend says a
  rule produced the selected state, and a compromised delivery link never animates.
- Renamed the machine-readable command-loss attack effects from `MAY_BE_DROPPED` to
  `IS_DROPPED`. The NuSMV guards deterministically block a command once its target device
  or delivery link is selected as compromised; DTOs, frontend checks, UI wording, and
  documentation now state that behavior exactly.
- Made device-list JSON import reject conflicting declarations of the same shared
  Environment Pool value, control-source label, or sensitivity label. Identical and
  complementary declarations still merge, while conflicts name both input rows and no
  device in the batch is created.
- Made every template API explicitly declare `Signal`. Omitting the field no longer
  silently turns a state-changing action into a command-only action; `true` means the
  event can trigger automations/specifications and `false` means command-only. Device
  details now use that user-facing wording instead of the implementation term “Signal”.
  Observable API routes are also rejected when another API or autonomous Transition
  could produce the same pulse, preventing one action from being reported as another.
- Made API `StartState` explicit. Template import no longer interprets a missing command
  precondition as “callable from any state”; authors must write an empty string/`_`
  pattern for that deliberate choice or provide a concrete start state.
- Rejected unknown JSON fields across user-facing REST request DTOs instead of silently
  discarding misspelled board, model, fix, auth, or chat inputs. Verification and
  simulation now report the exact unsupported nested path, retain HTTP `400` for DTO
  shape errors, and reserve `422` for model/template semantic validation.
- Validated raw verification/simulation environment overrides before default merging.
  Duplicate names, explicit blank values or trust/privacy labels, and invalid domains now
  fail visibly; omitted or `null` model-request fields retain their documented
  template-default meaning. Board Environment Pool REST edits use the separate
  field-patch contract documented above.
- Made device-list JSON import reject and identify unsupported top-level and nested
  runtime fields rather than creating a device after silently dropping them.
- Corrected the specification architecture contract for Safety template 7. The
  executable property checks attacked and non-attacked paths alike and never injects an
  `is_attack=FALSE` escape clause; only the main-module invariant limits the selected
  attack budget. The previous document example described the opposite behavior.
- Aligned the Environment Pool's defensive display fallback with the backend: an
  unresolved legacy source label is shown as untrusted rather than silently appearing
  trusted. Valid current templates still provide explicit trust/privacy labels.
- Made `InternalVariables[].IsInside` required across the canonical schema, Java DTO,
  frontend type/import preflight, and AI template guidance. Template authors must now
  explicitly choose device-local versus scene-shared ownership; omission can no longer
  silently turn an instance value into a shared environment value.
- Removed the implicit boolean domain for template variables. Every internal/shared
  reading must now declare either enum `Values` (including explicit `TRUE`/`FALSE` for a
  boolean) or complete numeric bounds, so a forgotten domain cannot be accepted with
  different model semantics.
- Rejected attack-enabled verification/simulation when a scene has no automation link
  and no reading declared falsifiable on compromise. The Board now disables the option
  with an explicit reason instead of reporting a behaviorally identical no-op run as
  attack analysis.
- Excluded behaviorally inert device instances from the MEDIC compromise budget. A
  device is now a countable attack point only when it has a declared falsifiable reading
  or receives an automation command; rule delivery links remain separate points. Model
  generation, request validation, async task snapshots, result semantics, Board budget
  controls, AI tool descriptions, and documentation now use the same effective surface.
- Required a stateful template's `InitState` to be one concrete complete
  `WorkingState`. Wildcard, partial, or undefined initial configurations now fail at the
  canonical backend boundary, matching manual device creation and portable-scene
  semantics.
- Replaced remaining Safety-template preview text that called MEDIC control-source
  labels an "untrusted state" or generic "untrusted data". User-facing summaries now
  match the generated property: the protected condition must not hold when any related
  control-source label is untrusted.
- Aligned the executable trust aggregation and machine-readable run contract with MEDIC
  Definition 3.3. Trust now means retained trusted control rather than generic integrity
  taint: one trusted trigger source keeps the target trusted, and only an all-untrusted
  trigger set marks it untrusted. Verification UI text now states this limitation.
- Revalidate raw stored template manifests at every model-build boundary. Unknown fields
  and missing required security labels now stop verification before DTO conversion;
  content privacy is no longer silently defaulted to public for stale template records.
- Made standard scene import fail closed on unknown JSON fields. The frontend now reports
  the exact unsupported path before confirmation, while `/api/board/batch` strictly
  parses every non-template DTO and validates raw template manifests before typed
  conversion. Response-only and template-catalog ids are rejected, preventing a lossy
  import from being reported as a complete replacement.
- Removed the unreferenceable `Transition.Signal` field from the canonical template
  schema, backend/frontend DTOs, AI guidance, and docs. Autonomous transitions now
  require a structured trigger and one modeled effect; user-visible one-step event
  pulses remain available only on state-changing APIs with `Signal=true`.
- Removed the misleading `WorkingState.Invariant` field from schema, DTOs, frontend
  types, device details, defaults, and examples. It was stored and displayed as if it
  constrained verification but was never read by the generator; device behavior and
  checked requirements now remain exclusively in structured Dynamics, Transitions,
  rules, and specifications.
- Removed unsafe implicit `trusted`/`public` template labels. Working states and internal
  variables now require explicit trust and privacy, content items require privacy, and
  frontend import preflight plus AI template guidance enforce the same contract. The
  built-in Oven template now labels its three local variables explicitly. Runtime
  builders inherit template labels only when an override is omitted; an explicit invalid
  label remains visible to validation instead of being silently replaced.
- Declared read-only trust/privacy labels for stateful sensor templates that have modes
  but no command APIs. Rules and specifications can now use those states as labeled
  sources without generating references to undeclared NuSMV variables; compromise still
  affects only explicitly falsifiable readings rather than hijacking sensor state.
- Corrected variable-evolution semantics and made them user-visible: undeclared
  device-local enum/boolean behavior now stutters instead of changing arbitrarily,
  while verification, simulation, and counterexample results return and display the
  declared-rate/device-effect policy for shared numeric values and domain-bounded
  nondeterminism for shared enum/boolean environment values.
- Rejected accepted-looking template behavior that the formal model could only apply
  partially or ignore. APIs are now state-only device commands (not network endpoints),
  API assignments/triggers and stateless APIs fail fast, API signals pulse only on an
  actual complete state change, and autonomous Transitions are limited to one validated
  state or variable effect. Environment-triggered state transitions now read the shared
  environment value instead of an undeclared device-local field.
- Made state-dependent template Dynamics domain-safe and executable. Numeric targets use
  integer rates; enum/boolean targets use validated values; unknown, duplicate, wrong-type,
  descending-range, normalized-duplicate, and malformed natural-rate declarations fail
  before save/model generation instead of being silently skipped or assigned a fallback
  rate. Boolean impacted variables no longer receive invalid numeric `_rate` machinery.
- Persisted immutable device/link/total attack-point counts with verification and
  simulation tasks and returned them in `modelSemantics`. Current and historical result
  UIs now explain the selected budget against the run snapshot rather than silently
  recomputing a potentially different denominator from the current board.
- Made automation execution precedence visible and user-controlled. Rules now persist an
  explicit order, the Board provides identity-preserving up/down controls backed by an
  atomic reorder endpoint, and standard scene JSON preserves the same semantics through
  `rules[]` order. State transitions, triggered-rule traces, and MEDIC trust/privacy
  propagation now share the exact first-selected branch, including API start-state and
  attack-delivery guards, so an unexecuted lower rule can no longer update labels.
- Corrected the machine-readable privacy contract to include rule-selected content
  sensitivity as well as trigger-source labels. UI scope text, TypeScript consistency
  checks, API/architecture docs, and tests now describe the actual propagation model
  without implying payload copying, access control, encryption, or transmission blocking.
- Separated user-facing device names from persistent device identity. Manual UI and AI
  `add_device` creation now assign opaque `device_*` references while preserving explicit
  display labels; case-insensitive conflicts are rejected without a write, and renaming
  never changes rule/specification identity.
- Treated complete-scene AI ids as response-local graph aliases instead of permanent
  user identity. `recommend_scenario` now assigns portable `device_1...` references and
  rewrites rule sources/targets, content sources, and specification conditions together,
  so punctuation/case in an LLM alias cannot merge devices at the NuSMV boundary.
- Added board-write model-namespace preflight for generated shared-environment, rule
  playback, attack-analysis, and existing-condition automatic-fix identifiers. Invalid
  standard scene JSON is rejected before any collection write with a reason attached to
  the offending device reference; the display name may remain unchanged.
- Extended direct verification/simulation namespace validation to include generated
  rule execution and automation-link attack markers, using shared constants with the
  generator and trace parser instead of drifting duplicate strings.
- Preserved every semantic `ValidationException` field error in REST `422` responses as
  `data.errors`. Scene import now shows a complete diagnostic list for compound failures
  and explicitly leaves the current board unchanged instead of surfacing only the first
  rejected field.
- Added explicit AI-scene adjustment feedback for deterministic runtime/layout defaults
  and missing required environment entries, separated from rejected and truncated
  candidates. The preview now shows device-local/environment runtime semantics and does
  not present a no-mode sensor's internal `Working` placeholder as a real state machine.
- Made standalone device recommendations expose the exact initial runtime that creation
  will use. Omitted labels, state/source/sensitivity labels, and local variable values are
  materialized from deterministic template defaults and listed in `adjustedItems`; explicit
  invalid values still reject the whole candidate instead of being silently replaced.
- Aligned AI-assistant `add_device` with the same effective-runtime semantics: partial or
  empty local runtime arrays now retain explicit values, fill each omitted template value
  and label, and report the exact defaulted paths. Its tool schema no longer calls the
  user-facing device name an id.
- Unified manual and device-list JSON creation on the same effective local-runtime helper.
  Omitted values now materialize enum-first or numeric-lower-bound defaults before save,
  while explicit blank scalar fields are rejected instead of being silently interpreted
  as defaults; scene exports continue to carry those effective values losslessly.
- Upgraded portable board scenes to schema version 4 and removed the canvas-only
  `Working` state from stateless device semantics. Stateful templates require an initial
  state; stateless scenes reject state-level source/sensitivity fields, restore the
  rendering placeholder only inside the canvas, and omit it again on export and AI scene
  responses.

### 2026-07-10

#### Fixed
- Corrected MEDIC trust propagation so a target event becomes untrusted only when every
  contributing trigger source is untrusted; one trusted source retains a trusted control
  path as defined by MEDIC Definition 3.3. Template-7 safety checks combine protected
  conditions with any untrusted protected-state label,
  and frontend formula previews use the same semantics as generated NuSMV. Multi-mode
  full-state conditions now propagate labels only from the modes they actually read,
  combining trust with AND and privacy with OR; multi-mode APIs include every changed
  state. Template import rejects incomplete state tuples or conflicting labels for a
  reused mode-state component instead of silently selecting a label by JSON order.
- Expanded the attack budget from device instances only to device instances plus one
  logical command-delivery link per submitted automation rule. Compromised links can
  drop their rule command independently, are included in the same upper-bound counter,
  and are returned as stable rule snapshots for named broken-link trace playback rather
  than exposing generated link indexes. Broken-link playback now stops command-flow
  particles, and the UI states that one run does not calculate a minimum violating
  compromise count. Attack-enabled requests now require a positive budget; disabled
  attack mode is the only user-facing state with an effective zero budget.
- Structured trace trust/privacy entries as literal `{ propertyScope, mode?, name }`
  labels and translated internal attack flags/counters to `compromised` and
  `compromisedPointCount`, keeping generated `Mode_state`, `trust_*`, `privacy_*`, and
  link-choice identifiers out of the user-facing trace contract.
- Replaced the ambiguous verification `safe`-only conclusion with explicit
  `SATISFIED` / `VIOLATED` / `INCONCLUSIVE` outcomes and `modelComplete` across sync,
  async, AI-tool, and Board result/history flows. No-emission and parser/count failures
  are now inconclusive rather than being presented as property violations.
- Replaced per-specification `passed` booleans with explicit per-item outcomes and
  stopped emitting `CTLSPEC FALSE` for specifications that cannot be translated.
  Omitted specifications can no longer manufacture violations or counterexamples;
  verification, simulation, async tasks, saved traces, AI tools, and Board history now
  carry and render item-level `{ issueType, itemLabel, reason }` generation issues.
- Made synchronous simulation fail with structured reason codes on timeout,
  interruption, execution failure, or zero parsed states instead of returning an empty
  success DTO. Simulation results, tasks, saved traces, AI history tools, and the Board
  now expose and display reduced-model status through `modelComplete` and
  `disabledRuleCount`.
- Added per-strategy automatic-fix attempt statuses and warnings, blocked fix generation
  and apply for counterexamples produced from incomplete generated models, and made
  forward verification reject any candidate that disables rules, skips specs, or has an
  incomplete emitted/parsed property result set.
- Changed automatic-fix discovery from an implicit serial run of every strategy to an
  explicit choose-and-try flow. Fault localization and strategy execution now have
  independent progress/error states, so a slow parameter search cannot be presented as
  “no suggestions” or hide a viable disable/condition strategy. Trying a strategy is
  explicitly read-only; only the separate Apply action writes server-recomputed rules.
- Renamed the destructive automatic-fix strategy from `disable` to `remove` and its
  response field to `removedRuleDescriptions`. The implementation permanently deletes
  rules and has no reversible enabled state, so REST, AI, frontend, docs, and tests no
  longer imply temporary disablement. Applying this strategy now requires a destructive
  confirmation that names the number of rules to be removed.
- Made `FIX_TIMEOUT_MS` a real pipeline deadline: each fix-time NuSMV capacity wait and
  process run is capped by the remaining budget. Strategy attempts distinguish
  `TIMED_OUT` (started but incomplete) from `SKIPPED_TIMEOUT` (never started), and the
  frontend's server-bounded long requests no longer fail at the generic 100-second CRUD
  timeout while the backend is still computing.
- Fixed the automatic-fix dialog's independent loading state and preference lifecycle:
  opening performs fault localization only, users explicitly try one strategy, editing a
  parameter preference invalidates the old apply action without losing selectable
  targets, and a mutating apply cannot be dismissed as though it were cancelled.
- Preserved persisted rule identity across the frontend verification/simulation model
  boundary. Triggered-rule and compromised-link snapshots now correlate to current
  rule-derived canvas edges, so animation no longer labels every active automation as a
  removed historical rule. Portable scene files and temporary UI ids remain id-free.
- Replaced raw verification `violatedSpecJson` in client responses with a structured
  `violatedSpec` snapshot, kept trace/simulation ownership and persisted request JSON
  server-internal, and returned structured attack/privacy execution context instead.
- Tightened portable scene files to the exact `iot-verify.board-scene` schema/version and
  a self-contained template dependency set: every referenced template requires a
  matching snapshot even if already installed, unreferenced snapshots are rejected, and
  missing device coordinates no longer default silently. Scene v3 also removes derived
  specification labels and requires the exact environment pool with explicit trust and
  privacy labels. Snapshot `name` must exactly match `manifest.Name`, so import cannot
  silently rename a template. Both frontend and backend reject these defects before any
  board mutation.
- Made shared environment semantics self-contained and order-independent. Impact-only
  templates now declare `EnvironmentDomains` without gaining read capability; unused
  account templates no longer supply hidden domains. Board/model boundaries reject
  same-name conflicts in casing, domain/enum order, natural change rate, default trust,
  or default privacy, and shared declarations require explicit trust/privacy labels.
- Documented `currentStatePrivacy` across the Board and AI recommendation contracts so
  manual creation, AI suggestions, and portable-scene JSON all preserve the same
  initial-state sensitivity label without implying access control.
- Tightened user-facing guarantee boundaries across verification, simulation, scene
  import/export, rule duplicate/similarity checks, and auto-fix apply. The Board now
  presents explicit verification outcome plus model completeness rather than a `safe`
  boolean that could be mistaken for full system safety,
  presents simulation as a model trace, includes environment variables in scene
  summaries, and keeps trace/spec/device technical ids in technical details.
- Replaced ordinary board full-list writes with targeted device/rule/spec create,
  update, rename, and delete commands. Mutation responses identify the affected item and
  return authoritative post-mutation collections; `/board/batch` is now reserved for
  explicitly confirmed atomic scene replacement/clear.
- Added dependency-aware device deletion: the UI confirms the exact related rules/specs,
  the backend compares those dependency ids under the write lock, and drift returns 409
  before any write instead of deleting newly related items.
- Made AI deletion of devices, templates, rules, specifications, and saved traces a
  server-enforced two-turn flow. The first call is a no-write preview, the tool loop
  stops, and a later explicit user confirmation is required; device previews use an
  opaque impact token and reject changed collateral effects.
- Kept rule/device/spec creation drafts open until targeted persistence acknowledges
  success, prevented duplicate submits while saving, and made device creation messages
  use the server-confirmed instance name after any conflict rename.
- Changed AI response-serialization fallback from a false success message to
  `RESULT_UNAVAILABLE`, distinguishing read-only failures from mutations that may have
  committed and instructing callers to refresh before retrying.
- Changed deterministic duplicate and AI similarity checks to return readable
  `matchedRule` text instead of rule database ids, and surfaced that rule in manual-create
  and recommendation-apply confirmation dialogs while retaining the explicit
  "not a conflict-free proof" boundary for negative results.
- Completed the auto-fix preferred-range contract: REST, AI tools, frontend types, and
  docs now submit `{ targetId, lower, upper }` copied from `ParameterAdjustment.targetId`
  instead of exposing zero-based rule/condition selectors to callers. Target ids are
  opaque trace-scoped selectors rather than reversible wrappers around internal
  rule/condition keys.
- Tightened the auto-fix apply contract so clients submit only a strategy and optional
  preferred ranges. The server recomputes and verifies the concrete repair before saving;
  normal REST/AI fix responses now expose readable adjustment and removed-rule
  descriptions instead of rule/condition positions or rule database ids.
- Added `rawCandidateCount`, `inspectedCount`, and `truncatedCount` to AI rule, device,
  specification, and coupled-scene recommendation responses, and surfaced truncated raw
  candidates in the Board recommendation panels.
- Removed ambiguous AI-rule `requiresUserInput` output from directly applicable
  recommendations, derived specification template labels from validated `templateId`,
  and stopped truncating an applied rule's displayed name to 30 characters.
- Changed malformed or schema-less whole AI recommendation responses from misleading
  empty HTTP-200 results into structured `AI_RESPONSE_INVALID` / HTTP-502 errors, while
  retaining `filteredItems` for parseable individual candidates that fail validation.
  AI rule-similarity parse failures likewise no longer degrade to a false "not similar"
  result.
- Made AI device and coupled-scene recommendations candidate-atomic for device runtime,
  rule-source, rule-content, and specification-condition validation so invalid nested
  items are reported through `filteredItems` instead of being silently defaulted or
  dropped from an otherwise "successful" recommendation.
- Rejected scene JSON imports that contain environment variables outside the retained
  device-template environment domains, and made `recommend_scenario` report those
  variables as filtered items so scene export/apply round trips do not lose them silently.
- Renamed the frontend specification-template preview field from `ltlFormula` to
  `formulaPreview` and explicitly labels the Control Center formula code as a formula
  preview while keeping CTL/LTL badges as type hints.
- Made specification `formula` and `devices[]` presentation caches derived from
  structured conditions in manual creation, AI-assistant creation, recommendation
  apply, and standard scene import; AI/file-provided preview caches no longer override
  the semantics shown to users.
- Made scene import and clear save the complete board semantic model
  (`nodes`, `environmentVariables`, `rules`, and `specs`) through one `/board/batch`
  transaction, so imported topology cannot be persisted with the previous environment
  pool. Batch device creation appends devices and applies environment patches through a
  targeted atomic mutation rather than replacing unrelated board collections.
- Extended scene-import batch saves so portable template snapshots are checked and any
  missing referenced templates are created in the same transaction as the complete board
  replacement. The response reports `createdTemplates`; failed imports no longer rely on
  a best-effort frontend rollback that could leave template side effects behind. A
  snapshot-marked scene request must provide all four semantic collections, and omitted
  required environment variables are rejected instead of being inherited or defaulted.
- Preserved authored `rules[]`, rule `sources[]`, `specs[]`, and specification
  condition-list order in portable scene JSON canonicalization because previews,
  generation, trace localization, and fix suggestions use positions from the board
  snapshot.

### 2026-07-09

#### Fixed
- Added per-candidate `filteredItems` feedback to AI rule, device, specification, and
  complete-scene recommendations so the Board can show why individual AI candidates were
  rejected by backend capability validation instead of only showing `filteredCount`.
- Reworked auto-fix parameter preferences in the Board dialog to choose from actual
  `ParameterAdjustment` targets; users no longer type rule/condition numbers to produce
  internal `r{idx}_c{idx}` preferred-range keys.
- Changed the REST and AI auto-fix steering contract to `preferredRangeSelections[]`
  (`targetId`, `lower`, `upper`) and reject the old internal
  `preferredRanges` locator map instead of accepting or silently ignoring it.
- Relabeled device/specification formula displays as formula previews with CTL/LTL
  badges where applicable, labeled verification result expressions as actual checked
  expressions, and moved device/specification technical ids behind collapsible technical
  details.
- Aligned coding-agent manuals with the current device-identity contract: board
  references are canonical node ids, labels are display-only snapshots, and stack
  guidance lives in the `CLAUDE.md` files while root `AGENTS.md` mirrors Codex rules.
- Added board scene import/export in the Board header for reusable devices,
  environment variables, rules, specifications, and referenced template snapshots, with
  import validation and rollback on failed saves.
- Improved Board ergonomics: larger default device nodes, direct minimap zoom controls,
  clearer rule edges, inspector device clicks that focus/highlight nodes instead of
  opening details, and environment-pool text that hides backend-only NuSMV names.
- Tightened scene portability and board orientation: scene JSON export is now canonical
  and round-trip comparable, scene import rejects mismatched template snapshots, the
  Board header includes a confirmed Clear Scene action, inspector device/rule/spec tabs
  have consistent collapsible search panels, and created devices/rules are focused on
  the canvas after save.
- Added an end-to-end guard that exports a scene, clears the board, imports the scene,
  exports it again byte-identically, and verifies the imported scene can be modeled.
- Aligned AI `add_device` and backend node creation defaults with the Board UI's
  176x128 device node size.
- Aligned AI-created rules/specifications with user-visible board semantics:
  `manage_rule` now persists readable `ruleString` text, `manage_spec` now derives
  `formula` and bound `devices[]`, and environment variable keys are matched literally
  instead of treating `a_` as a user-facing alias for generated SMV names.
- Removed remaining reserved-prefix leaks from the user contract: `variable_` is no
  longer treated as a hidden canvas-node prefix, `trust_`/`privacy_` condition keys are
  matched literally like `a_` variables, trace environment variables are serialized and
  replayed with literal user/template names instead of generated NuSMV aliases, and
  custom template creation now rejects concrete generated NuSMV identifier collisions.
- Added a coupled AI scene recommendation tool and Action Dock entry. The backend
  `recommend_scenario` tool returns one importable `iot-verify.board-scene` draft whose
  devices, environment variables, rules, and specifications are validated together,
  instead of stitching together independent device/rule/spec recommendations.
- Improved AI recommendation UX: rule/device/spec/scene responses now expose validation
  counters so the Board can explain filtered suggestions, and device recommendations now
  return/apply concrete instance hints such as suggested label, role, location, initial
  state, and local runtime values instead of only a template name.
- Tightened AI recommendation application semantics: applying a recommended rule now runs
  the explicit AI similarity check before saving, and scene recommendation no longer
  reports a complete scenario when validation removes every generated device.
- Synchronized AI-tool documentation/index references after adding `recommend_scenario`
  and `check_rule_similarity`: the endpoint index now lists `/api/board/scenario/recommend`
  and `/api/board/rules/check-similarity`, and the documented tool count/category map
  reflects 33 tools including environment management, scene recommendation, and AI
  rule-similarity tools.
- Split rule duplicate detection from AI semantic similarity analysis. `Create Rule`
  now uses a deterministic typed trigger/action duplicate check before saving, while the
  original external-LLM analysis is available through the explicit AI similarity check
  action and `/api/board/rules/check-similarity`.
- Fixed fix-apply semantic drift detection for environment-only changes: the canonical
  board fingerprint now includes shared environment variables that are affected by
  devices even when no current device reads them, so stale fixes cannot be applied after
  changing those environment initial values.
- Tightened Board scene-import and creation feedback: imported rules now fail fast when
  required target command fields are missing, and newly created specifications focus and
  highlight in the inspector just like devices/rules.
- Bound retained NuSMV temporary model directories to diagnostic identity: verification
  and simulation model dirs now include `user_<userId>` plus `sync` or `task_<taskId>`,
  saved simulation dirs use `saved_trace`, and auto-fix model dirs include
  `trace_<traceId>`.
- Aligned async simulation feedback with sync simulation and async verification: when a
  user waits for an async simulation to complete and no other animation is active, the
  Board opens the simulation timeline immediately; if another timeline is active, the
  completed trace stays in history without stealing focus, and the user is told where
  to find the saved run instead of seeing a silent completion. Playback now stops as
  soon as the final state is shown, resets when a same-length run replaces the visible
  simulation, and disables Play for one-state counterexamples.
- Clarified verification-result status in the Board UI: a `safe=true` response with
  disabled rules or skipped specs now shows a warning state instead of presenting the
  incomplete emitted-spec check as full system safety.
- Removed the remaining auto-fix preferred-range rule/condition number inputs in favor
  of selecting parameter-adjustment targets with fault-rule context.
- Corrected specification UI terminology: the spec panel no longer describes the
  mixed CTL/LTL template set as LTL-only, and the creation preview now says
  specification description while deriving the CTL/LTL badge from the generated formula.
  The preview sentence is now localized and formats state/mode/variable/API/trust/privacy
  targets as user-facing device properties instead of hard-coded English fragments.
- Clarified the rule-save contract in docs and code comments: `saveRules` takes the
  complete desired rule list, preserves surviving ids/`createdAt`, inserts new rules,
  and deletes existing rules omitted from the request.
- Changed AI `manage_spec` add semantics to require an explicit `templateId` instead of
  silently defaulting missing ids to the Always template, preventing ambiguous AI-created
  specifications.
- Prevented incomplete async verification tasks from opening as unsafe results: failed,
  cancelled, pending, and running tasks now show task-state feedback instead of coercing
  a missing `isSafe` value to `false`.
- Separated trace runtime globals from board environment variables: the compromised-point counter and
  other NuSMV globals now serialize under `TraceStateDto.globalVariables`, while
  `envVariables` contains only literal user environment names.
- Preserved literal device variables that look like generated NuSMV helper names
  (`trust_*`, `privacy_*`, `*_rate`, `*_a`) during trace parsing instead of routing or
  dropping them by prefix/shape alone.
- Added a concrete `MODULE main` namespace collision guard so device instance ids cannot
  collide with generated environment identifiers (`a_<name>`), the compromised-point counter, or
  auto-fix `param_*` / `lambda_*` variables in the emitted SMV model.
- Aligned AI verification/simulation tool argument validation with REST/service
  semantics: out-of-range `attackBudget` and simulation `steps` now return a structured
  validation error instead of being silently clamped.
- Disabled silent JSON scalar coercion and count clamping at user/API boundaries:
  integer and boolean fields now reject quoted strings/floats, AI id/count arguments
  fail before board loading when malformed, and the Board UI validates recommendation
  counts, simulation steps, attack budget, and scene-import geometry without rewriting
  user input.
- Clarified NuSMV init-value semantics in docs and generator comments: user-facing
  device/environment initial values are rejected at save/model boundaries when illegal;
  generator-level clamping is only defensive fallback behavior for direct low-level calls.
- Hardened AI integer-argument validation against oversized JSON integers and documented
  non-integer rejection. `attackBudget` is an upper bound over device-instance and
  submitted automation-link points; attack-mode requests cannot exceed that total, and
  the Board UI uses `min(50, deviceCount + ruleCount)` as the visible slider limit.
- Hardened `fix_violation.preferredRangeSelections` parsing so oversized JSON integers
  cannot be truncated into accepted 32-bit bounds.

### 2026-07-06

#### Changed
- **Board panel state now lives only in `board_layout`.** `BoardLayoutDto.panels`
  carries control/inspector collapsed state, width, and active section alongside canvas
  pan/zoom. The old `board_active` DTO/entity/repository/API was removed.
- **Verification spec results are now identity-bearing objects.** Sync verification,
  completed async verification tasks, and `verify_model` AI tool output now return
  `specResults` as `{ specId, outcome, expression }` entries for the specifications
  actually emitted to NuSMV. Async task persistence stores this object-array JSON in the
  existing `specResultsJson` column; `specResults` is strictly the structured shape (the
  pre-release boolean-array format is no longer read, so the column must not contain it).
- Verification now treats "no specifications emitted to NuSMV" as an unreliable failure
  (`safe=false`, empty `specResults`) instead of a vacuous pass, and completed async task
  `violatedSpecCount` now counts failed structured spec results rather than only saved
  traces.
- Async verification submission is centralized through `submitVerification`: invalid
  requests are rejected before task creation, queue saturation marks the created task
  failed and returns `503`, and retained low-level `verifyAsync` calls now require a
  non-null task id and use the same submit-before-poll semantics.
- Async simulation now follows the same centralized submission pattern through
  `submitSimulation`, so REST and AI callers no longer duplicate task creation,
  dispatch, and failure-compensation logic.
- Task inbox summary endpoints now accept optional `excludeTaskIds`, and the frontend
  uses it while explicitly watching a task so the 5s inbox refresh does not re-fetch the
  same task already covered by the 1s per-task polling loop.
- Verification and simulation service-layer entry points now deep-snapshot requests and
  run NuSMV runtime validation before execution or task creation. Direct service and
  AI-tool callers can no longer mutate queued DTO objects after submission, bypass null
  list-item checks, or skip runtime constraints such as attack intensity, simulation
  steps, device identity, and executable specification conditions. REST endpoints still
  keep their full DTO Bean Validation at the HTTP boundary.
- Synchronous simulation now propagates validation errors instead of returning a
  success-shaped empty result; `simulate_model` reports those failures as structured
  `BUSINESS_ERROR` responses.
- Saved simulation traces now persist the same validated execution snapshot used by the
  NuSMV run, so direct service callers cannot mutate the original request object during
  execution and skew `requestJson`.
- Async verification and simulation now expose lightweight per-user task inbox endpoints
  (`GET /api/verify/tasks`, `GET /api/simulate/tasks`). The Board UI uses them for a
  task inbox and global mini task indicator, so background tasks remain visible and
  cancellable after closing the submit panel or refreshing the page.
- **Board UI chrome was normalized around responsive layout and theme tokens.** The
  side panels, floating panels, task/history surfaces, canvas map, and trace/simulation
  timelines now use shared board surface/card/form tokens; timelines are bottom-centered
  between side panels, node labels/states have bounded responsive layout, and stable
  Playwright selectors cover the primary user-facing regions.
- **Canvas tool overlays were tightened for real canvas work.** The canvas map is now
  compact/translucent, docks to the visible canvas top-left, keeps its mini-map dots
  and edges inside the viewport, and its fit/center buttons are covered by the real
  browser check. Trace/simulation timelines are lighter, the right action rail no
  longer overlaps the inspector, and the grid is painted as an infinite viewport
  background driven by pan/zoom.
- **The board action rail is now grouped and accessible.** Run actions and AI
  suggestion actions are visually separated, desktop buttons show short text labels,
  icons are distinct, and every tool button exposes an explicit accessible name and
  pressed state for keyboard and screen-reader users.
- **The system inspector now uses entity tabs with local create affordances.** Devices,
  rules, and specifications are browsed one category at a time, each list has a nearby
  add action that opens the matching control-center form, and the inspector active tab
  is persisted through `board_layout.panels.inspector.activeSection`.
- **Board usability checks now cover tool panels, language/theme variants, and trace
  edge cases.** Floating tool panels expose stable selectors, recommendation panels use
  localized labels/actions, side panels clamp or wrap long text, missing device images
  fall back to inline SVG, and the simulation timeline is checked with short, standard,
  and long traces from the real backend.

#### Removed
- The `VerificationService` / `SimulationService` interfaces no longer expose the
  low-level async task plumbing (`verifyAsync`/`simulateAsync`, `createTask`,
  `failTaskById`). REST and AI callers go through `submitVerification` /
  `submitSimulation`, which own validation, task creation, and failure compensation
  internally; the remaining pieces are package-private implementation details.

### 2026-07-05

#### Fixed
- **Empty verification requests no longer succeed vacuously.** Sync and async verification now
  require at least one specification at the DTO boundary (`@NotEmpty`), the Board UI blocks
  no-spec verification before calling the API, and service-layer defensive paths fail instead of
  returning a satisfied result with empty `specResults`. NuSMV generation warnings and fix
  forward verification remain explicit: omitted specs surface as structured issues, and empty
  NuSMV result sets are not treated as verified fixes.
- **Fix-apply now blocks spec/device-only drift.** Applying a verified fix previously replayed the
  trace's stored context on the server, so editing spec conditions or device instance state
  (variables, privacies, initial state, trust) after verifying — without touching rules or templates —
  was not detected and a stale fix could be persisted onto the current rules. apply now compares a
  canonical **semantic fingerprint** of the trace snapshot against the current board (device names
  canonicalized, empty variable/privacy lists manifest-defaulted, values de-quoted, so an untouched
  board still matches), and rejects with `400` on drift. The check runs **inside the same per-user
  write lock + transaction** as the rule save (read → check → write is one atomic critical section), so
  a concurrent spec/device/node edit cannot slip in between the check and the write. When the current
  board fails to build a device model it fails closed, distinguishing cause: an invalid/changed board
  rejects with `400`, while an unconfirmable infrastructure error (e.g. template repository unavailable)
  rejects with `503` ("retry later") instead of misattributing it to a board change.
- **Device reference resolution unified across spec generation, drift fingerprint, and fix candidates.**
  A single `DeviceReferenceResolver` now owns the `deviceId → deviceLabel → normalized-label` fallback
  order, so the NuSMV generator, semantic fingerprint, and fix-candidate builder no longer each guess
  device names independently (they previously disagreed for AI/historical specs carrying a node-id
  `deviceId` plus a label). condition-fix `add` now maps verification-time names (`d_1Lamp`) back to the
  current board's persisted label (`1Lamp`) before saving, so the frontend can resolve the node.
- **Template-drift check fails closed on apply.** A template-repository error during apply no longer
  proceeds to recompute and persist; it is treated as unverifiable drift and rejected. `/fix` still
  fails open (a repo error only drops the advisory warning).
- **Digit-leading device labels no longer misfire the rule-drift check.** The frontend prefixes such
  labels (`1Lamp` → `d_1Lamp`) in the verification snapshot while rules persist the raw label; the
  apply-time rule fingerprint now canonicalizes both sides, so an untouched board is no longer rejected.
- **Historical trace playback respects the same guards as current-result playback.** Viewing a saved
  verification trace now checks the simulation-timeline / recommendations mutex, takes the animation
  lock, and closes the result dialog; the `View` button is disabled while those panels are open.
- **Trace attack/intensity labels reflect the viewed trace.** `TraceDto` now derives and exposes
  `isAttack` / `intensity` / `enablePrivacy` from its stored request snapshot, and the trace control bar
  reads them instead of the live verification form, so a historical trace is labelled with the
  parameters it was actually run under.
- **Successful-simulation logs are reachable.** A successful simulation opens the timeline directly; its
  execution logs and raw NuSMV output are now retained and openable on demand via a "View logs" action
  (previously the result dialog holding them was only reachable on error).
- **AI board overview now reports the same rule connections as the canvas.** `board_overview` derives
  edge summaries from rule conditions and commands instead of the optional persisted `/board/edges`
  geometry table, matching the frontend's rule-derived canvas connections.
- **Async verification and simulation can be cancelled from the Board UI.** The existing cancel REST
  endpoints are now reachable from the async progress panels, and user-requested cancellation is shown
  as an informational outcome rather than a generic failure.
- **`fix_violation` is discoverable by the AI planner.** The tool was registered and documented, but the
  system prompt and explicit tool-name router omitted it; both now list the tool.

### 2026-07-04

#### Changed
- **Decoupled the LLM backend from Volcengine Ark; the AI assistant now targets any
  OpenAI-compatible endpoint.** Introduced a vendor-neutral LLM layer under
  `component/ai/`: a domain model (`LlmMessage`, `LlmToolCall`, `LlmToolSpec`,
  `LlmChatRequest`/`LlmChatResponse`), a `LlmProvider` strategy interface, and an
  `OpenAiLlmProvider` adapter that is the sole holder of an LLM SDK import. Facades
  `LlmChatService` (tool loop + streaming), `PromptCompletionService` (one-shot
  recommend/duplicate-check completions), and `LlmMessageCodec` (persistence wire-format
  ⇄ domain conversion) sit between the business layer and the provider. `ChatServiceImpl`
  and all AI tools now depend only on the domain model — no SDK type leaks into business
  code. Tool declarations return `LlmToolSpec` instead of the SDK's `ChatTool`.

#### Fixed
- **NuSMV generation warnings are now part of the verification contract.** Rule
  conditions that cannot be generated fail closed to `FALSE`, skipped/invalid specs are
  omitted rather than emitted as false properties, and verification/simulation DTOs
  return `generationIssues` alongside `checkLogs`, `disabledRuleCount`, and
  `skippedSpecCount` so a satisfied subset cannot hide that part of
  the requested model was excluded. Warning collection is passed through a request-scoped
  `SmvGenerationContext` instead of global mutable state, and completed async verification
  tasks now persist/return the same two count fields.
- **Rule creation no longer fabricates dummy triggers.** Frontend save, duplicate-check,
  direct verify, and simulation paths validate that every rule has at least one concrete
  trigger condition; the backend also requires non-empty `RuleDto.conditions`.
- **Specification persistence now keeps the authored formula and device bindings.**
  `SpecificationDto`/`SpecificationPo`/`SpecificationMapper` preserve `formula` and
  `devices` metadata across board saves.
- **Board edge storage is geometry-only again.** Frontend API mapping no longer expects
  phantom edge fields such as `fromApi`, `toApi`, `itemType`, `relation`, or `value`.

#### AI Tools
- **AI rule/spec recommendations now use device labels as their primary references.**
  `recommend_rules` emits `deviceName` values that match board labels, and
  `recommend_specifications` requires `templateId` to be one of `"1"` through `"7"`;
  recommendations with illegal template ids or unresolvable devices are filtered out.
  Tool validators, prompt schemas, and backend DTO validation now also converge on
  supported relation operators and non-empty condition values.
- **Device template manifests now have an executed canonical schema.**
  `backend/device-template-schema.json` is validated by REST template import,
  AI `add_template`, and default-template initialization before DTO mapping and NuSMV
  pre-checks. API triggers are now explicitly schema-invalid; conditional template
  behavior must be modeled through `Transitions`.

#### Configuration (breaking)
- **Config keys renamed `volcengine.ark.*` → `llm.*`.** Env vars: `VOLCENGINE_API_KEY` →
  `OPENAI_API_KEY`, `VOLCENGINE_MODEL_ID` → `OPENAI_MODEL`, `VOLCENGINE_BASE_URL` →
  `OPENAI_BASE_URL`, `ARK_TIMEOUT_MINUTES` → `LLM_TIMEOUT_MINUTES`; new `LLM_PROVIDER`
  (default `openai`). Point `OPENAI_BASE_URL` at the official API or a relay.
  `ProductionSafetyCheck` now guards `llm.api-key` (`OPENAI_API_KEY`).

#### Dependencies
- Replaced `com.volcengine:volcengine-java-sdk-ark-runtime` with
  `com.openai:openai-java` (4.41.0). Removed `ArkAiClient` and `ArkAiConfig`.

### 2026-07-03

#### Security
- **Fixed a `UserContextHolder` ThreadLocal cross-request leak in `JwtAuthenticationFilter`.**
  The filter set the per-request `UserContextHolder` (a `ThreadLocal` read by the AI-tool
  path via `AbstractAiTool`) but never cleared it. On a reused Tomcat worker thread, a
  later request arriving without a valid token would neither set nor clear it and would
  observe the previous request's `userId` — a potential cross-user access on the AI-tool
  path. The filter now clears `UserContextHolder` in a `finally` around
  `filterChain.doFilter` (covering the blacklisted-token early path too). The REST path
  was unaffected — `@CurrentUser` reads `SecurityContextHolder`, which Spring clears per
  request.

#### Changed

- **Integrated duplicate-rule checking in rule creation dialog.**
  The `POST /api/board/rules/check-duplicate` endpoint (backend implementation existed
  but was frontend-unintegrated) is now callable via `boardApi.checkDuplicateRule(rule)`.
  `RuleBuilderDialog.vue` added a visible check action and confirmation flow; the current
  2026-07-09 contract splits deterministic save-time duplicate detection from the
  explicit AI similarity action.
- **Frontend API base URL is now relative by default and configurable end-to-end.**
  Both `src/api/http.ts` (axios, `(VITE_API_BASE_URL || '') + '/api'`) and
  `src/api/chat.ts` (SSE) derive their base URL from `import.meta.env.VITE_API_BASE_URL`.
  When it is empty (the default) requests go to a relative `/api`, which the Vite dev
  server and a production reverse proxy (Nginx) forward to the backend — so dev and
  same-origin prod need no config. Previously axios hardcoded `http://localhost:8080/api`,
  which bypassed the Vite dev proxy and, in prod without an override, pointed the
  browser at the user's own machine. Set an absolute `VITE_API_BASE_URL` only for
  cross-origin deployments (resolves former frontend fix item F-11).

#### Fixed
- **Custom-template API editor now emits a backend-valid manifest.** The template
  creator (`CustomTemplateCreator.vue`) previously produced API definitions that the
  NuSMV pre-check rejected:
  - `Trigger` was built from a single pseudo-value (`user`/`auto`/`event`) as
    `{ Attribute: <pseudo>, Relation: 'EQ', Value: '' }` — Attribute wasn't a legal
    mode/internal-variable and `Value` was blank, both failing P1
    (`validateTriggerCompleteness` / `illegalTriggerAttribute`). It is now edited as
    three fields `{ Attribute, Relation, Value }` — Attribute a dropdown of legal
    modes + internal variables, Relation ∈ `= != > >= < <=`, all required when set
    (or omitted entirely for no trigger).
  - API `Assignments` used the wrong field names `{ VariableName, ChangeRate }`; the
    backend DTO is `{ Attribute, Value }`, so assignment data was dropped and validation
    failed. Now emitted as `{ Attribute, Value }`.
- **Spec trust/privacy conditions restrict the relation operator.** For `targetType`
  `trust`/`privacy` (enum-valued), the operator dropdown now offers only `= != in not_in`
  (was also offering `> >= < <=`, which generate meaningless ordering comparisons on
  enum domains).
- **Async verification/simulation polling reworked for correct lifecycle & error
  handling** (`Board.vue`):
  - Verification async polling is now an awaited `pollAsyncVerification(taskId)`
    (a serial `while` + `await sleep` loop, matching `pollAsyncSimulation`) instead of a
    fire-and-forget `setInterval`. Two problems are fixed: (a) the `async` branch used to
    return immediately, so the outer `finally` set `isVerifying=false` while polling was
    still running — the progress bar disappeared at once and the verify button
    re-enabled, letting the user launch duplicate tasks; now `isVerifying` stays true
    until polling truly ends. (b) the old `setInterval(async …)` callback could re-enter
    concurrently when a status request took longer than the 1s tick (duplicate requests,
    duplicate toasts, stale progress overwrites); the serial loop can't re-enter.
  - Both pollers surface terminal states (`FAILED`/`CANCELLED`) immediately with the
    task's `errorMessage` (simulation previously swallowed `FAILED` in its transient
    `catch` and only reported a generic timeout after 2 minutes).
  - Both pollers distinguish **permanent** status-fetch errors (HTTP 4xx — auth,
    forbidden, task-not-found) from **transient** ones (network blips, 5xx): permanent
    errors fail fast; transient errors retry until the poll ceiling.
  - Both are bounded (simulation 2 min, verification 10 min) so a task stuck in
    `RUNNING` (e.g. a hung NuSMV run) surfaces a timeout instead of polling forever.
- **Rule saving now honors the incremental-upsert contract.** `boardApi.getRules` used
  to prefix every existing rule's DB id as `rule_<id>`, and `saveRules` treated any
  `rule_`-prefixed id as new (sent `id: null`) — so every save of an existing rule
  re-inserted it and deleted the old row, churning ids and resetting `createdAt` (against
  the backend design and `docs/api/board.md`). `getRules` now returns the raw numeric id;
  only client-created rules (`rule_<timestamp>`) send `id: null`, so existing rules are
  updated in place.
- **Custom-template JSON import no longer corrupts enum variables.** The importer used to
  inject a default `LowerBound: 0 / UpperBound: 100` even when the source variable had
  `Values` (enum) — producing a manifest the backend rejects (`@AssertTrue
  isValidVariableDefinition`: `Values` XOR range, never both). It now emits `Values`
  as-is and only writes bounds when the source actually had them.
- **Custom-template API editor validates Trigger/Assignment completeness.** `confirmSaveApi`
  now blocks a Trigger with an Attribute but no Relation/Value, and any half-filled
  assignment, matching backend P1 (`validateTriggerCompleteness`) / assignment validation.
- **Custom-template manual-build path applies the same `Values` XOR range rule.** The
  form's build-manifest step used to always emit `LowerBound`, `UpperBound`, and filtered
  `Values` together; it now emits enum `Values` when present, otherwise the range —
  matching the JSON-import path (the UI currently exposes only range inputs, so this is a
  robustness/consistency fix rather than a live UI bug).
- **`boardApi.saveRules` return type corrected to `Promise<void>`.** It previously claimed
  to return `RuleForm[]` but actually unpacked the backend `RuleDto[]` shape; no caller
  consumed it. Callers needing the persisted rules (e.g. server-assigned ids) should
  re-fetch via `getRules()`.

#### Types (frontend contracts aligned to backend DTOs)
- `DeviceManifest` gained `Contents` (`DeviceContent { Name, Privacy, IsChangeable }`);
  `Dynamic` gained the optional `Value` (backend allows `Value` XOR `ChangeRate`);
  `DeviceAPI.Assignments` is now `DeviceAssignment[]` (`{ Attribute, Value }`) instead of
  `any[]`.
- `SimulationState` gained `rules?` and `trustPrivacies?` (backend `TraceStateDto`).
- `DeviceNode` gained `currentStateTrust?`, `variables?`, `privacies?` (backend
  `DeviceNodeDto`), removing the need for `(node as any)` casts.
- Board panel active state is no longer modeled by a separate frontend type; layout
  state belongs to `BoardLayoutDto`.

#### Removed (dead / duplicate frontend types)
- `types/panel.ts` was removed. Layout DTO types live in `types/canvas.ts`, and panel
  collapsed/active-section state is part of `BoardLayoutDto.panels`.
- `types/spec.ts` no longer exports `relationOperators`, `RelationOperator`,
  `targetTypes`, `TargetType` — unused duplicates of the live versions in
  `assets/config/specTemplates.ts` (which is what components import). Prevents the two
  copies from drifting.
- `api/rules.ts` no longer exports `getRules`, `saveRules`, or the `Rule` interface —
  a dead second rule-persistence surface. Rule persistence lives only on `boardApi`
  (`api/board.ts`); `api/rules.ts` now owns rule *recommendation* only.
- `assets/config/specTemplates.ts` no longer redefines `SpecTemplateType` /
  `SpecTemplateDetail`; it imports them from `types/spec.ts` (and re-exports for existing
  importers), leaving `types/spec.ts` as the single source.
- `types/spec.ts` dropped the unused `SpecForm` interface; `types/rule.ts` dropped the
  unused `GLOBAL_VARIABLES` const and `GlobalVariableName` type (a runtime list that did
  not belong in a types file and had no references).

#### Documentation
- Clarified architecture documentation ownership and kept durable backend design notes
  in the owning API / architecture overview documents rather than a dated audit report.
- **`POST /api/board/rules/check-duplicate` integrated in frontend** through
  `RuleBuilderDialog`; the 2026-07-09 contract now uses this endpoint as the deterministic
  save-time duplicate check and exposes AI semantic analysis separately.
- Aligned `ChatSession`/`ChatMessage` frontend types to backend DTOs (`userId: number`,
  added missing `createdAt`/`sessionId` fields).
- Updated `docs/guides/frontend-integration.md` to clarify `Trace*` / `Simulation*` type
  trees are intentionally parallel but NOT fully isomorphic (e.g., `TraceTrustPrivacy.trust`
  is `boolean | null` mirroring backend `TraceTrustPrivacyDto`, whereas
  `SimulationTrustPrivacy` uses looser `boolean` / optional `privacy`).

### 2026-03-04

#### Fixed
- **Blank `InitState` on modeless sensors**: 16 modeless sensor templates (Weather,
  Clock, Temperature Sensor, Humidity Sensor, …) had an empty-string `InitState`,
  which the AI device-creation path passed through verbatim, persisting `state=""`;
  a later `POST /api/board/nodes` was then rejected (400) by `DeviceNodeDto.state`'s
  `@NotBlank`. Fixes:
  - `NodeServiceImpl.getInitStateFromTemplate()` now `isBlank()`-checks `InitState`
    and falls back to `HARD_FALLBACK_STATE` (`"Working"`); log message corrected to
    "has missing or blank InitState".
  - `DeviceNodeMapper.toDto()` now backfills a null/blank `state` with `"Working"`
    (`FALLBACK_STATE`), preventing legacy dirty data from failing `@NotBlank` on a
    GET → POST round-trip.
  - Added 3 unit tests (`NodeServiceImplMutationTest`): empty, normal, and missing
    `InitState`.
- **Sprinkler Controller.json**: corrected an API-definition key from the erroneous
  `"s"` to `"Assignments"` (two occurrences).

### 2026-03-03

#### Changed — NuSMV generation pipeline
- **Identifier safety** (`DeviceSmvDataFactory`, `BoardStorageServiceImpl`):
  `sanitizeSmvToken()` now escapes NuSMV reserved words case-insensitively (including
  `W`), on top of space stripping, illegal-character replacement, and digit-prefix
  handling, for generation-time cleaning of mode/state names. `toVarName()` gained the
  same digit-prefix and reserved-word defenses. `computeIdentifiers()` guards
  `result` (varName), `base` (module-name prefix), and `suffix`. InternalVariable /
  ImpactedVariable names are validated at persistence time by
  `validateTemplateManifestForNuSmv()` (regex + reserved words + collision) and are
  **not** run through generation-time sanitization.
- **trust/privacy three-layer defense**: entry normalization
  (`normalizeTrustPrivacy()` = trim + lowercase); validation
  (`SmvModelValidator.validatePropertyValues()`); output-layer re-normalization in
  `SmvDeviceModuleBuilder`, defaulting null content privacy to `public`.
- **Numeric-bound clamping** (`SmvBoundsUtils`, `SmvMainModuleBuilder`): attack-mode
  upper-bound expansion centralized in `SmvBoundsUtils.resolveEffectiveUpperBound()`;
  `next()` candidate expressions clamp via `max(lower, min(upper, expr))`.
- **Defensive intensity handling**: `SmvGenerator` clamps `intensity` to `0..50`;
  `SmvBoundsUtils` additionally zeroes negative intensities.
- **`SmvSpecificationBuilder.build()`** gained a 5th parameter `enablePrivacy`; with
  privacy off, a privacy spec is omitted and reported as a structured generation issue
  (defense-in-depth; `validateNoPrivacySpecs` upstream is the primary guard). No
  always-false placeholder is emitted.
- **Regression coverage** (`SmvGeneratorFixesTest`): WITH-rate extreme NCR, internal
  variable boundary branches, `range=0` and negative-intensity cases.

#### Added / Changed — backend hardening
- **Production safety guard**: new `ProductionSafetyCheck` (`@PostConstruct`) refuses
  startup under a `prod`/`production` profile if `jwt.secret`,
  `spring.datasource.password` (`DB_PASSWORD`), or `volcengine.ark.api-key`
  (`VOLCENGINE_API_KEY`) still hold unsafe defaults. `PRODUCTION_MODE` removed; profile
  matching is case-insensitive. `JwtUtil.@PostConstruct` also WARN-logs a default key
  under prod. Superseded by the 2026-07-04 LLM config rename above: the production guard now
  checks `llm.api-key` / `OPENAI_API_KEY`.
- **Exception handling**: `IllegalArgumentException` → masked generic 400,
  `IllegalStateException` → 500, new `DataIntegrityViolationException` → 409 CONFLICT.
- **Thread-pool context propagation**: `ThreadConfig.TaskDecorator` deep-copies
  `Authentication`, `UserContextHolder.userId`, and MDC into child threads.
- **Async-task TOCTOU elimination**: `completeTask`/`failTask` became atomic
  conditional UPDATEs (`WHERE status <> CANCELLED`, `@Modifying(clearAutomatically =
  true)`); `handleCancellation` → `cancelTaskIfStillActive`
  (`WHERE status IN (PENDING, RUNNING)`). `TransactionTemplate` used for
  `VerificationServiceImpl.saveTraces()` and `ChatServiceImpl.processStreamChat()`.
- **Redis resilience**: `RedisTokenBlacklistService` counts consecutive failures
  (`AtomicInteger`), ERROR-alerting every 10th (`% ALERT_THRESHOLD`).
- **Request validation**: `@NotEmpty` devices, `@Size(max=10000)` chat content,
  `@NotNull @RequestBody` coverage (`BoardStorageController` via class-level
  `@Validated`).
- **Read-only transactions**: `@Transactional(readOnly = true)` on all read methods of
  `BoardStorageServiceImpl`, `VerificationServiceImpl`, `SimulationServiceImpl`,
  `ChatServiceImpl`.
- **Entity indexes/constraints**: indexes on `device_edge(user_id)`,
  `verification_task(user_id)`, `simulation_task(user_id)`; unique constraint on
  `device_templates(user_id, name)`.
- **DTO `progress` field**: exposed on `VerificationTaskDto` / `SimulationTaskDto`.
- **`VerificationTaskDto` consistency**: added `@NoArgsConstructor`,
  `@AllArgsConstructor`, `@JsonInclude(NON_NULL)` to align with `SimulationTaskDto`.
- **AI-tool safety**: `AiToolManager.execute()` catch-all returns a generic
  "Tool execution failed due to an internal error" (no `e.getMessage()` leak);
  `AddTemplateTool` pre-builds a `tolerantMapper`; `AddNodeTool` uses
  `parseDoubleOrNull()` / `parseIntOrNull()` to handle JSON null, non-numeric, and
  empty strings (all passed as `null` to trigger default layout values).
- **`ArkAiClient` configurable timeout**: `volcengine.ark.timeout-minutes` (default 5).
- **`JsonUtils`**: registered `JavaTimeModule`; added `fromJsonToStringList()` /
  `fromJsonList()`.
- **DELETE trace 404**: a missing trace now throws `ResourceNotFoundException`
  (previously a silent 200).
- **`JwtAuthenticationFilter`**: `getUserIdFromToken()` wrapped in try-catch —
  malformed tokens treated as unauthenticated.
- **Async controller pattern**: `verifyAsync` / `simulateAsync` return `Result<Long>`
  (no longer `ResponseEntity`); `TaskRejectedException` → `ServiceUnavailableException`.
- **Temp-file retention**: `cleanupTempFile()` is a no-op — `nusmv_*` temp directories
  are kept for post-mortem debugging.
- **Surefire JVM config**: `maven-surefire-plugin` adds
  `-Djdk.attach.allowAttachSelf=true -XX:+EnableDynamicAgentLoading`, fixing
  Mockito/ByteBuddy `MockMaker` init on JDK 17.
- **Error-message suppression**: `application.yaml` sets
  `server.error.include-message: never` and `include-binding-errors: never`.
- **`SecurityConfig` ObjectMapper**: `SecurityFilterChain` uses the Spring-managed
  `ObjectMapper` (inherits `JavaTimeModule` etc.).
- **`ArkAiClient` ObjectMapper**: injected via constructor (Spring-managed) instead of
  a field-initialized `new ObjectMapper()`.
- **`ArkAiClient` parse pre-check**: `parseToolMessage()` / `parseAssistantToolCalls()`
  fast-check `content.stripLeading().startsWith("{")` before `readTree()`, keeping
  plain-text messages off the JSON path; fallback path logs at DEBUG.
