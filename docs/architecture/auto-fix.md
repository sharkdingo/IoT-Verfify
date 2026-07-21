# Automatic Fix

When verification finds a violation, the fix system localizes potentially responsible
rules. Callers choose which repair strategy to try; REST/AI callers that omit the list use
the three-strategy default order. Each offered candidate is re-verified against all specs.

A suggestion is only advisory until the user chooses to **apply** it; applying writes the
repaired rules back to the board (see [Applying a suggestion](#applying-a-suggestion-fixstrategyapplier)).

API contract (`fault-rules`, `fix`, `fix/apply`) → [../api/verification.md](../api/verification.md).
Spec formulas → [spec-templates.md](spec-templates.md).

Verified against code on 2026-07-21. Source: `component/nusmv/fixer/` — `RuleFixer`,
`localize/FaultLocalizer`, `strategy/{ParameterAdjustStrategy, ConditionAdjustStrategy,
RemoveRulesFixStrategy, FixStrategyUtils, FixStrategyApplier}`, `BoardSemanticFingerprint`,
`parameterize/{ParameterExtractor, CounterexampleInitialStateConstraints}`;
`service/impl/FixServiceImpl` (apply flow). Config keys
(`FIX_*`) → [../getting-started/configuration.md](../getting-started/configuration.md).

---

## Pipeline (`RuleFixer`)

1. **Fault localization** (`FaultLocalizer.localize`): identify which rules were
   triggered in the counterexample trace (a fast pass, no NuSMV invocation). This also
   backs `GET /api/verify/traces/{id}/fault-rules`. Localization uses the same
   canonical rule semantics as SMV generation: user-authored IF conditions are read from
   the current trace state `Si`, while the command effect is checked on the transition
   to `Si+1`.
2. **Strategy attempts**: run the requested strategies in order. The default order is
   `parameter → condition → remove`: the first two implement Salus §5.1/§5.2, while
   `remove` is an IoT-Verify destructive fallback. A caller may override the list and order via
   `FixRequestDto.strategies`.
3. Each strategy produces at most one **verified** `FixSuggestionDto` (see forward
   verification below). Results accumulate into `FixResultDto`; `strategyAttempts`
   records a status and reason for every requested strategy, including those skipped
   before execution. A strategy that starts its main candidate search also reports
   `attemptsUsed` and `attemptLimit`.

Before strategy search, `FixServiceImpl` checks the counterexample's source-generation
metadata. If any rule or specification was omitted, no strategy is run: the result has
`fixable=false`, an empty suggestion list, `sourceModelComplete=false`, warnings, and
`SKIPPED_INCOMPLETE_SOURCE_MODEL` for every requested strategy. Apply rejects the same
trace. A repair must not be certified against a counterexample from a reduced model.

The fixer also reuses the trace's complete per-run `attackScenario`. Candidate discovery
pins the first complete counterexample state, including device compromise flags and every
automation-link choice. Exact selections therefore stay fixed; for an exhaustive
`ANY_UP_TO_BUDGET` run, discovery reproduces the concrete attacker branch that produced
this counterexample while forward verification deliberately removes those candidate-only
`INIT` constraints and checks the original exhaustive budget. Automation links are
correlated by persisted rule id rather than generated list position.
Any candidate that removes or duplicates an explicitly selected automation-link rule is
ineligible because it would change that fixed attacker choice rather than repair the model
under the original scenario.

A deadline (`FIX_TIMEOUT_MS`, default 300000) bounds the strategy pipeline. It is checked
before each strategy and inside search loops; every NuSMV capacity wait and child process
also receives the remaining deadline and uses the smaller of that budget and
`NUSMV_TIMEOUT_MS`. A strategy that starts but exceeds the deadline is `TIMED_OUT`;
later strategies that never start are `SKIPPED_TIMEOUT`. Strategies that need spec
negation (`parameter`, `condition`) are skipped if no valid `violatedSpecIndex` is
available; `remove` does not require it
(`FixStrategy.requiresViolatedSpec()`). Unsupported strategy names are skipped.
NuSMV process failures and incomplete or unparseable result sets are reported as
`FAILED_SOLVER_EXECUTION`, rather than as a completed no-result search. A finite candidate
limit that leaves unchecked assignments is `SEARCH_BUDGET_EXHAUSTED`; this is independent
of the wall-clock timeout.

---

## Strategy 1 — parameter adjustment (`ParameterAdjustStrategy`)

Turns a rule's numeric threshold conditions into `FROZENVAR` parameters, then uses
NuSMV to solve `¬ρ` (the negated spec) for corrected values. When multiple thresholds
are in scope, the strategy first searches the smaller repair class in which exactly one
localized threshold changes. It checks policy-boundary hints and then values nearer to
the original. If redundant rules issue the same command and cannot be repaired one at a
time, it next moves their matching policy-boundary thresholds together and resolves any
exact-rule collision by continuing in the trigger-tightening direction. Only then does it
fall back to joint tuple solving. A discovered joint solution is also refined toward the
original values. These are bounded preferences, not a proof of a globally minimum edit if
the attempt or time budget expires.
Same-command coordination uses the complete persisted command identity: resolved target
device, action, resolved content device, and content value. Rules that share an actuator and
action but display or transmit different content are not coordinated as one policy.

Eligibility is deliberately narrower than the paper's abstract value-substitution step:
the persisted condition must use `>`, `>=`, `<`, or `<=`, contain an integer value, and
resolve to a manifest variable that declares both `LowerBound` and `UpperBound`. Equality,
mode, state, and enum conditions are handled as condition-clause candidates rather than
parameter-adjustment targets. When no eligible target exists, the attempt is reported as
`SKIPPED_NO_PARAMETERIZABLE_VALUES` instead of looking like a failed solver search.

The parameterized discovery model uses the candidate-only replay and fail-closed negation
contract defined by the [NuSMV model](nusmv-model.md). Candidate generation also rejects
any model that disables a rule or skips a specification.

- `ParameterExtractor` reads solved numeric values. Policy-boundary hints are accepted only
  from the same resolved device or the same declared shared-environment domain; a same-named
  attribute on an unrelated device cannot consume the bounded search budget. For an integer
  boundary `N`, the bounded single-parameter phase probes `N-1`, `N`, and `N+1`; this covers
  strict/non-strict boundary differences and one-transition environment movement before the
  more expensive joint solver is used.
- Every eligible condition is returned independently in `FixResultDto.parameterTargets`,
  even when no candidate passes forward verification. Each target is `{ targetId, attribute,
  relation, originalValue, lowerBound, upperBound, description }`, so clients can offer a
  preferred range after an unsuccessful first search rather than depending on a successful
  `ParameterAdjustment`.
- Candidate values are searched within optional caller-supplied
  `preferredRangeSelections[]`. Each selection is chosen from a concrete
  `ParameterTarget.targetId` and carries `{ targetId, lower, upper }`;
  `lower`/`upper` are inclusive 32-bit integer bounds. The API-facing `targetId` is an
  opaque selector scoped to the trace/fix context; it keeps zero-based rule/condition
  locators out of REST and AI-tool requests, and the parameter strategy matches it
  against the currently available adjustment targets.
  A selection is considered used as soon as it matches an eligible target, regardless of
  whether that constrained search finds a verified suggestion. Only selections that match
  no parameterizable condition are reported in
  `FixResultDto.unusedPreferredRangeSelections`.
  The Board UI labels each choice with the fault rule text, condition context, attribute,
  and relation so users do not type or infer internal parameter locators.
  It can turn a parameter into an explicit no-change constraint by locking its preferred
  range to `[originalValue, originalValue]`.
- Bounded by `FIX_MAX_ATTEMPTS` (main solve attempts), `FIX_MAX_REFINE_ATTEMPTS`
  (refinement iterations), `FIX_MAX_CANDIDATES_PER_RULE`, and the overall
  `FIX_TIMEOUT_MS` deadline. For a multi-threshold search, at most half of the main
  candidate budget is initially reserved for one-threshold probes. The remaining budget
  is shared by one bounded same-command coordinated boundary probe, when applicable, and
  joint tuple solving. `attemptsUsed` reports this main budget only; the separate closest-value
  refinement budget is not added to it. Distance and refinement-window arithmetic uses `long`
  intermediates so the full signed 32-bit manifest domain cannot overflow.
- Emits API-facing `ParameterAdjustment` entries: `{ targetId, attribute, relation,
  originalValue, newValue, lowerBound, upperBound, description }`. Internal rule and
  condition positions remain inside the fixer and are not serialized to REST or AI callers.
  A strict `> upperBound` or `< lowerBound` result makes its rule unreachable and is labeled
  explicitly in the Board. Non-strict `>= upperBound` and `<= lowerBound` results still match
  one domain value and are not described as disabled.
- A candidate must also satisfy the Board's exact-duplicate rule invariant before it can be
  certified. Parameter and condition edits use the same `RuleSemanticSignature` as persistence;
  a formally passing edit that would duplicate another automation is rejected during search.
  A structurally rejected boundary does not consume a NuSMV attempt, and parameter search
  continues in the relation's trigger-tightening direction to find the next persistable value.
- Witness extraction is covered by a real NuSMV 2.7.1 smoke test on minimal false
  EF/EG CTL models. CI must install NuSMV 2.7.1 for this check; local runs without
  NuSMV skip the smoke test. This confirms the core `FROZENVAR` output behavior for
  that version and environment, but it is not an exhaustive proof for every generated
  template shape.

## Strategy 2 — condition adjustment (`ConditionAdjustStrategy`)

Adds a boolean lambda guard to a rule and uses NuSMV to decide which conditions must be
adjusted. Internally, existing conditions can be `keep` or `remove`, and candidates can
be `add` or ignored; the returned suggestion filters out `keep` entries and emits only
actionable `ConditionAdjustment` entries: `{ action, attribute, targetType, description,
ruleDescription, deviceLabel, relation, value }`. Internal rule/condition positions and
the model device reference needed for an add operation are retained inside the signed
suggestion token and restored only after the server verifies that token during apply.

The lambda scope contains localized fault rules plus rules sharing a device or an
environmental domain with the violated specification. Candidate additions may be state,
mode, variable, or positive API-event conditions taken from the specification. For mode
and variable candidates with a declared enum or integer range, the policy supplies the
clause shape while an additional `FROZENVAR` supplies Salus §5.2's free value `Y`; the
selected concrete value is included in the signed suggestion and used by forward
verification and apply. State-tuple and positive API-event candidates retain the concrete
policy value because their persisted rule semantics are not a single scalar domain. Trust
and privacy conditions remain specification-only because the persisted rule language has
no corresponding trigger type.

Before the unrestricted lambda search, the strategy tries bounded deterministic
configurations. It first adds one policy-derived guard to a localized rule while retaining
every existing trigger, then tries removing one existing trigger while adding none. For
redundant rules issuing the same command, it also tries adding the same candidate-clause
shape to those rules together; this handles a dormant backup rule without asking NuSMV to
enumerate the full lambda product. Expanded-rule single additions remain available after
those higher-value probes. Each selected free guard may still solve over its declared `Y`
domain. Only after those configurations are unsatisfiable or fail complete-model forward
verification does the strategy search unrestricted joint add/remove combinations. This
prioritized phase receives at most half of `FIX_MAX_ATTEMPTS`; the remaining budget stays
available to joint search, and removal probes that would necessarily empty a one-condition
rule are not generated. As in parameter coordination, command equality includes target,
action, content device, and content value.

Free-value candidates are deduplicated by clause shape (resolved device/domain, target
type, attribute, and relation), not by the policy's placeholder literal. Search exclusions
are semantic: when a candidate lambda is `FALSE`, its unused `Y` value is omitted from the
excluded assignment, preventing the attempt budget from being spent on equivalent disabled
candidates. Command `EndState` and incompatible concrete `StartState` values are removed
from a free candidate's domain; one unsafe policy literal therefore does not discard other
valid values for the same clause shape.

The candidate filter rejects a positive condition that is already satisfied by the same rule
command's declared API `EndState` on the command target. That would be a postcondition
masquerading as a trigger (for example, `camera.state = taking_photo -> camera.take_photo`)
and can make the useful automation unreachable while still making a safety property pass. A
candidate on the command target is also rejected when it is provably false under every concrete
state allowed by the API `StartState`; wildcard start-state segments remain eligible instead of
being treated as contradictions. A rule with no meaningful condition adjustment is reported as
having no condition fix; the user should revise the property, adjust a genuine precondition, or
choose permanent rule removal.

Condition adjustment is not a hidden form of rule removal. It keeps the rule and its command and
must leave at least one valid trigger condition. Although an always-false trigger could resemble
removal at the level of one state transition, empty or synthetic trigger conditions are not a
valid persisted rule representation: the DTO rejects an empty condition list and SMV generation
fails closed for one. Permanent rule removal operates on the rule set itself, deletes the complete
automation, and therefore has a separate destructive confirmation and search strategy.

### Paper alignment boundaries

The implementation follows Salus §5 for fault-localized parameter/condition solving,
fixed-counterexample candidate discovery, exclusion of tried assignments, user-preferred
numeric ranges, and all-initial-state forward verification. It deliberately exposes one
verified suggestion per requested strategy and API call. Re-running parameter adjustment
with a different range can request a different solution, but the service does not persist
an exclusion history across calls to enumerate the next solution from the same strategy.

The UI can protect an individual numeric parameter by locking its range to the original
value. A general "do not modify this app rule" constraint is not currently part of the
fix request contract; users can avoid the destructive strategy, review the exact signed
condition edits before apply, or edit the rule manually. This is a product boundary rather
than a claimed implementation of the paper's full rule-protection control.

Forward verification proves only the submitted formal specifications. It does not infer an
unstated preference such as "retain this event trigger" or "do not broaden this automation."
When several equal-size condition edits satisfy the complete model, deterministic search order
may return any one of them; a formally verified edit can therefore still be undesirable under
an unmodeled user intent. Acceptance scenarios for condition adjustment must assert the concrete
edit, not merely `verified=true`, and users must review that signed edit before apply.

## Strategy 3 — permanent rule removal (`RemoveRulesFixStrategy`)

Destructive fallback. Finds a minimal set of rules to remove: for each candidate set, it
regenerates the model without those rules and re-verifies. Emits readable
`removedRuleDescriptions` so a user can review what will be permanently deleted;
internal rule positions are not part of the external contract. The product has no
persisted enabled/disabled rule state, so this action must never be described as
"disable" or imply that it can later be re-enabled. When the violated specification is
available, the candidate scope includes both localized rules and rules sharing a referenced
device or environment domain. This is necessary because a lower-priority automation may be
dormant in the selected trace and take over only after the executed rule is removed. With an
unresolved specification, removal retains its fault-only fallback. Under an exact attack
scenario, the strategy skips every removal set that would remove a selected automation-link
point or make a selected device cease to be behavior-changing. Request validation and every
fix candidate use the same exact-point-versus-attack-surface validator, so deleting the last
rule targeting a selected actuator cannot silently disable that actuator's attack variable.
The strategy compares the attempted count with the complete non-empty combination space;
reaching `FIX_MAX_ATTEMPTS` is reported as budget exhaustion only when combinations remain.

---

## Forward verification (`FixStrategyUtils.forwardVerify`)

Every candidate fix — a modified rule set — is turned back into an SMV model and
re-checked against **all** specs before it is accepted. Forward verification rejects
the candidate if generation disables any rule, skips any specification, emits a
different number of properties, parses a different number of results, or reports a
false property. This is why `FixSuggestionDto.verified=true` means the proposal passed
the complete generated model used by that fix attempt; it remains a model-level result,
not a guarantee about unmodelled physical behavior. The ordinary UI therefore presents
this state as **passed recomputation in the current complete formal model**, rather than
as an unqualified "verified solution".
For `EXACT_POINTS`, generation first recomputes the candidate rule set's attack surface
and rejects it unless every selected device remains behavior-changing and every selected
automation-link rule id still occurs exactly once.

---

## Result shape

`FixResultDto` = `{ traceId, violatedSpecId, faultRules: FaultRuleDto[],
suggestions: FixSuggestionDto[], strategyAttempts: FixStrategyAttemptDto[], fixable,
sourceModelComplete, sourceDisabledRuleCount, sourceSkippedSpecCount,
sourceGenerationIssues[], templateSnapshotComparison, summary, warnings[], parameterTargets[],
unusedPreferredRangeSelections[] }`.

`FixSuggestionDto` = `{ suggestionToken, strategy, description, parameterAdjustments[],
conditionAdjustments[], removedRuleDescriptions[], verified }`.

Each `strategyAttempts[]` item states whether that strategy found a verified proposal,
found none, failed to generate a complete candidate model, failed to complete reliable
NuSMV solving/result parsing, exhausted a bounded candidate search, or was skipped (timeout,
unsupported name, missing violated spec, no fault
rules, no parameterizable numeric value, or incomplete source model). Ordinary UI localizes limitations from those stable
statuses, source-model completeness fields, itemized generation-issue codes, and
`templateSnapshotComparison`. The English `summary` and `warnings` remain technical
diagnostics for the AI/tool or advanced-details layer. Full field tables are in
[../api/verification.md](../api/verification.md).

---

## Applying a suggestion (`FixStrategyApplier`)

`/fix` only *offers* verified suggestions; nothing is written to the board until the user
applies one (`POST /api/verify/traces/{id}/fix/apply`, handled by
`FixServiceImpl.applyFix`). Because a suggestion is computed against the trace's
verification-time snapshot, apply cannot trust that the board still matches — so it
**never trusts unsigned client data** and checks the exact signed proposal plus the current
model snapshot before persisting.

**The server signs the exact suggestion.** Every verified `/fix` proposal receives a short-lived
HMAC token bound to the authenticated user, trace, strategy, complete user-visible proposal,
preferred ranges, expiry, and all hidden operation locators (parameter and condition positions,
the internal device reference for condition additions, and remove-rule positions). Apply submits that displayed proposal
and token. Any edit, replay in another context, or expired token rejects with `400`; otherwise the
same proposal is applied. This removes the second expensive strategy search and prevents apply
from silently choosing a different valid suggestion than the one the user reviewed.

**Drift guards** (all reject with `400` unless noted) ensure the earlier verification evidence
still describes the model being changed:

- **Source-model completeness** — apply rejects traces whose verification disabled any
  rule or skipped any specification. The user must resolve generation warnings and
  verify again before asking the system to certify a repair.

- **Frozen-template replay and drift** — the trace stores the exact parsed manifests used
  by verification. `/fix` rebuilds from that saved set, never from whichever versions are
  current. Apply first compares current manifests with the saved
  set: a confirmed difference blocks with `400`; an unavailable repository comparison
  is reported as unknown and blocks with retryable `503`. `/fix` remains usable against
  the frozen model but adds an explicit warning for either confirmed drift or an
  unavailable comparison, so the degraded applicability is never silent.
  Apply-side `503` responses proven to occur before the write use the specialized mapping
  defined in the [API error mapping](../api/overview.md#error-and-status-codes); clients must not
  infer a no-write result from an unclassified proxy or infrastructure `503`.
- **Board-rule drift** — the server's internal rule/condition positions are relative to
  the snapshot; apply aligns snapshot and current rules by index + an **order-preserving**
  fingerprint and rejects if rules were added/removed/edited/reordered, so a stale index
  never edits the wrong rule.
- **Spec/device/environment drift** — a spec-, device-, or environment-pool-only edit
  touches neither rules nor templates. Apply compares a canonical
  **semantic fingerprint** (`BoardSemanticFingerprint`) of the trace snapshot against the
  current board — not raw-JSON equality: both sides run through the same normalization
  (device names canonicalized via `DeviceNameNormalizer`, effective variable/trust/privacy
  values derived from the same manifests NuSMV uses, values de-quoted) so an untouched board
  matches its model-boundary normalized snapshot instead of misfiring. Environment
  variables, including variables that are only affected by devices, are compared as the
  board-level pool; missing required pool values use the same default merge as
  verification. Omitted internal enum/numeric variables use the
  generator's effective defaults. If the current board no longer
  builds a valid model it fails **closed**, distinguishing a genuinely changed/invalid
  board (`400`, "re-run verification") from an infrastructure error that leaves drift
  unconfirmable (`503`, "retry later").

All final drift checks use one complete current semantic snapshot containing devices,
the Environment Pool, rules, specifications, and exact template manifests. That snapshot
is captured **inside the same per-user write lock + transaction** as the save (read →
check → apply → write is one atomic critical section), so the checks cannot themselves
mix different Board moments and a concurrent save cannot slip between a check and the
write.

**Per-strategy effect** (`FixStrategyApplier.apply`): `parameter` overwrites the target
condition's value (and relation); `condition` adds/removes conditions; `remove` permanently deletes
the flagged rules. Parameter and condition fixes regenerate each touched rule's
`ruleString` from the persisted typed conditions and command so board lists, history, AI
context, and scene export do not keep showing the pre-fix text. A `condition` fix that
would leave a rule with **no** trigger
conditions is rejected — and `ConditionAdjustStrategy` already excludes such solutions
during the search, since an empty-condition rule is fail-closed in NuSMV (never fires) and
so could otherwise verify yet be un-appliable (`RuleDto.conditions` is `@NotEmpty`).
Parameter and condition searches generate NuSMV-only FROZENVARs such as `param_r0_c0`
and `lambda_r0_c0`. These names are not user-facing reserved prefixes. During
parameterized model generation, `SmvMainModuleBuilder` checks them against the active
`MODULE main` namespace (device instances, generated `a_<environmentName>` variables,
the internal compromised-point counter, automation-link choices, and rule probes) and fails generation rather
than emitting a colliding model.

When applying a condition fix, model-boundary NuSMV `varName` references are translated back to
the raw `DeviceNode.id` from the current board snapshot before persistence. If a reference cannot
be mapped, the transaction fails closed and no rule is written; the internal model identifier is
not returned as a user-facing validation error.

The response (`FixApplyResultDto`) returns the signed `appliedSuggestion`,
`verificationRechecked=false`, `verificationEvidenceReused=true`, before/after rule counts,
and the full persisted rule list.
The localized UI derives its success explanation from these structured fields instead
of displaying the backend's English `message`; it states both the all-submitted-spec
scope and the unmodelled-real-world limitation.
Full request/response field tables and the exact `400`-vs-`503` semantics are in
[../api/verification.md](../api/verification.md).
