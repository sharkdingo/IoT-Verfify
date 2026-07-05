# Automatic Fix

When verification finds a violation, the fix system localizes the responsible rules and
tries, in order, three repair strategies — each candidate re-verified against all specs
before being offered.

A suggestion is only advisory until the user chooses to **apply** it; applying writes the
repaired rules back to the board (see [Applying a suggestion](#applying-a-suggestion-fixstrategyapplier)).

API contract (`fault-rules`, `fix`, `fix/apply`) → [../api/verification.md](../api/verification.md).
Spec formulas → [spec-templates.md](spec-templates.md).

Verified against code on 2026-07-05. Source: `component/nusmv/fixer/` — `RuleFixer`,
`localize/FaultLocalizer`, `strategy/{ParameterAdjustStrategy, ConditionAdjustStrategy,
DisableFixStrategy, FixStrategyUtils, FixStrategyApplier}`, `BoardSemanticFingerprint`,
`parameterize/ParameterExtractor`; `service/impl/FixServiceImpl` (apply flow). Config keys
(`FIX_*`) → [../getting-started/configuration.md](../getting-started/configuration.md).

---

## Pipeline (`RuleFixer`)

1. **Fault localization** (`FaultLocalizer.localize`): identify which rules were
   triggered in the counterexample trace (a fast pass, no NuSMV invocation). This also
   backs `GET /api/verify/traces/{id}/fault-rules`.
2. **Strategy attempts**: run the requested strategies in order. The default order is
   `parameter → condition → disable`: the first two implement Salus §5.1/§5.2, while
   `disable` is an IoT-Verify fallback. A caller may override the list and order via
   `FixRequestDto.strategies`.
3. Each strategy produces at most one **verified** `FixSuggestionDto` (see forward
   verification below). Results accumulate into `FixResultDto`.

A soft deadline (`FIX_TIMEOUT_MS`, default 300000) bounds the whole pipeline; if it
expires before a strategy runs, remaining strategies are skipped and noted in the
`summary`. Strategies that need spec negation (`parameter`, `condition`) are skipped if
no valid `violatedSpecIndex` is available; `disable` does not require it
(`FixStrategy.requiresViolatedSpec()`).

---

## Strategy 1 — parameter adjustment (`ParameterAdjustStrategy`)

Turns a rule's numeric threshold conditions into `FROZENVAR` parameters, then uses
NuSMV to solve `¬ρ` (the negated spec) for corrected values, refining toward the value
closest to the original.

- `ParameterExtractor` finds parameterizable numeric conditions.
- Candidate values are searched within an optional caller-supplied `PreferredRange`
  (`{ lower, upper }`, keyed `r{ruleIdx}_c{condIdx}`, e.g. `r0_c1`); keys that match no
  parameterizable condition are reported back in
  `FixResultDto.unusedPreferredRangeKeys`.
- Bounded by `FIX_MAX_ATTEMPTS` (NuSMV calls per strategy), `FIX_MAX_REFINE_ATTEMPTS`
  (refinement iterations), and `FIX_MAX_CANDIDATES_PER_RULE`.
- Emits `ParameterAdjustment` entries: `{ ruleIndex, conditionIndex, attribute,
  relation, originalValue, newValue, lowerBound, upperBound }`.
- Witness extraction is covered by a real NuSMV 2.7.1 smoke test on minimal false
  EF/EG CTL models. CI must install NuSMV 2.7.1 for this check; local runs without
  NuSMV skip the smoke test. This confirms the core `FROZENVAR` output behavior for
  that version and environment, but it is not an exhaustive proof for every generated
  template shape.

## Strategy 2 — condition adjustment (`ConditionAdjustStrategy`)

Adds a boolean lambda guard to a rule and uses NuSMV to decide which conditions must be
adjusted. Emits `ConditionAdjustment` entries: `{ ruleIndex, conditionIndex, action,
attribute, description, deviceName, relation, value }`.

## Strategy 3 — rule disabling (`DisableFixStrategy`)

Fallback. Finds a minimal set of rules to disable: for each candidate set, it
regenerates the model without those rules and re-verifies. Emits
`disabledRuleIndices` (the rule indices to disable).

---

## Forward verification (`FixStrategyUtils.forwardVerify`)

Every candidate fix — a modified rule set — is turned back into an SMV model and
re-checked against **all** specs before it is accepted. A candidate that does not make
every spec pass is discarded and the strategy moves on. This is why a
`FixSuggestionDto` carries `verified = true`: it is not a guess, it has been model-checked.

---

## Result shape

`FixResultDto` = `{ traceId, violatedSpecId, faultRules: FaultRuleDto[],
suggestions: FixSuggestionDto[], fixable, summary, unusedPreferredRangeKeys[] }`.

`FixSuggestionDto` = `{ strategy, description, parameterAdjustments[],
conditionAdjustments[], disabledRuleIndices[], verified }`.

The `summary` string carries human-readable notes, including timeout or
value-drift warnings and (when localization cannot resolve the violated spec) a note
that the parameter/condition strategies were skipped. Full field tables are in
[../api/verification.md](../api/verification.md).

---

## Applying a suggestion (`FixStrategyApplier`)

`/fix` only *offers* verified suggestions; nothing is written to the board until the user
applies one (`POST /api/verify/traces/{id}/fix/apply`, handled by
`FixServiceImpl.applyFix`). Because a suggestion is computed against the trace's
verification-time snapshot, apply cannot trust that the board still matches — so it
**never trusts the client** and re-derives everything server-side before persisting.

**The server recomputes, it does not replay the client's suggestion.** The client sends
back the exact suggestion it displayed (WYSIWYG) plus the same `preferredRanges` `/fix`
used. Apply re-runs the requested strategy against the trace's own context and requires
the submitted suggestion to match that freshly recomputed, NuSMV-verified result (by the
operations it encodes). The client's `verified` flag is ignored; if the server cannot
reproduce a verified suggestion, or the submitted one differs, apply rejects with `400`.
It then applies its *own* recomputed suggestion to a deep copy of the persisted rules, so
what is saved is exactly what NuSMV just verified.

**Drift guards** (all reject with `400` unless noted) run because the recompute replays
the trace's *stored* context and would otherwise re-prove the same fix against a stale
model or write it onto a changed board:

- **Template drift** — apply rebuilds the device model from the **current** templates; if
  a template used by the trace changed, apply blocks with `400` (`/fix` only warns).
  Checked before the expensive recompute. Fails **closed**: if the template repo errors
  so drift cannot be confirmed, the unverifiable check is treated as drift and apply
  rejects with `400` ("re-run verification") rather than proceeding.
- **Board-rule drift** — the suggestion's `ruleIndex`/`conditionIndex` are relative to
  the snapshot; apply aligns snapshot and current rules by index + an **order-preserving**
  fingerprint and rejects if rules were added/removed/edited/reordered, so a stale index
  never edits the wrong rule.
- **Spec/device drift** — a spec- or device-only edit touches neither rules nor
  templates, so the recompute alone would miss it. Apply compares a canonical
  **semantic fingerprint** (`BoardSemanticFingerprint`) of the trace snapshot against the
  current board — not raw-JSON equality: both sides run through the same normalization
  (device names canonicalized via `DeviceNameNormalizer`, empty variable/privacy lists
  manifest-defaulted, values de-quoted) so an untouched board matches its
  frontend-transformed snapshot instead of misfiring. If the current board no longer
  builds a valid model it fails **closed**, distinguishing a genuinely changed/invalid
  board (`400`, "re-run verification") from an infrastructure error that leaves drift
  unconfirmable (`503`, "retry later").
- **Strategy mismatch** — `strategy` ≠ `suggestion.strategy` is rejected.

The board-rule and spec/device checks run **inside the same per-user write lock +
transaction** as the save (read → check → apply → write is one atomic critical section),
so a concurrent save cannot slip in between the check and the write.

**Per-strategy effect** (`FixStrategyApplier.apply`): `parameter` overwrites the target
condition's value (and relation); `condition` adds/removes conditions; `disable` deletes
the flagged rules. A `condition` fix that would leave a rule with **no** trigger
conditions is rejected — and `ConditionAdjustStrategy` already excludes such solutions
during the search, since an empty-condition rule is fail-closed in NuSMV (never fires) and
so could otherwise verify yet be un-appliable (`RuleDto.conditions` is `@NotEmpty`).

The response (`FixApplyResultDto`) returns the full persisted rule list after applying.
Full request/response field tables and the exact `400`-vs-`503` semantics are in
[../api/verification.md](../api/verification.md).
