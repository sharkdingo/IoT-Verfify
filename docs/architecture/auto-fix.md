# Automatic Fix

When verification finds a violation, the fix system localizes the responsible rules and
tries, in order, three repair strategies — each candidate re-verified against all specs
before being offered.

API contract (`fault-rules`, `fix`) → [../api/verification.md](../api/verification.md).
Spec formulas → [spec-templates.md](spec-templates.md).

Verified against code on 2026-07-03. Source: `component/nusmv/fixer/` — `RuleFixer`,
`localize/FaultLocalizer`, `strategy/{ParameterAdjustStrategy, ConditionAdjustStrategy,
DisableFixStrategy, FixStrategyUtils}`, `parameterize/ParameterExtractor`. Config keys
(`FIX_*`) → [../getting-started/configuration.md](../getting-started/configuration.md).

---

## Pipeline (`RuleFixer`)

1. **Fault localization** (`FaultLocalizer.localize`): identify which rules were
   triggered in the counterexample trace (a fast pass, no NuSMV invocation). This also
   backs `GET /api/verify/traces/{id}/fault-rules`.
2. **Strategy attempts**: run the requested strategies in order. The default order,
   following the Salus paper §5, is `parameter → condition → disable`. A caller may
   override the list and order via `FixRequestDto.strategies`.
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
