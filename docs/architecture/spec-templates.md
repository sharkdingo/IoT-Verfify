# Specification Templates & Validation

How a `SpecificationDto` becomes a CTL/LTL formula, and the P1–P5 model-validation
rules run before SMV generation.

Request field contract for specs → [../api/verification.md](../api/verification.md).
Modeling pipeline → [nusmv-model.md](nusmv-model.md).

Verified against code on 2026-07-04. Source:
`component/nusmv/generator/module/SmvSpecificationBuilder.java`,
`component/nusmv/generator/SmvModelValidator.java`.

---

## The seven templates

`SmvSpecificationBuilder` selects a CTL or LTL structure by `templateId`. Six are CTL;
`templateId = "6"` (Persistence) is the only LTL one. Each spec has three condition
groups — `aConditions` (A), `ifConditions` (IF), `thenConditions` (THEN).

### CTL templates (`templateId != "6"`)

| id | Name | Positive formula | Semantics |
| :--- | :--- | :--- | :--- |
| `1` | Always | `AG(A)`, or `AG((IF) -> (THEN))` when A is empty but IF/THEN are present | A holds globally; the implication form expresses an invariant without a separate template |
| `2` | Eventually | `AF(A)` | A eventually holds on all paths |
| `3` | Never | `AG !(A)` | A never holds on any path |
| `4` | Immediate | `AG((IF) -> AX(THEN))` | Right after IF, THEN holds in the next state |
| `5` | Response | `AG((IF) -> AF(THEN))` | After IF, THEN eventually holds on all paths |
| `7` | Safety | `AG !(body)` where `body` = A conditions + injected trust/attack terms | The condition must not hold in an untrusted state |

### LTL template (`templateId == "6"`)

| id | Name | Positive formula | Semantics |
| :--- | :--- | :--- | :--- |
| `6` | Persistence | `G((IF) -> F G(THEN))` | After IF, THEN eventually holds persistently |

### Counterexample search (negated forms)

To find a counterexample, the builder also emits the negation of each formula (this is
what actually runs). For reference, the negated forms in
`generateNegatedCtlSpec` / `generateNegatedLtlSpec`:

| id | Negated formula |
| :--- | :--- |
| `1` | `EF(!(A))`, or `EF((IF) & !(THEN))` for the implication form |
| `2` | `EG(!(A))` |
| `3` | `EF(A)` |
| `4` | `EF((IF) & EX(!(THEN)))` |
| `5` | `EF((IF) & EG(!(THEN)))` |
| `6` | `LTLSPEC F((IF) & G F(!(THEN)))` |
| `7` | `EF(body)` |

---

## Safety template (id 7) detail

`buildSafetySpec()` injects, for each A-condition, the matching trust term and (in
attack mode) an `is_attack` term:

```smv
-- input: aConditions = [{ deviceId: "fan_1", targetType: "state", key: "FanMode", value: "auto" }]
-- isAttack = true  →
CTLSPEC AG !(fan_1.FanMode=auto & fan_1.trust_FanMode_auto=untrusted & fan_1.is_attack=FALSE)
-- isAttack = false →  (no is_attack term — that variable is not declared)
CTLSPEC AG !(fan_1.FanMode=auto & fan_1.trust_FanMode_auto=untrusted)
```

The `is_attack=FALSE` term restricts the check to non-attacking devices' untrusted
states. For an environment-variable A-condition written as `a_varName OP value`, the
injected trust term uses `deviceVarName.trust_varName` (the `a_` prefix is dropped — it
does not generate a non-existent `trust_a_varName`).

---

## Condition → SMV expression

Each `SpecConditionDto` maps by `targetType`:

```
state    → deviceVarName.ModeName = stateName
variable → a_varName OP value            (environment var: key starts with "a_", or is in the device's envVariables)
         → deviceVarName.varName OP value (internal var: key is in the device's internalVariables)
         → otherwise → InvalidConditionException
api      → deviceVarName.apiName_a OP TRUE/FALSE   (only =, !=, IN, NOT_IN)
trust    → deviceVarName.trust_{key} OP value      (key resolved via resolvePropertyKey)
privacy  → deviceVarName.privacy_{key} OP value    (key resolved via resolvePropertyKey)
unknown  → InvalidConditionException  (fail-closed; no guessing)
```

Conditions in a group are joined with `&`. `IN` / `NOT_IN` take a comma-separated value
set. `deviceId` uses strict resolution (varName first, then a unique templateName);
ambiguity throws `AMBIGUOUS_DEVICE_REFERENCE` (not fail-closed).

### Fail-closed behavior

- If a condition cannot be built (unsupported relation, empty value, unresolvable key,
  unsupported targetType), the spec is **not** silently dropped — it degrades to
  `CTLSPEC FALSE -- invalid spec: <reason>`, keeping the spec count aligned.
- Privacy specs when `enablePrivacy = false` degrade to
  `CTLSPEC FALSE -- privacy spec skipped: enablePrivacy=false` (defense-in-depth;
  `validateNoPrivacySpecs` upstream is the primary guard).
- Specs with an unsupported `templateId` throw `InvalidConditionException` during
  generation and are recorded as `[spec-skipped]` warnings. Empty A/IF specs are also
  skipped explicitly. Both paths increment `skippedSpecCount` and surface in verification
  `checkLogs`; they are never treated as silently satisfied.
- `SpecificationDto.templateId` is also constrained at the DTO boundary to `"1"` through
  `"7"`; AI recommendation prompts and validators enforce the same enum before data reaches
  persistence or SMV generation.

### Attack budget and vacuity

The builder does **not** inject `& intensity<=N` into a spec's antecedent (that would
cause vacuous truth). The attack budget lives in `main` instead:

```smv
MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 3;
```

---

## Model validation — P1–P5

`SmvModelValidator` runs before SMV text is generated. Failures abort generation.

| Rule | Checks | On failure |
| :--- | :--- | :--- |
| P1 | `Trigger.Attribute` is in modes + internalVariables, and normalized `Trigger.Relation` is one of `=`/`!=`/`>`/`>=`/`<`/`<=` | `illegalTriggerAttribute` / `illegalTriggerRelation` |
| P2 | API/Transition `StartState`/`EndState` format & semantics: multi-mode → semicolon segment count equals mode count; single-mode → no semicolons; state values must be legal for their mode | `invalidStateFormat` |
| P3 | Same `(mode, stateName)` has consistent trust/privacy across WorkingStates | `trustPrivacyConflict` |
| P4 | trust values ∈ {`trusted`,`untrusted`}, privacy ∈ {`public`,`private`} (case-insensitive, normalized); applies to instance-, template-, and content-level | `SmvGenerationException` (`[INVALID_PROPERTY_VALUE]`) |
| P5 | A shared environment variable (`IsInside=false`) has consistent range/enum values across templates | `envVarConflict` |

### Soft validation (warn only, non-blocking)

- A user-supplied variable name not present in the template.
- A modeless sensor receiving a `state` argument.
- Internal-variable `init()` value checks
  (`SmvDeviceModuleBuilder.validateInternalInitValue()`): out-of-enum → first value;
  out-of-range → clamp; no enum/range → no `init()` emitted.
- Environment-variable `init()` value checks
  (`SmvMainModuleBuilder.validateEnvVarInitValue()`): out-of-enum → first value;
  out-of-range → clamp (attack mode uses the expanded upper bound); non-numeric →
  ignored.

### Generation-time fail-closed (not part of P1–P5)

- Rule-condition parse failure (missing device, empty/unknown attribute, unsupported
  relation, empty value, empty `IN`/`NOT_IN` list, illegal API-signal relation/value)
  → the rule guard becomes `FALSE`, a `[rule-disabled]` warning is emitted, and
  `disabledRuleCount` increments.
- Ambiguous templateName reference in a rule/command/spec device → throws
  `AMBIGUOUS_DEVICE_REFERENCE` (does not fail-closed).
- Transition triggers referencing an environment variable are rewritten to `a_<attr>`
  (not `device.<attr>`) during generation, avoiding references to undeclared internal
  variables.

---

## Logic-integrity checklist

_Migrated from the former `NuSMV_Module_Documentation.md` §12._

The following chains are closed loops in the current backend implementation:

1. **Input-constraint loop**: DTO validation
   (`@NotNull/@NotEmpty/@Pattern/@Min/@Max/@Size`) plus generation-time fail-closed
   behavior (rule/spec condition parse failures are never silently passed). `@NotEmpty`
   replaces `@NotNull` on the device list (rejects empty lists), `@Size(max=10000)` bounds
   chat content, and `@NotNull` covers every `@RequestBody` in `BoardStorageController`.
2. **Template loop**: catalog templates (in resources) are seeded into the DB first, then
   read at runtime by `userId + templateName`. If a template is missing, `loadManifest()`
   returns `null`; the caller `buildDeviceSmvMap()` collects all missing devices and
   ultimately throws `SmvGenerationException.multipleDevicesFailed()`. Custom-template
   creation runs a NuSMV probe-generate pre-check: InternalVariable/ImpactedVariable names
   must be legal identifiers and not reserved words; mode/state names are sanitized
   automatically at generation time; normalized identifiers of different kinds must not
   collide (Mode vs InternalVariable vs ImpactedVariable), though InternalVariable and
   ImpactedVariable may share a name (a common pattern). `loadManifest()` classifies
   exceptions precisely: `BaseException` is re-thrown as-is, a JSON parse error →
   `MANIFEST_PARSE_ERROR`, and anything else → `TEMPLATE_LOAD_ERROR`.
3. **Modeling loop**: `DeviceSmvDataFactory` → `SmvModelValidator (P1–P5)` →
   `SmvDevice/Main/SpecificationBuilder` produce a complete `model.smv`. Mode/state names
   are sanitized centrally via `sanitizeSmvToken()` (spaces / illegal characters / leading
   digit / case-insensitive reserved-word escaping); InternalVariable/ImpactedVariable
   names are **not** sanitized at generation time (they are cross-referenced in many
   places, and partial sanitization would break `.equals()` matching) — instead illegal
   values are strictly rejected at persistence time. `toVarName()` provides parallel
   defense for device IDs; `computeIdentifiers()` applies leading-digit guarding and
   reserved-word escaping to `varName`, the module-name prefix (base, from templateName),
   and the module-name suffix. Trust/privacy land via a three-layer loop of "entry
   normalization + validation + re-normalization at emit".
4. **Execution loop**: `NusmvExecutor` supports batch verification and interactive
   simulation, with timeout (configured centrally by `NusmvConfig.timeoutMs`, `@Min(100)`
   startup validation, overridable via the YAML `${NUSMV_TIMEOUT_MS:120000}` environment
   variable), a concurrency gate, busy returns, and stdout/stderr handling.
5. **Result loop (verification)**: per-spec result parsing, counterexample parsing, trace
   persistence, task status and progress (progress persisted to the DB with a three-tier
   fallback chain: memory → DB column → terminal-state inference), and unified sync/async
   error semantics.
6. **Result loop (simulation)**: trace parsing, `steps` vs `requestedSteps` reconciliation
   (`steps = states.size() - 1`, which may be less than `requestedSteps`), optional
   persistence, and async task lifecycle management. Cross-instance cancel safety:
   `completeTask`/`failTask` use atomic conditional UPDATEs (`WHERE status <> CANCELLED`)
   to eliminate TOCTOU races, returning the affected-row count (0 = already cancelled).
7. **Observability loop**: `model.smv` / `request.json` / `output.txt` / `result.json`
   (the main verification and simulation paths) are available for replay and debugging;
   the cancel early-exit path must be diagnosed together with the task status.
8. **Numeric-bounds loop**: `next()` candidate expressions for both environment and
   internal variables uniformly clamp with `max(lower, min(upper, expr))`, covering the
   boundary branches (WITH-rate / no-rate) and the TRUE branch, preventing arithmetic
   results from exceeding the NuSMV VAR declared range. Under attack mode, the upper-bound
   expansion formula is centralized in `SmvBoundsUtils.resolveEffectiveUpperBound()`,
   shared by `SmvDeviceModuleBuilder` (VAR declaration) and `SmvMainModuleBuilder`
   (transition clamp range), so the declared range and the transition clamp range stay
   consistent.
9. **Fix loop (Fix Pipeline)**: `FixServiceImpl` → `RuleFixer` → three strategies
   (parameter/condition/disable) chained. A global soft timeout is controlled by
   `FixConfig.fixTimeoutMs` (default 300s, `@Min(1000)`); `FixContext.isExpired()` checks
   the deadline at the strategy-loop entry, the `forwardVerify()` entry, and inside each
   strategy loop; after timeout the summary appends "(fix timed out; results may be
   partial)". Template-drift detection: `DeviceTemplatePo.updatedAt`
   (`@PrePersist`/`@PreUpdate`) is compared against `trace.createdAt`, and on drift the
   summary appends a WARNING. Known limitation: soft timeout — after the deadline, at most
   one in-flight NuSMV call may still run (bounded by `nusmv.timeout-ms`).

Runtime prerequisites still required:

- MySQL, Redis, JWT, LLM, CORS, thread-pool, and NuSMV runtime settings are centralized in
  [../getting-started/configuration.md](../getting-started/configuration.md), including the
  production startup guards.
- The current user's templates are initialized and consistent with the `templateName` in
  the frontend request.
- The `device_templates` table gains a `(user_id, name)` unique constraint; confirm there
  is no duplicate data before the first deployment.
