# NuSMV Model Generation

How a verification request becomes a `.smv` model that NuSMV can check. This document
owns the **modeling logic**: the generation pipeline, identifier handling, and how
user input maps onto SMV constructs.

Scope boundaries:
- Request/response **field contracts** → [../api/verification.md](../api/verification.md).
- **Spec templates ↔ CTL/LTL** and the **P1–P5 validation rules** →
  [spec-templates.md](spec-templates.md).
- **Auto-fix** algorithm → [auto-fix.md](auto-fix.md).

> **NuSMV version**: NuSMV 2.6–2.7 only. Output parsing depends on NuSMV's standard
> English output (`-- specification ... is true/false`, `Trace Type`, `NuSMV >`
> prompt). nuXmv and other variants are not supported.

Verified against code on 2026-07-03. Source:
`component/nusmv/generator/`.

---

## Generation pipeline

`SmvGenerator.generate(...)` orchestrates the following, producing a `model.smv`
file (with `request.json` written alongside for post-mortem debugging):

| Step | Class | Role |
| :--- | :--- | :--- |
| 1 | `DeviceSmvDataFactory.buildDeviceSmvMap()` | User input + template → `DeviceSmvData` |
| 2 | `SmvModelValidator.validate()` | P1–P5 pre-generation validation (see spec-templates.md) |
| 3 | `SmvRuleCommentWriter.build()` | Rules → SMV comments |
| 4 | `SmvDeviceModuleBuilder.build()` | Each device → a `MODULE` definition |
| 5 | `SmvMainModuleBuilder.build()` | `main MODULE` + `ASSIGN` block |
| 6 | `SmvSpecificationBuilder.build()` | Specs → `CTLSPEC` / `LTLSPEC` |

The generated model is then handed to `NusmvExecutor` (semaphore-bounded process
execution, timeout protection) and the output to `SmvTraceParser`. That end-to-end
flow is documented in [verification-flow.md](verification-flow.md).

Supporting utilities in the same package: `SmvBoundsUtils` (numeric bounds),
`SmvRelationUtils` (relation normalization), `PropertyDimension` (trust/privacy
dimension modeling).

---

## Template resolution (important)

- At runtime, templates come from the **current user's template table (DB)**, not
  directly from `resources/deviceTemplate`.
- Default templates are seeded from `resources/deviceTemplate/*.json` into the DB
  (auto-imported on registration). `POST /api/board/templates/reload` is a **reset**:
  it deletes the user's existing templates, then re-imports defaults.
- If a request's `templateName` does not exist in the current user's templates, SMV
  generation fails with `SmvGenerationException`.
- Device references in rules/specs resolve by `varName` first; a `templateName`
  fallback is allowed only when it matches a **unique** instance — multiple matches
  raise `AMBIGUOUS_DEVICE_REFERENCE`.

---

## Identifier handling

Two different mechanisms apply to two different classes of identifier. This split is
deliberate — see the rationale below.

### Sanitized at generation time — `sanitizeSmvToken()`

Applies to **mode names and state names**
(`DeviceSmvDataFactory.sanitizeSmvToken()`). Transformations:

1. Remove spaces.
2. Replace non-alphanumeric characters with `_`.
3. Prefix a leading digit with `_`.
4. Escape NuSMV reserved words case-insensitively (including `W`).

Device IDs get a parallel defense via `toVarName()`.

After normalization, identifiers of different kinds (Mode vs InternalVariable vs
ImpactedVariable) must not collide. InternalVariable and ImpactedVariable **are**
allowed to share a name (a common pattern: a device's internal variable drives an
identically named environment variable).

### Rejected at persistence time — `validateTemplateManifestForNuSmv()`

Applies to **InternalVariable and ImpactedVariable names**. These are **not**
sanitized at generation time, because they are cross-referenced in many places and
partial sanitization would break `.equals()` matching. Instead they must be legal
NuSMV identifiers (`[a-zA-Z_][a-zA-Z0-9_]*`) and not reserved words, and this is
enforced strictly when a template is saved
(`BoardStorageServiceImpl.validateTemplateManifestForNuSmv()`). Illegal values are
rejected at insert time (probe-generate pre-check on custom template creation returns
400/500).

---

## Attack and privacy dimensions

Two optional modeling dimensions, both off by default (they enlarge the state space):

- **Attack mode** (`isAttack`, `intensity`): generates an `is_attack` frozen variable
  and expands sensor value ranges. `intensity` (0–50) constrains the global attack
  budget via `INVAR intensity <= N` and scales range expansion; `intensity = 0`
  forces all `is_attack` to FALSE.
- **Privacy** (`enablePrivacy`): generates `privacy_*` variables for states,
  variables, and content. Recommended only when specs contain privacy conditions.

---

## SMV file structure

_Migrated from the former `NuSMV_Module_Documentation.md` §4._

A complete SMV file is composed of the following parts:

```smv
-- Rule comments (SmvRuleCommentWriter)
--IF thermostat_1.temperature>30 THEN fan_1.fanAuto

-- Device module definitions (SmvDeviceModuleBuilder) — one per device template
MODULE Thermostat_thermostat1
  FROZENVAR                          -- frozen variables (constant during verification)
    is_attack: boolean;              -- generated only when isAttack=true
  VAR                                -- state variables
    ThermostatMode: {cool, heat, off};         -- mode state
    temperature: 15..35;                        -- external variable (mapped from main's a_temperature)
    setCool_a: boolean;                         -- API signal
    trust_ThermostatMode_cool: {untrusted, trusted};  -- state trust
    trust_temperature: {untrusted, trusted};          -- variable trust
    privacy_ThermostatMode_cool: {private, public};   -- only when enablePrivacy
    privacy_temperature: {private, public};           -- variable privacy
  ASSIGN
    init(ThermostatMode) := cool;    -- initial state
    init(setCool_a) := FALSE;
    init(trust_ThermostatMode_cool) := trusted;
    init(trust_temperature) := trusted;
    init(privacy_ThermostatMode_cool) := public;
    init(privacy_temperature) := public;

-- Main module (SmvMainModuleBuilder)
MODULE main
  FROZENVAR
    intensity: 0..50;                -- generated only when isAttack=true
  INVAR intensity <= 3;              -- global attack-budget constraint
  VAR
    thermostat_1: Thermostat_thermostat1;      -- device instantiation
    fan_1: Fan_fan1;
    a_temperature: 15..35;              -- environment variable (a_ prefix)
  ASSIGN
    -- state transitions (attack hijack takes priority, then template Transitions)
    next(thermostat_1.ThermostatMode) := case
      thermostat_1.is_attack=TRUE: {cool, heat, off};
      thermostat_1.ThermostatMode = cool & thermostat_1.temperature > 30 & thermostat_1.is_attack=FALSE : heat;
      TRUE : thermostat_1.ThermostatMode;      -- default: self-hold
    esac;
    -- API signal (based on state-change detection)
    next(fan_1.fanAuto_a) := case
      fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
      TRUE: FALSE;
    esac;
    -- trust propagation (PropertyDimension.TRUST)
    next(fan_1.trust_FanMode_auto) := case
      fan_1.is_attack=TRUE: untrusted;
      thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
      thermostat_1.temperature > 30: untrusted;
      TRUE: fan_1.trust_FanMode_auto;         -- self-hold
    esac;

-- Specifications (SmvSpecificationBuilder)
  CTLSPEC AG(thermostat_1.ThermostatMode != off)
  CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.trust_FanMode_auto = untrusted))
  LTLSPEC G((thermostat_1.temperature > 25) -> F G(fan_1.FanMode = auto))
```

### NuSMV syntax cheat-sheet

| Syntax | Meaning | Example |
| :--- | :--- | :--- |
| `MODULE name` | Module definition | `MODULE Thermostat_t1` |
| `FROZENVAR` | Frozen variable (constant after init) | `is_attack: boolean;` |
| `VAR` | State variable | `mode: {on, off};` |
| `ASSIGN` | Assignment block | `init(x) := 0; next(x) := ...` |
| `init(v) := expr` | Initial value | `init(mode) := off;` |
| `next(v) := case ... esac` | State transition | see example above |
| `CTLSPEC` | CTL temporal-logic spec | `CTLSPEC AG(p)` |
| `LTLSPEC` | LTL temporal-logic spec | `LTLSPEC G(p -> F q)` |
| `AG(p)` | Holds globally on all paths | safety property |
| `EF(p)` | Eventually holds on some path | reachability property |
| `G(p -> F q)` | Globally: p implies eventually q | liveness property |

---

## How user input maps to the model

_Migrated from the former `NuSMV_Module_Documentation.md` §5._

### isAttack (attack mode)

When `isAttack=true`, the SMV model changes as follows.

Device module (`SmvDeviceModuleBuilder`):

```smv
FROZENVAR
    is_attack: boolean;    -- a frozen attack flag added per device
```

Main module (`SmvMainModuleBuilder`):

```smv
FROZENVAR
    intensity: 0..50;      -- global attack-budget variable
INVAR intensity <= 3;      -- global budget constraint (example N=3)

-- environment-variable ranges expand in proportion to intensity (upper bound only)
-- the formula is centralized in SmvBoundsUtils.resolveEffectiveUpperBound()
-- expansion = (upper-lower)/5 * intensity/50
-- e.g. temperature originally 15..35 becomes 15..39 when intensity=50
VAR
    a_temperature: 15..39;
```

Specification (`SmvSpecificationBuilder`):

```smv
-- current behavior: specs no longer auto-inject intensity<=N
-- the budget constraint lives solely in main's INVAR
CTLSPEC AG(!(fan.state = auto & fan.trust_FanMode_auto = untrusted))
```

### intensity (attack strength)

`intensity` (0–50) has two roles in the current implementation:

1. **Global budget constraint**: generates `INVAR intensity <= N` in the `main` module.
2. **Range-expansion ratio**: under attack mode, scales the expansion by `intensity/50`.

```smv
-- example: range = upper - lower = 20
-- intensity = 0   => expansion = 0
-- intensity = 25  => expansion = 2
-- intensity = 50  => expansion = 4
```

### enablePrivacy (privacy dimension)

When `enablePrivacy=true`:

Device module — sensor variable privacy:

```smv
FROZENVAR
    privacy_temperature: {public, private};   -- per sensor variable
```

Device module — state privacy:

```smv
VAR
    privacy_ThermostatMode_cool: {private, public};   -- per (mode, state) combination
```

Device module — content privacy:

```smv
-- content with IsChangeable=false → FROZENVAR (privacy immutable)
FROZENVAR
    privacy_photo: {public, private};

-- content with IsChangeable=true → VAR (privacy mutable)
VAR
    privacy_photo: {public, private};
```

Main module — privacy propagation rules:

```smv
-- when a rule fires, privacy propagates from source device to target device
-- the guard uses the full rule condition (appendRuleConditions), not the simplified API signal
-- e.g. rule "IF condition THEN camera.takePhoto(MobilePhone.photo)"
next(camera_1.privacy_photo) := case
    <rule conditions>: private;              -- set to private when the rule fires
    TRUE : camera_1.privacy_photo;           -- self-hold
esac;
```

**Note:** when `enablePrivacy=false`, if the specs contain a condition with
`targetType="privacy"`, the upstream `SmvGenerator.validateNoPrivacySpecs()` throws
`SmvGenerationException` (the primary guard). As defense-in-depth, when
`enablePrivacy=false` the `SmvSpecificationBuilder` also skips any spec with a privacy
condition and emits a `CTLSPEC FALSE -- privacy spec skipped: enablePrivacy=false`
placeholder.

### devices (device instances)

| User input field | SMV effect |
| :--- | :--- |
| `varName` | Determines the SMV instance variable name (e.g. `thermostat_1`) and the module-name suffix |
| `templateName` | Loads the DeviceManifest from the DB — defines the full set of modes/states/variables/transitions |
| `state` | Determines the initial value of `init(ModeVar)` |
| `currentStateTrust` | Overrides the template default state-trust initial value |
| `variables[].value` | Determines the initial value of `init(varName)` |
| `variables[].trust` | Overrides the variable-trust initial value |
| `privacies[].privacy` | Overrides the privacy initial value (only effective when enablePrivacy=true) |

Environment-variable initial values (`IsInside=false`):

- A shared environment variable is declared only once in `main` (`a_varName`); its
  `init(a_varName)` is aggregated across devices' user input via
  `resolveEnvVarInitValues()` (each device's initial value is first range/enum-checked by
  `validateEnvVarInitValue()`).
- If multiple devices give conflicting initial values for the same environment variable
  (inconsistent after validation/normalization), `resolveEnvVarInitValues()` throws
  `envVarConflict`.
- For an environment variable with no enum and no declared bounds, `main` declares it as
  `0..100` by default; user initial values accept integers only, out-of-range values are
  clamped to `0`/`100`, and non-numeric values are ignored.

Internal-variable initial values (`IsInside=true`):

- `SmvDeviceModuleBuilder.validateInternalInitValue()` checks the user-supplied `init()`
  value: enum variables check membership (fall back to the first value with a warning if
  out of enum); numeric variables check the `[lower..upper]` range (clamp with a warning
  if out of range); a variable with neither enum nor range gets no `init()`, preserving
  NuSMV's non-deterministic initialization.

### rules (IFTTT rules)

Rules manifest in SMV as several groups of `next()` assignments:

```
user rule: IF thermostat_1.temperature > 30 THEN fan_1.fanAuto
```

Generated SMV (assuming the fanAuto API has startState=off, endState=auto, signal=true;
the example below assumes `isAttack=false` — under attack mode an extra
`& fan_1.is_attack=FALSE` term is appended):

```smv
-- 1. state transition (driven directly by the rule condition; the API's EndState determines the target state)
--    guard = rule condition + API startState constraint
next(fan_1.FanMode) := case
    thermostat_1.temperature > 30 & fan_1.FanMode=off : auto;
    TRUE : fan_1.FanMode;
esac;

-- 2. API signal (based on state-change detection, not driven directly by the rule condition)
--    with startState:    guard = current state=startState & next(state)=endState
--    without startState: guard = current state!=endState & next(state)=endState
next(fan_1.fanAuto_a) := case
    fan_1.FanMode=off & next(fan_1.FanMode)=auto: TRUE;     -- startState=off
    TRUE: FALSE;
esac;

-- 3. trust propagation (TRUST dimension)
--    guard = rule condition & all source variables' trust are trusted (AND semantics)
--    under attack mode, an extra is_attack=TRUE → untrusted priority branch is added
next(fan_1.trust_FanMode_auto) := case
    fan_1.is_attack=TRUE: untrusted;                          -- only when isAttack=true
    thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
    thermostat_1.temperature > 30: untrusted;                 -- condition met but source untrusted
    TRUE: fan_1.trust_FanMode_auto;                           -- self-hold
esac;

-- 4. privacy propagation (only when enablePrivacy=true, PRIVACY dimension)
--    guard = rule condition & all source variables' privacy are private
next(fan_1.privacy_FanMode_auto) := case
    thermostat_1.temperature > 30 & (thermostat_1.privacy_temperature=private): private;
    TRUE: fan_1.privacy_FanMode_auto;                         -- self-hold
esac;
```

Note: trust propagation generates two lines — set to `trusted` when the condition holds
and the source is trusted, set to `untrusted` when the condition holds but the source is
untrusted. Privacy propagation generates only one line (set to `private` when the
condition holds and the source is private).

**Rule-condition parse failure (fail-closed):** when one of a rule's IF conditions cannot
be parsed (e.g. the device does not exist, `attribute` is empty, with `relation!=null` the
attribute matches no mode/internal variable/API signal, the relation is unsupported, the
relation is non-null but the value is empty, the `IN/NOT_IN` value list is empty, or an API
signal's relation/value is invalid), `appendRuleConditions` sets the whole rule's guard to
`FALSE`, so the rule never fires. This is a fail-closed policy — better that a rule not
fire than that an invalid condition be silently ignored and turn the rule into an
unconditional trigger. A warn-level log records the failure reason.

**`useNext` recursion avoidance (key to state modeling):** when building a rule guard for
`next(target.mode)`, if the condition references the same target device, the generator
rewrites it to read the current state (`effectiveUseNext=false`), avoiding a
`next(x)`-depends-on-`next(x)` recursive definition (NuSMV `recursively defined` error).

### `SmvMainModuleBuilder` transition types

The `ASSIGN` block of `MODULE main` generates the various `next()` transitions in this
order:

| # | Method | Generates | Notes |
| :--- | :--- | :--- | :--- |
| 1 | `appendStateTransitions()` | `next(device.ModeVar)` | Rule-driven state transitions + template-Transition-driven state transitions. In attack mode, non-sensor devices get a highest-priority branch `is_attack=TRUE: {all legal states}` — the actuator is hijacked |
| 2 | `appendEnvTransitions()` | `next(a_varName)` | `next()` for environment variables, including NaturalChangeRate, device impact rate, boundary checks. A Transition trigger referencing an environment variable uses `a_<attr>` (checks only the current device's env var, avoiding cross-device same-name collisions) |
| 3 | `appendApiSignalTransitions()` | `next(device.apiName_a)` | API signal variables, based on state-change detection (`current!=end & next(mode)=end`) |
| 4 | `appendTransitionSignalTransitions()` | `next(device.transName_t)` | Template Transition signal variables, based on state-change detection |
| 5 | `appendPropertyTransitions()` (TRUST) | `next(device.trust_Mode_State)` | State-level trust propagation (includes the is_attack priority branch) |
| 6 | `appendPropertyTransitions()` (PRIVACY) | `next(device.privacy_Mode_State)` | State-level privacy propagation (only when enablePrivacy=true) |
| 7 | `appendVariablePropertyTransitions()` (TRUST) | `next(device.trust_varName)` | Variable-level trust self-hold (an actuator's VAR variables must have a next) |
| 8 | `appendVariablePropertyTransitions()` (PRIVACY) | `next(device.privacy_varName)` | Variable-level privacy self-hold (only when enablePrivacy=true) |
| 9 | `appendContentPrivacyTransitions()` | `next(device.privacy_contentName)` | Privacy transition for content with IsChangeable=true: when a rule command references the content (e.g. `THEN Facebook.post(MobilePhone.photo)`), the rule firing sets the content privacy to `private`; otherwise self-hold |
| 10 | `appendVariableRateTransitions()` | `next(device.varName_rate)` | Change rate for affected variables, determined by the device's WorkingState.Dynamics. The `_rate` range is computed dynamically from the actual ChangeRate values in the template (fallback `-10..10` when there is no Dynamics) |
| 11 | `appendExternalVariableAssignments()` | `device.varName := a_varName` | External variables (IsInside=false) mirror the environment variable (a plain assignment, not next). Note: in code this method is called after `appendVariableRateTransitions` |
| 12 | `appendInternalVariableTransitions()` | `next(device.varName)` | `next()` for internal variables (IsInside=true); in attack mode generates an `is_attack=TRUE: lower..upper` branch (upper bound expanded via `SmvBoundsUtils.resolveEffectiveUpperBound()`). Transition trigger references also use the current device's env var check |

Environment-variable `next()` transition example (numeric, with device impact rate):

```smv
next(a_temperature) :=
case
    -- when there is a device impact rate (e.g. airconditioner.temperature_rate)
    a_temperature=35-(airconditioner.temperature_rate): {max(15, min(35, toint(a_temperature)-1+airconditioner.temperature_rate)), max(15, min(35, a_temperature+airconditioner.temperature_rate))};
    a_temperature>35-(airconditioner.temperature_rate): {35};
    a_temperature=15-(airconditioner.temperature_rate): {max(15, min(35, a_temperature+airconditioner.temperature_rate)), max(15, min(35, a_temperature+1+airconditioner.temperature_rate))};
    a_temperature<15-(airconditioner.temperature_rate): {15};
    TRUE: {max(15, min(35, a_temperature-1+airconditioner.temperature_rate)), max(15, min(35, a_temperature+airconditioner.temperature_rate)), max(15, min(35, a_temperature+1+airconditioner.temperature_rate))};
esac;
```

Internal-variable attack expansion takes effect in three places:

1. **VAR declaration range expansion** (`SmvDeviceModuleBuilder.appendInternalVariables`):
   only for numeric internal variables of sensor devices; the formula matches environment
   variables — `expansion = range/5 * intensity/50` — and expands the upper bound only.
2. **next() attack branch** (`SmvMainModuleBuilder.appendInternalVariableTransitions`):
   when `isAttack=true` and the device is a sensor, generates a
   `device.is_attack=TRUE: lower..upper` branch, with the upper bound expanded via
   `SmvBoundsUtils.resolveEffectiveUpperBound()` (consistent with the VAR declaration),
   letting the attacker set the variable to any value in the expanded range.
3. **Actuator state hijack** (`SmvMainModuleBuilder.appendStateTransitions`): when
   `isAttack=true` and the device is a non-sensor (actuator), the case for
   `next(device.ModeVar)` gets a highest-priority branch
   `device.is_attack=TRUE: {all legal states}`, letting the attacker hijack the actuator to
   any legal state. This branch takes priority over rules and template Transitions, so a
   compromised actuator bypasses the normal transition logic. The resulting state jump also
   triggers an API-signal pulse (`appendApiSignalTransitions` detects
   `next(mode)=endState`) — this is expected behavior; a hijacked device can produce
   arbitrary signals.

---

## Complete SMV example

_Migrated from the former `NuSMV_Module_Documentation.md` §6._

A complete SMV file for a thermostat + fan scenario, generated with attack mode and the
privacy dimension enabled.

**Scenario:** when the thermostat temperature > 30, the fan turns on automatically; verify
the fan never runs in an untrusted state.

**Request parameters:** `isAttack=true, intensity=50, enablePrivacy=true`

```smv
--IF thermostat_1.temperature>30 THEN fan_1.fanAuto

MODULE Thermostat_thermostat1
FROZENVAR
	is_attack: boolean;
VAR
	ThermostatMode: {cool, heat, off};
	temperature: 15..35;
	setCool_a: boolean;
	trust_ThermostatMode_cool: {untrusted, trusted};
	trust_ThermostatMode_heat: {untrusted, trusted};
	trust_ThermostatMode_off: {untrusted, trusted};
	trust_temperature: {untrusted, trusted};
	privacy_ThermostatMode_cool: {private, public};
	privacy_ThermostatMode_heat: {private, public};
	privacy_ThermostatMode_off: {private, public};
	privacy_temperature: {private, public};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(ThermostatMode) := cool;
	init(setCool_a) := FALSE;
	init(trust_ThermostatMode_cool) := trusted;
	init(trust_ThermostatMode_heat) := trusted;
	init(trust_ThermostatMode_off) := trusted;
	init(trust_temperature) := trusted;
	init(privacy_ThermostatMode_cool) := public;
	init(privacy_ThermostatMode_heat) := public;
	init(privacy_ThermostatMode_off) := public;
	init(privacy_temperature) := public;

MODULE Fan_fan1
FROZENVAR
	is_attack: boolean;
VAR
	FanMode: {auto, manual, off};
	fanAuto_a: boolean;
	trust_FanMode_auto: {untrusted, trusted};
	trust_FanMode_manual: {untrusted, trusted};
	trust_FanMode_off: {untrusted, trusted};
	privacy_FanMode_auto: {private, public};
	privacy_FanMode_manual: {private, public};
	privacy_FanMode_off: {private, public};
ASSIGN
	init(is_attack) := {TRUE, FALSE};
	init(FanMode) := off;
	init(fanAuto_a) := FALSE;
	init(trust_FanMode_auto) := trusted;
	init(trust_FanMode_manual) := trusted;
	init(trust_FanMode_off) := trusted;
	init(privacy_FanMode_auto) := public;
	init(privacy_FanMode_manual) := public;
	init(privacy_FanMode_off) := public;

MODULE main
FROZENVAR
	intensity: 0..50;
INVAR intensity <= 50;
VAR
	thermostat_1: Thermostat_thermostat1;
	fan_1: Fan_fan1;
	a_temperature: 15..39;
ASSIGN
	init(intensity) := 0 + toint(thermostat_1.is_attack) + toint(fan_1.is_attack);
	-- 状态转换（攻击劫持优先 + 规则条件驱动 + API startState 约束）
	next(thermostat_1.ThermostatMode) := case
		thermostat_1.is_attack=TRUE: {cool, heat, off};
		TRUE: thermostat_1.ThermostatMode;
	esac;
	next(fan_1.FanMode) := case
		fan_1.is_attack=TRUE: {auto, manual, off};
		thermostat_1.temperature > 30 & fan_1.is_attack=FALSE & fan_1.FanMode=off : auto;
		TRUE : fan_1.FanMode;
	esac;
	-- API 信号（基于状态变化检测）
	next(fan_1.fanAuto_a) := case
		fan_1.FanMode!=auto & next(fan_1.FanMode)=auto: TRUE;
		TRUE: FALSE;
	esac;
	next(thermostat_1.setCool_a) := case
		thermostat_1.ThermostatMode!=cool & next(thermostat_1.ThermostatMode)=cool: TRUE;
		TRUE: FALSE;
	esac;
	-- 环境变量 next() 转换（含 NaturalChangeRate 边界检查 + clamp 夹紧）
	next(a_temperature) :=
	case
		a_temperature>=39: {max(15, min(39, a_temperature - 1)), a_temperature};   -- 上边界：候选值夹紧到声明区间
		a_temperature<=15: {a_temperature, max(15, min(39, a_temperature + 1))};   -- 下边界：候选值夹紧到声明区间
		TRUE: {max(15, min(39, a_temperature - 1)), max(15, min(39, a_temperature)), max(15, min(39, a_temperature + 1))};
	esac;
	-- 信任传播
	next(fan_1.trust_FanMode_auto) := case
		fan_1.is_attack=TRUE: untrusted;
		thermostat_1.temperature > 30 & (thermostat_1.trust_temperature=trusted): trusted;
		thermostat_1.temperature > 30: untrusted;
		TRUE: fan_1.trust_FanMode_auto;
	esac;
	next(fan_1.trust_FanMode_manual) := case
		fan_1.is_attack=TRUE: untrusted;
		TRUE: fan_1.trust_FanMode_manual;
	esac;
	next(fan_1.trust_FanMode_off) := case
		fan_1.is_attack=TRUE: untrusted;
		TRUE: fan_1.trust_FanMode_off;
	esac;
	-- thermostat_1 状态级 trust（攻击优先 + 自保持）
	next(thermostat_1.trust_ThermostatMode_cool) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_cool;
	esac;
	next(thermostat_1.trust_ThermostatMode_heat) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_heat;
	esac;
	next(thermostat_1.trust_ThermostatMode_off) := case
		thermostat_1.is_attack=TRUE: untrusted;
		TRUE: thermostat_1.trust_ThermostatMode_off;
	esac;
	-- 变量级 trust（自保持）
	next(thermostat_1.trust_temperature) := thermostat_1.trust_temperature;
	-- 隐私传播
	next(fan_1.privacy_FanMode_auto) := case
		thermostat_1.temperature > 30 & (thermostat_1.privacy_temperature=private): private;
		TRUE: fan_1.privacy_FanMode_auto;
	esac;
	next(fan_1.privacy_FanMode_manual) := fan_1.privacy_FanMode_manual;
	next(fan_1.privacy_FanMode_off) := fan_1.privacy_FanMode_off;
	-- thermostat_1 状态级 privacy（自保持）
	next(thermostat_1.privacy_ThermostatMode_cool) := thermostat_1.privacy_ThermostatMode_cool;
	next(thermostat_1.privacy_ThermostatMode_heat) := thermostat_1.privacy_ThermostatMode_heat;
	next(thermostat_1.privacy_ThermostatMode_off) := thermostat_1.privacy_ThermostatMode_off;
	-- 变量级 privacy（自保持）
	next(thermostat_1.privacy_temperature) := thermostat_1.privacy_temperature;
	-- 外部变量赋值（简单赋值，非 next）
	thermostat_1.temperature := a_temperature;
-- Specifications
	CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.trust_FanMode_auto = untrusted))
	CTLSPEC AG(!(fan_1.FanMode = auto & fan_1.privacy_FanMode_auto = private))
	LTLSPEC G((thermostat_1.temperature > 30) -> F G(fan_1.FanMode = auto))
```

### Parameter-combination examples

Example A — `isAttack=true, intensity=0, enablePrivacy=false`:

```smv
MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 0;
VAR
    ts_1: Sensor_ts1;
ASSIGN
    init(intensity) := 0 + toint(ts_1.is_attack);
```

Meaning: the budget is 0, forcing every device's `is_attack=FALSE`.

Example B — `isAttack=true, intensity=25, enablePrivacy=false`:

```smv
MODULE Sensor_ts1
FROZENVAR
    is_attack: boolean;
VAR
    temperature: 0..110;   -- 原始 0..100，range=100，expansion=100/5*25/50=10
ASSIGN
    init(is_attack) := {TRUE, FALSE};

MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 25;
```

Example C — `isAttack=true, intensity=50, enablePrivacy=true`:

```smv
MODULE Camera_c1
FROZENVAR
    is_attack: boolean;
    privacy_photo: {public, private};
VAR
    trust_Mode_on: {untrusted, trusted};
    privacy_Mode_on: {private, public};
ASSIGN
    init(is_attack) := {TRUE, FALSE};

MODULE main
FROZENVAR
    intensity: 0..50;
INVAR intensity <= 50;
```

Example D — specs no longer inject `intensity<=N`:

```smv
-- current behavior
CTLSPEC AG(!(door_1.LockState = unlocked & door_1.trust_LockState_unlocked = untrusted))

-- budget constraint lives in main
INVAR intensity <= 3;
```

---

## Related

- API field contract: [../api/verification.md](../api/verification.md)
- Config keys (`NUSMV_*`): [../getting-started/configuration.md](../getting-started/configuration.md)
- Change history (identifier sanitization, boundary centralization, atomic cancel
  safety, user isolation): [../../CHANGELOG.md](../../CHANGELOG.md)
