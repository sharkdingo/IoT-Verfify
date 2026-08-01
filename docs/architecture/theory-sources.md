# Theory sources

The modeling, verification, fix, and bounded-exploration semantics in this repo draw on published
algorithms. This page records which paper motivates each behaviour, which parts the product adopts,
and where it deliberately differs. The product contract is the explicit behavior documented here,
in the owning API/model documents, and in `modelSemantics`; a paper is not a silent override for a
different user-facing contract.

Read the cited section before changing generated-model semantics, then keep the formal checker,
bounded explorer, API contract, tests, and UI explanation aligned with the chosen product meaning.

## The four papers

| Paper | Venue | Owns | Local copy |
| :--- | :--- | :--- | :--- |
| **MEDIC** — Security Checking of Trigger-Action-Programming Smart Home Integrations | ISSTA '23 | Device/rule/environment FSM construction, trust & privacy propagation, attack model + attack intensity, CTL/LTL spec templates | `D:\组\MEDIC.pdf` |
| **Salus** — Systematically Debugging IoT Control System Correctness for Building Automation | BuildSys '16 | Counterexample fault localization and automatic fix strategies (§4–§5) | `D:\组\2993422.2993426.pdf` |
| **HAFuzz** — Temporal Specification Oriented Fuzzing for TAP Smart Home Integrations | ICSE '26 | Bounded candidate exploration: runtime-verification monitor over finite steps, seed selection, mutation | `D:\HAFuzz\icse26-26.pdf` |
| **智能家居物联网系统形式化模型建模与验证** (NJU undergraduate thesis, 2018) | — | Earlier FSM formulation this project's device/state modeling descends from | `D:\组\门神 FSM.pdf` |

The local paths are outside the repo and are not tracked. Anyone reviewing modeling semantics needs
their own copy; the citations below are precise enough to check against any copy of each paper.

## Where each behaviour comes from

- **FSM per device** — WorkingStates → states, InternalVariables → variables, APIs → transitions
  carrying a `Signal_Device_API` label. MEDIC §3.1, Fig. 1. Implementation:
  `SmvDeviceModuleBuilder`, `DeviceSmvDataFactory`.
- **Rule execution** — MEDIC §3.2, Def. 3.2, Fig. 3 introduces a two-state handling node
  (`Ready`/`Waiting`). IoT-Verify collapses that internal handling step: IF reads the current state and
  the command writes the target's next state, matching HAFuzz §3.3, Fig. 5 and the product's Immediate
  template. Implementation: `SmvMainModuleBuilder`'s rule branches and execution probes.
- **Environment model** — MEDIC §3.1, Fig. 2b defines a numeric shared value by
  `v' - v ∈ [-1 + env.D.v, 1 + env.D.v]`: the device effect is combined with a per-step
  `[-1, 1]` physical disturbance. IoT-Verify exposes that fixed interval as the required
  `NaturalChangeRate` parameter. `[-1, 1]` therefore reproduces the paper rule exactly; `0`
  explicitly disables independent natural change; another declared interval is a visible
  parameterized extension. The declaration is a **constraint on `v' - v`**, so the formal
  generator and the bounded explorer both admit *exactly* the integers in it — combined with the
  active device effect and clamped to the declared domain. **The interval is the whole meaning: no
  value is added to it and none omitted.** Two failure modes bracket this, and both actually shipped:

  - *Omitting interior values* is **unsound**. Emitting only `{lower, 0, upper}` made NuSMV *prove*
    `AG (v = 5 -> AX v != 6)` for a variable declared `[-3, 3]`, i.e. a `SATISFIED` verdict for a step
    the declaration permits.
  - *Adding a stutter* is **unfaithful**. Injecting `0` into every interval made
    `[-4, -2]` ("this tank always drains 2–4 per step") unstatable: NuSMV reported `AF (level = 0)`
    false and `EG (level = 10)` true, offering a trace where the mandatory drain never happened — a
    pseudo-counterexample the user cannot act on. MEDIC never re-adds a stutter either, because `0` is
    already inside `[-1, 1]`.

  So an interval **excluding** `0` means the value *always* changes; one **including** `0` means it
  *may* hold. A user who wants "drains 2–4, or holds" writes `[-4, 0]`, which is a strictly weaker
  claim and says so on its face. This is exact semantics, not a verification abstraction. Because the
  span is a state-space cost, it is bounded by `RequestLimits.MAX_NATURAL_CHANGE_RATE_SPAN` and a
  wider declaration is rejected rather than silently narrowed.
- **Device effect timing** — Fig. 2b combines the device effect and the environment step in the same
  transition, so each device's `<var>_rate` is a `DEFINE` over its current state rather than a state
  variable. A stored rate is read unprimed while it is itself computed from the current mode, which
  delayed every effect by one step and made a device that started in an acting mode contribute
  nothing on the first transition. The bounded explorer derives the same effect from the live state.
- **Trust and privacy propagation** — `trust`/`privacy` labels belong to states and variables. Under
  MEDIC §3.3, Def. 3.3, Fig. 4, a target becomes untrusted only when every contributing trigger source
  is untrusted, while any private source makes the target private. Implementation:
  `SmvMainModuleBuilder`'s property transitions.
- **Attack model** — a boolean `attacked` per device; a compromised sensor reports a random in-domain
  value with `trust := untrusted`, and a compromised actuator or link drops the command via an
  `attacked == False` transition guard. Compromise adds no new actuator state transition. MEDIC §3.4,
  Figs. 5–6. Implementation: `AttackSurface`, `SmvDeviceModuleBuilder`, `SmvMainModuleBuilder`.
- **Attack intensity** — `intensity = Σ d.attacked` as a counter variable, with specs extended by
  `attack.intensity ≤ v`. MEDIC §4.2–§4.3. Implementation: the attack-budget handling in
  `SmvMainModuleBuilder`.
- **Spec templates** — the trustworthiness and privacy invariants
  `AG !(d.st.trust=untrusted AND d.st=True)` and `AG !(d.st.privacy=private AND d.st=True)`, plus the
  attack-extended forms. MEDIC §4.1, §4.3. Implementation: `SmvSpecificationBuilder`; see
  [spec-templates.md](spec-templates.md).
- **Fault localization and fixes** — Salus §4–§5. Implementation: `FaultLocalizer` and the strategies
  under `component/nusmv/fixer/`; see [auto-fix.md](auto-fix.md).
- **Bounded exploration** — HAFuzz's runtime-verification monitor checking LTL violations within finite
  steps, used to guide seed selection. Implementation: `FuzzEngine`, `FuzzModel`, and the
  `component/fuzz/paper/` monitor FSM; see [fuzzing-flow.md](fuzzing-flow.md). HAFuzz findings are
  candidate evidence, never formal conclusions — budget exhaustion is not satisfaction.

## Where this project deliberately differs from or goes beyond a paper

These are intentional, not drift. Keep the list honest when adding more.

- Device templates are user-authored JSON schemas rather than vendor capability documents, so the repo
  validates manifests at persist time (`DeviceTemplateSchemaValidator`, `SmvModelValidator`) — a step
  MEDIC does not need.
- Rule execution collapses MEDIC's internal `Ready`/`Waiting` handling-node transition into one
  user-visible current-state-to-next-state step. This keeps verification, simulation, traces, fixes,
  HAFuzz path formation, and specification template 4 on one temporal convention.
- Numeric environment evolution parameterizes MEDIC's fixed per-step `[-1, 1]` disturbance.
  Every shared numeric declaration must state `NaturalChangeRate`: use `[-1, 1]` for exact
  MEDIC behavior, `0` for explicit stutter absent device effects, or another interval for a
  deliberate domain-specific widening. The interval is modeled exhaustively rather than as a
  shortlist of interesting values, so a wider interval is a genuinely weaker assumption instead of a
  different one. The generator never layers a second hidden `[-1, 1]` term on top of that
  declaration. An interval that excludes zero (say `[2, 4]`) is a *mandatory* per-step change; to
  allow holding still the user writes an interval containing zero (`[0, 4]`). Optional device-local
  numeric rates use the same convention as a project extension; they are not part of MEDIC's shared
  physical-environment equation.
- Specification templates 1–7 extend MEDIC's two primitive security templates with safety and
  reachability shapes. MEDIC §4.1 explicitly anticipates this ("More CTL templates ... can be defined
  and integrated into MEDIC for different requirements on demand").
- Generation is *observable*: a rule or spec that cannot be modeled is reported through
  `disabledRuleCount` / `skippedSpecCount` / `generationIssues` rather than silently dropped. The
  papers assume well-formed input.

## Conformance checked against the papers (2026-07-31)

Spot-checked by reading each paper's algorithm alongside the implementation. Verified conforming:

- **Salus §5.3 parameter refinement** — candidates are ordered by distance from the original value
  (`ParameterAdjustStrategy`), so the closest working value is offered first.
- **Salus §5.2 condition candidates** — candidate conditions to add are derived from the violated
  specification's own conditions (`FixStrategyUtils`), not invented.
- **HAFuzz distance-guided search** — the explorer keeps the minimum-distance seed per round and
  persists both the requested and effective seed, so a finding is replayable. Its per-level weight
  is Algorithm 1 line 25's `2^(l_up-l) / (2^l_up - 1)`; the reference artifact obtains the same
  denominator by summing the powers used by all levels.
- **FSM thesis ch.4 repair loop** — the ¬ρ search proposes candidate values and `forwardVerify`
  re-checks each against the real specification; a rejected candidate is added to the exclusion
  invariants rather than retried. `forwardVerify` also refuses to confirm a fix whose regenerated
  model is incomplete, so a vacuous pass is never reported as a repair.

## Review discipline

- A test or NuSMV run confirms what the implementation does; paper conformance still requires reading
  the cited definition and comparing the complete transition, not one boundary example.
- A paper-inspired assumption that widens behavior must be represented in the product contract. Do not
  introduce undeclared nondeterminism merely because it is conservative for one analysis goal.
- When the product deliberately abstracts a paper mechanism, name both semantics and explain why the
  product convention wins, rather than describing a subset as an exact reproduction.
