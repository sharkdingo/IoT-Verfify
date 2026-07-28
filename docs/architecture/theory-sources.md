# Theory sources

The modeling, verification, fix, and bounded-exploration semantics in this repo implement published
algorithms. This page is the index: which paper owns which behaviour, and where the implementation
lives. **When the code and a paper disagree, the paper is the specification** — the opposite of the
repo's usual "code wins" rule, which governs code vs. *our own* docs.

Read this before changing generated-model semantics. A construct that looks unmotivated is usually
deliberate; see the cautionary case at the bottom.

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
- **Rule model as a handling node** — a rule becomes its own two-state FSM (`Ready`/`Waiting`) whose
  `Rule_i_Command` label synchronizes with the target device. MEDIC §3.2, Def. 3.2, Fig. 3.
  Implementation: `SmvMainModuleBuilder`'s rule branches and execution probes.
- **Environment model and disturbance** — a shared variable is a single-state self-loop constrained by
  `v' - v ∈ [-1 + env.D.v, 1 + env.D.v]`: the value moves by the device effect "with a slight
  disturbance in the range of [-1, 1] in each time step". MEDIC §3.1 (final paragraph before §3.2),
  Fig. 2b. Implementation: `SmvMainModuleBuilder.appendNumericEnvTransition` and its twin
  `FuzzModel.ValueDomain.nextEnvironmentNumericCandidates`.
- **Trust and privacy propagation** — `trust`/`privacy` per state and variable; a rule whose THIS part
  is untrusted makes its THAT part untrusted. MEDIC §3.3, Def. 3.3, Fig. 4. Implementation:
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

## Where this project deliberately goes beyond a paper

These are intentional, not drift. Keep the list honest when adding more.

- Device templates are user-authored JSON schemas rather than vendor capability documents, so the repo
  validates manifests at persist time (`DeviceTemplateSchemaValidator`, `SmvModelValidator`) — a step
  MEDIC does not need.
- Specification templates 1–7 extend MEDIC's two primitive security templates with safety and
  reachability shapes. MEDIC §4.1 explicitly anticipates this ("More CTL templates ... can be defined
  and integrated into MEDIC for different requirements on demand").
- Generation is *observable*: a rule or spec that cannot be modeled is reported through
  `disabledRuleCount` / `skippedSpecCount` / `generationIssues` rather than silently dropped. The
  papers assume well-formed input.

## Conformance checked against the papers (2026-07-28)

Spot-checked by reading each paper's algorithm alongside the implementation. Verified conforming:

- **MEDIC environment disturbance** — `v' - v ∈ [-1 + env.D.v, 1 + env.D.v]` appears as the ±1
  boundary candidates in `SmvMainModuleBuilder.appendNumericEnvTransition` and, mirrored, in
  `FuzzModel.nextEnvironmentNumericCandidates`. Both engines agree, so a fuzz candidate path stays
  reachable in the formal model.
- **Salus §5.3 parameter refinement** — candidates are ordered by distance from the original value
  (`ParameterAdjustStrategy`), so the closest working value is offered first.
- **Salus §5.2 condition candidates** — candidate conditions to add are derived from the violated
  specification's own conditions (`FixStrategyUtils`), not invented.
- **HAFuzz distance-guided search** — the explorer keeps the minimum-distance seed per round and
  persists both the requested and effective seed, so a finding is replayable.
- **FSM thesis ch.4 repair loop** — the ¬ρ search proposes candidate values and `forwardVerify`
  re-checks each against the real specification; a rejected candidate is added to the exclusion
  invariants rather than retried. `forwardVerify` also refuses to confirm a fix whose regenerated
  model is incomplete, so a vacuous pass is never reported as a repair.

## The cautionary case

On 2026-07-28 the ±1 environment disturbance was mistaken for an unauthored step and removed from both
engines. The reasoning looked sound and was checked against a real NuSMV 2.7.1 run: with no declared
`NaturalChangeRate` and every device effect inactive,
`35 -> 34`, which reads exactly like a false alarm. It was reverted the same day: MEDIC §3.1 specifies
that disturbance, because a numeric environment value is an imperfectly-observed physical quantity.

Two lessons worth keeping:

- **An empirical check confirms what the code does, not that the code is wrong.** The NuSMV run proved
  the transition existed. It could not tell me the transition was intended.
- **Asymmetric risk.** An over-permissive environment model yields a false alarm the user can dismiss;
  an over-restrictive one hides a real violation. When unsure which way to err, err toward the paper.
