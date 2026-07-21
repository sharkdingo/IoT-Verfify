# NuSMV Model Generation

This document owns the architecture-level contract for converting an IoT-Verify
scenario into NuSMV. Request and response field tables live in
[../api/verification.md](../api/verification.md); specification formulas live in
[spec-templates.md](spec-templates.md); identity rules live in
[device-identity.md](device-identity.md).

Verified against code on 2026-07-22. Primary sources:
`SmvGenerator`, `DeviceSmvDataFactory`, `SmvModelValidator`,
`SmvDeviceModuleBuilder`, `SmvMainModuleBuilder`, `SmvSpecificationBuilder`, and
`SmvTraceParser`, `NusmvExecutor`, and `NusmvTempArtifactCleaner`.

## What the model means

The generated model is a finite abstraction of the submitted device templates,
instance starting values, shared environment pool, automation rules, and formal
specifications. A successful check establishes a property only for that generated
model and the assumptions returned in `modelSemantics`. It does not prove firmware,
network, authentication, encryption, physical installation, or real-world timing.

Simulation returns one NuSMV trajectory. It is model exploration, not a forecast.
Verification explores all modeled branches, but a `SATISFIED` result is complete only
when `modelComplete=true`; see [verification-flow.md](verification-flow.md).

## Generation pipeline

```text
VerificationRequestDto / SimulationRequestDto
  -> DeviceSmvDataFactory (capture referenced manifests once and resolve canonical ids)
  -> NusmvRequestValidator (request semantics against that captured set)
  -> DeviceSmvDataFactory (rebuild normalized runtime data from the same manifests)
  -> SmvModelValidator (template/model invariants)
  -> SmvDeviceModuleBuilder (one module per distinct device-module shape)
  -> SmvMainModuleBuilder (instances, environment, rules, labels, attack scenario)
  -> SmvSpecificationBuilder (CTL/LTL generated from structured conditions)
  -> model.smv
  -> NuSMV 2.6-2.7
  -> structured result, generation issues, and optional trace
```

Every generator entry receives a structured per-run attack scenario. `NONE` disables
attack choices. `EXACT_POINTS` fixes each modeled device/link flag to `TRUE` or `FALSE`.
`ANY_UP_TO_BUDGET` keeps flags nondeterministic and constrains their total to a validated
`1..50` upper bound. The budget is never clamped and cannot exceed the behavior-changing
device points plus submitted rule links. The value `50` is a per-run checker input cap,
not an attack-surface count. For larger scenes, clients must show both the full
`modelSemantics.modeledAttackPointCount` and the 50-point run cap; a run at the cap does
not cover branches with more than 50 simultaneous compromises.

Template resolution is a model-boundary snapshot, not a late repository lookup.
Synchronous and asynchronous services capture every distinct referenced manifest before
accepting the run, return that scope as `modelSnapshot`, and pass the resolved device
model into generation. A queued task therefore cannot validate against one template
version and execute against another. Verification counterexamples and simulation traces
persist the exact manifests internally; automatic-fix replay uses that saved set. Raw
manifests remain server-side implementation/audit context, while users see counts,
capture time, and explicit current-Board comparison status.

## Data and identity boundaries

### Device templates and instances

`DeviceTemplateDto.manifest` defines possible behavior. `DeviceNodeDto` defines one
instance and its starting overrides. A template name is not an instance identity.
Rules and specifications are converted to canonical model ids (`devices[].varName`)
before generation; labels remain display metadata.

`backend/device-template-schema.json` is the structural authority for default,
REST-imported, and AI-created templates. Persistence also runs semantic validation and
a NuSMV probe generation. Invalid templates are rejected, not partially imported.

### Variable scope

| Manifest declaration | Model meaning |
| :--- | :--- |
| `InternalVariables[].IsInside=true` | Device-local variable, emitted as `device.variable` |
| `InternalVariables[].IsInside=false` | Shared environment reading, stored once in the board environment pool and emitted internally as `a_<name>` |
| `EnvironmentDomains[]` | Domain/default metadata for an impact-only shared value; no device read mirror or rule/spec read permission |
| `ImpactedVariables[]` | Shared environment value the device may change; this grants write impact, not read permission |
| `FalsifiableWhenCompromised=true` | The compromise model may replace this reported value with any value in its declared domain and marks its trust label untrusted |

`IsInside` and `FalsifiableWhenCompromised` are required on every template variable.
`IsInside` explicitly chooses ownership: `true` is instance-local and `false` is
scene-shared. Omission is rejected because defaulting it to shared would change rule,
scene-import, and attack semantics. `FalsifiableWhenCompromised` is explicit
because API presence cannot classify a composite device as a pure sensor or actuator.
Use `true` for sensor readings or received data that compromise can falsify. Use
`false` for actuator progress, setpoints, and other values that the selected threat
model does not falsify.

Variable domains are semantic, not UI hints. Numeric ranges are ascending and use
`ChangeRate` for `WorkingStates[].Dynamics`; enum/boolean domains use an explicit
in-domain `Value`. A Dynamic may target only a local variable or a shared variable listed
in `ImpactedVariables`, once per working state. Domain/type mismatches, normalized enum
duplicates, malformed natural rates, and unknown targets fail template validation instead
of being omitted or converted to an arbitrary fallback rate. Numeric impact rate variables
are generated only for numeric domains; boolean impacts remain boolean.

WorkingState behavior is structured. The manifest does not accept a raw `Invariant`
NuSMV expression: that legacy-looking field never participated in generation and would
also force users to author internal identifiers. State-dependent effects belong in
`Dynamics`, autonomous behavior in `Transitions`, and properties to check in structured
specifications.

A stateful template's `InitState` is deterministic and must match one complete
`WorkingState` tuple. Partial tuples and `_` are reserved for API/Transition endpoints
that intentionally change only selected modes; they cannot be used to hide an
unspecified model starting state.

The attack model never widens `Values` or `LowerBound..UpperBound`. Every variable must
choose one domain form explicitly; boolean readings use
`Values: ["TRUE", "FALSE"]`. An omitted domain is rejected instead of silently becoming
boolean.

Evolution is scope-sensitive. A device-local variable follows its declared Transition
assignment, WorkingState Dynamic, or numeric `NaturalChangeRate`; if none applies, it
retains its current value. The generator does not invent arbitrary local device changes.
A shared numeric environment value follows its declared natural rate and active device
effects within the declared domain. A shared enum/boolean environment value is an
uncontrolled model input and may otherwise choose any value in its declared domain on
each step. These assumptions are returned, rather than merely documented, through
`modelSemantics.environmentEvolutionEffects` and `localVariableFallbackPolicy`.

### Environment authority

The board environment pool is the scenario-level source of initial value, trust, and
privacy for shared variables. Shared template declarations must label trust/privacy
explicitly. Per-device copies in model requests express which
templates may read that value; they are not independent values. Conflicting domains
for the same shared name are rejected, including conflicts in enum ordering, natural
change rate, default trust/privacy, or name casing. Every impact resolves from the same
manifest; the generator loads only templates referenced by submitted devices, so an
unused account template cannot change the current model.

Explicit shared initial values are exact model inputs after whitespace normalization.
Invalid enum or numeric values, unknown or duplicate environment entries, undeclared
domains, and malformed natural-change rates fail generation; the generator never
clamps a value, replaces it with the first enum member, assumes `0..100`, or silently
omits it. When a valid value is omitted, the documented template default or
nondeterministic initialization may apply according to the model contract.

Generated identifiers such as `a_temperature`, `trust_temperature`, and module names
are internal NuSMV details. API traces convert shared variables back to their literal
board names and place runtime-only globals in `globalVariables`.

## MEDIC-aligned security dimensions

IoT-Verify follows the threat and label-propagation model in *Security Checking of
Trigger-Action-Programming Smart Home Integrations* (MEDIC, ISSTA 2023), especially
Sections 3.3, 3.4, and 4.3:

- compromised sensor data may be falsified and becomes untrusted;
- a TAP command may fail to reach a compromised actuator target;
- a compromised automation delivery link independently drops its rule command;
- a target becomes untrusted only when all trigger sources are untrusted; one trusted
  source means the user retains a trusted control path under MEDIC Definition 3.3;
- private data propagates when any trigger source is private;
- exhaustive verification uses an upper-bound threshold; exact runs use only their
  explicitly selected points.

A device instance is one budget point only when compromise can change this generated
model: it has a template-declared falsifiable reading and/or is the target of at least
one submitted automation command. Each submitted automation rule's command-delivery
link is another point. Inert canvas devices are excluded instead of consuming budget
without an effect. This is a user-visible abstraction of MEDIC's node/link threat model:
the rule link is countable, but it is not a claim that IoT-Verify knows the home's
physical Wi-Fi, Zigbee, or routing topology. One rule is one delivery link, rather than
separate sensor-to-handler and handler-to-actuator segments. A multi-condition rule can
render several trigger edges on the canvas, but those visual edges do not create extra
attack-budget points.

### Attack selection and budget

When attack modeling is enabled, every behavior-changing device point receives an
internal frozen `is_attack` flag and every submitted rule receives a frozen
automation-link flag.
Device modules with no modeled compromise effect receive no attack flag. The main module
derives the total selected in that branch and constrains it:

```smv
FROZENVAR
    iot_verify_compromised_point_count: 0..(EFFECTFUL_DEVICE_COUNT + RULE_COUNT);
    iot_verify_automation_link_compromised_0: boolean;
INVAR iot_verify_compromised_point_count <= ATTACK_BUDGET;

ASSIGN
    init(iot_verify_automation_link_compromised_0) := {TRUE, FALSE}; -- exhaustive mode
    init(iot_verify_compromised_point_count) :=
        0 + toint(device_1.is_attack) + toint(device_2.is_attack)
          + toint(iot_verify_automation_link_compromised_0);
```

These names are diagnostics, not API input. In `ANY_UP_TO_BUDGET`, each flag is
nondeterministic and the invariant uses `<=`, so budget `N` represents every modeled
selection from zero through `N` compromised points. In `EXACT_POINTS`, selected flags
initialize to `TRUE`, all other modeled flags initialize to `FALSE`, and no budget
invariant changes that fixed selection. Automation-link exact selection uses the
persisted submitted `ruleId`, so automatic-fix reverification reuses the same link even
if generated list positions change.
One verification call does not search for or report the smallest budget that can cause
a violation. Users comparing minimum compromise resistance must rerun verification with
different upper bounds and compare the first violating complete result.

The response makes this machine-readable:

```text
attackPointUnit = BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK
attackSelectionPolicy = EXACT_ATTACK_POINTS | UP_TO_ATTACK_BUDGET_NONDETERMINISTIC
selectedAttackPoints = [...stable ids plus frozen display labels, only for exact mode...]
attackEffects = [
  ...only effects present in this scene...
]
modeledDeviceAttackPointCount = EFFECTFUL_DEVICE_COUNT
modeledFalsifiableReadingDeviceCount = FALSIFIABLE_READING_DEVICE_COUNT
modeledAutomationLinkAttackPointCount = RULE_COUNT
modeledAttackPointCount = EFFECTFUL_DEVICE_COUNT + RULE_COUNT
```

`attackEffects` includes reading falsification only when the falsifiable-reading count is
nonzero, and includes target/link command loss only when the rule count is nonzero. It
therefore describes the generated scene rather than advertising every mechanism the
platform can support. The falsifiable-reading count is a subset of the distinct effectful
device count and is not added again to the attack-point total.

The four counts are computed from canonical device instance semantics, then persisted with both
asynchronous task context and saved verification/simulation traces. Historical results
therefore remain interpretable after the board changes and are not reconstructed from raw
request collection lengths or template aliases. With
attack mode `NONE`, `attackSelectionPolicy=NOT_MODELED` and `attackEffects=[]`; the snapshot
counts still describe the run's potential behavior-changing attack surface while the
effective budget is zero.

The service rejects an enabled attack scenario when the scene has no automation rule and none of its
template variables is marked `FalsifiableWhenCompromised=true`. Every attack flag would
otherwise be behaviorally inert, so accepting the request would present a no-op run as
attack analysis. In a larger valid run, those inert device instances are likewise
excluded from the generated attack choices and snapshot denominator.

### Reading falsification

For a variable marked `FalsifiableWhenCompromised=true`:

- a shared/environment reading is selected from its declared domain whenever that
  instance is attacked;
- a device-local reading uses the declared domain in both its initial and next-state
  attacked branches;
- its trust label is `untrusted` while attacked.

Variables marked `false` keep their ordinary initialization and dynamics. This is true
even on a template that also has APIs. Conversely, a local reading marked `true` is
falsifiable even when the same composite template has APIs.

### TAP command loss

Rule-driven commands require both `target.is_attack=FALSE` and the corresponding
automation-link choice to be `FALSE`. A compromised target or compromised delivery
link therefore drops the matching command. The same guard prevents a dropped command from
updating target trust/privacy labels. Template internal transitions and unrelated
dynamics are not frozen, and the attacker is not given an arbitrary actuator-state
hijack branch.

The automation link is a logical delivery path derived from one TAP rule. Physical
network routes, packet timing, encryption, and multiple network segments are not
modeled.

### Trust and privacy labels

Trust is always modeled. Privacy propagation is modeled only when
`enablePrivacy=true`; a privacy specification forces the effective flag on at both the
UI and service boundaries. Results return that effective value, so a caller that submits
`false` cannot mistake the run for one that omitted privacy propagation.

Template declarations are the default label authority. A state's initial trust/privacy
comes from its matching `WorkingStates[]` entry, and a variable's label comes from its
`InternalVariables[]` entry. Device runtime fields override only the current state or
named variable when explicitly supplied; omitted fields do not materialize a copied
instance value. Shared Environment Pool entries similarly fall back to their active
template domain labels when an override is absent. Trust labels describe provenance and
propagation; `untrusted` does not mean the device is selected as compromised.

Default source labels follow MEDIC's origin semantics rather than a generic sensor
reliability score. Built-in schedule/date values, inbound email, car/mobile location,
step counts, exterior RFID events, and door/window contact readings start as
`untrusted`: each can initiate an automation without an in-house user action retaining
control of that trigger. An in-house action source such as the built-in Motion Detector
may start as `trusted`. This distinction does not claim that motion sensing is inherently
more accurate or authenticated; it states only the modeled origin assumption. Compromise
can still falsify any value whose template explicitly sets
`FalsifiableWhenCompromised=true` and then forces that value's source label to
`untrusted`. Users may override initial labels when their deployment assumptions differ;
the label is neither authentication nor an attack probability.

Default privacy labels follow sensitivity of the fact itself, not device ownership or the
mere existence of an API. Routine appliance modes and ordinary environmental readings
start as `public`; location, activity/occupancy, security access, communications, financial,
health, and personal-content facts start as `private`. These are reviewable template
authoring defaults, not access-control decisions. Users may override them when the actual
deployment has different privacy assumptions.

Concrete built-in examples follow that classification: social-network `posting`, phone
`taking photo` / `uploading to cloud`, and door/window/garage open/contact facts are
private, while the same devices' idle or ordinary powered-on states remain public.

| Dimension | Rule propagation policy | What it does not mean |
| :--- | :--- | :--- |
| Trust | MEDIC retained-control label: target is untrusted only if every resolved trigger source is untrusted; one trusted source keeps it trusted | Authentication, data-integrity taint, exploit probability, or device ownership |
| Privacy | Target is private if any resolved trigger source or the rule's explicitly selected content item is private | Access control, encryption, copying payload bytes, or blocking transmission |

The exact policies are returned as
`TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED` and
`TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE`. When privacy is disabled, the latter is
`NOT_MODELED`. The response also returns
`labelPropagationScope=AUTOMATION_RULE_COMMANDS_ONLY`, matching MEDIC Definition 3.3:
the reset assignments are attached to synchronized TAP command transitions. Template
internal Transitions, WorkingState Dynamics, and natural evolution may change a state or
value but do not copy their trigger's label into that result. Their declared/previous
labels remain in force unless an automation command or modeled attack branch updates
them. This is a deliberate model boundary, not evidence that those internal behaviors
preserve real-world trust or confidentiality.

Template security labels are explicit inputs, not permissive defaults. Every
WorkingState and InternalVariable declares both trust and privacy, every shared
EnvironmentDomain declares both, and every Content declares privacy. Template import
rejects a missing label rather than silently interpreting unknown provenance as trusted
or unknown sensitivity as public.

Every model run revalidates the stored raw template manifest against the canonical JSON
schema before DTO conversion. An old or externally modified database row therefore
cannot drop an unknown behavior field or default a missing content label to public behind
a successful verification result; the run fails before model generation instead.

A content item is a template-authored sensitivity label used as one propagation input.
It is not a modeled payload or access-control object. A rule may select it only when the
target API explicitly declares `AcceptsContent=true`; this prevents unrelated commands
such as opening a light from being presented as content transfers. Specifications
therefore check the resulting target state/variable label; directly checking the static
content declaration would be a trivial classification assertion rather than a leakage
property.

For a full-state rule condition on a multi-mode device, only modes referenced by the
condition's state tuple participate in label propagation. Current labels within one mode
are selected by that mode's actual state. Referenced modes are combined with OR over
`trusted` predicates (one trusted source retains control) and OR over `private`
predicates (one private source propagates sensitivity). A signal API that changes several
modes combines every changed state in the same way. Template validation requires complete working-state tuples and
rejects conflicting labels for a reused mode-state component rather than allowing JSON
order to choose the generated label.

Authored multi-mode state conditions may use either an empty tuple segment or `_` as an
explicit per-mode wildcard. For example, `on;_` constrains the first mode to `on` and
leaves the second mode unconstrained. Rule generation, specification generation, fault
localization, and fix validation interpret both spellings identically. This does not relax
template manifests: every declared `WorkingState.Name`, `InitState`, and concrete API
state tuple must still be complete and valid.

State overrides use literal `currentStateTrust` and `currentStatePrivacy` values.
Variable overrides use literal template variable names. Generated keys such as
`mode_state`, `trust_*`, and `privacy_*` are not user-authoring concepts.

Whether state labels exist depends on the template having modes, not on it having a
command API. A stateful sensor with no APIs therefore exposes its WorkingState trust and
privacy labels as read-only model data when its state is used by a rule or specification.
Compromising that sensor still affects only readings explicitly marked
`FalsifiableWhenCompromised`; it does not grant arbitrary state-machine control.

For a multi-mode state or signal API that contributes several mode states, a safety
specification references every contributing trust label. A protected compound state is
treated as unsafe when any of its participating state labels is untrusted, so those
untrusted predicates are disjoined. This safety check is distinct from rule propagation,
where MEDIC marks a target untrusted only when all trigger sources are untrusted. If a safety condition
cannot resolve its trust source, generation fails
closed; it is never degraded to an unconditional prohibition.

## Rule semantics

A rule reads all IF conditions in the current state and changes the command target in
the next state. `targetType` is explicit (`api`, `variable`, `mode`, or `state`); the
generator does not infer it from a name.

- signal API conditions represent an event pulse and require an explicit `Signal=true`;
  every API must explicitly choose `Signal=true` (observable trigger) or `false`
  (command-only), because omission cannot safely decide rule/spec capability;
- autonomous `Transitions` do not expose event signals. A Transition always has a
  structured trigger and one modeled state/variable effect; only a state-changing API
  may expose a user-referenceable one-step pulse with `Signal=true`. Template validation
  rejects an observable API whose state-change route overlaps another API or Transition;
- state/mode conditions use enum equality, inequality, inclusion, or exclusion;
- bounded numeric variables additionally support ordering comparisons;
- command actions must exist in the target template;
- command loss under attack applies at the target guard as described above.

An API pulse is true for one step only when at least one affected mode actually changes
from the API's complete `StartState` tuple into its complete `EndState` tuple. Merely
remaining in the end state does not satisfy an API condition. Template validation rejects
stateless APIs, no-effect APIs, API variable assignments, and duplicate signal APIs with
indistinguishable state transitions. Triggered `Transition.Assignments` are validated
against declared target domains so accepted template behavior is never silently ignored.
An accepted autonomous Transition has one modeled effect only: one concrete mode update
or one variable assignment. Combined/multi-mode/multi-assignment effects are rejected at
template and generation boundaries because independently generated `next(...)` branches
could otherwise apply only part of the declared action. Environment-variable triggers
read the shared `a_<name>` value; impact-only environment declarations remain write-only.
Enum/mode/boolean trigger values use equality/inequality and numeric thresholds must lie
inside the declared range, preventing an accepted transition from silently becoming
impossible or tautological.

Rule order resolves overlapping actions atomically. If a higher-priority matching API
shares any affected mode with a lower API, the lower API is blocked as a whole; APIs with
disjoint affected modes may execute together. State updates, execution probes, and
trust/privacy propagation all use that same selected action and the API's full start-state
guard.

Request validation rejects known semantic mismatches before execution. A residual
generation-time condition failure disables that rule with guard `FALSE`, increments
`disabledRuleCount`, and adds an item-level `generationIssues` reason. It is not silently
treated as a working rule.

Internal `iot_verify_rule_fired_<index>` probes record which generated rule guards were
true in a trace. The parser returns stable rule ids and user-facing rule snapshots; the
probe names and indexes are not user concepts. Fault localization consumes this execution
evidence when present, so a lower-priority rule that merely looked applicable is not
reported as if it actually executed; reconstruction is only a fallback for traces without
probe metadata.

## Specification semantics

The persisted `SpecificationDto.formula` is a display preview/cache. Verification does
not parse it. `SmvSpecificationBuilder` reconstructs the CTL/LTL expression from
`templateId` plus structured conditions. Results expose the actual
`SpecResultDto.expression`, and saved counterexamples expose `checkedExpression`.

If a specification cannot be emitted, the generator increments `skippedSpecCount` and
adds an item-level `generationIssues` entry. It does not replace the property with a
constant or call the reduced run complete. Formula details and all seven templates are
owned by [spec-templates.md](spec-templates.md).

## Model shape

Each distinct device module declares its modes, local/shared-variable mirrors, event
signals, trust/privacy labels, optional content labels, and optional attack flag. The
`main` module instantiates devices and owns:

1. shared environment domains and initial values;
2. device and automation-link attack choices plus the compromised-point upper-bound invariant;
3. state transitions from rules and template transitions;
4. environment and local-variable dynamics;
5. API/transition event pulses;
6. trust and optional privacy propagation;
7. rule-execution probes used only for structured trace explanation.

Rules are evaluated in the persisted `rules[]` order independently for each target mode.
The first enabled command branch for one target mode wins, while branches for different
modes may be selected together. A rule command branch appears before autonomous template
transitions for the same mode in that step. State transitions, rule-execution probes, and
trust/privacy updates all use the same selected branch, including the command API's
`StartState` constraint and attack delivery guards. A lower-priority rule cannot update
labels when an earlier competing rule won that mode.

NuSMV properties follow the main module. Auto-fix parameter search may additionally
emit internal `param_*`/`lambda_*` frozen variables. Public fix requests use stable
`targetId`/`adjustmentId`; users and AI tools do not submit those generated names or
rule/condition indexes.

## Execution artifacts and output bounds

The executor continuously drains NuSMV output in fixed byte chunks so a full process pipe
cannot deadlock and a single unterminated line cannot force an unbounded `readLine()`
allocation. It retains at most the configured byte count for each stdout/stderr stream.
Truncation retains a valid UTF-8 prefix, appends an explicit marker, and makes verification
or simulation fail as incomplete before result/trace parsing. Completed `nusmv_*` directories retain
`model.smv`, `request.json`, `output.txt`, and `result.json` for diagnosis, then a
scheduled cleaner removes them by maximum age and oldest-first directory count. All
executors acquire the directory lease before checking the model file or waiting for a
concurrency permit, and hold an OS file lock through process/output completion. The cleaner
holds that same local/OS exclusion continuously from its inactivity check through recursive
deletion; there is no check/delete activation window. The sibling lock file also allows
Windows to delete the protected directory while the lock remains open. Neither age retention
nor count pressure can therefore remove an active model. Defaults and overrides are owned by the
[configuration reference](../getting-started/configuration.md#nusmv).

Candidate discovery for parameter and condition repair is intentionally narrower than
ordinary verification. Its main module may add validated `INIT` constraints that reproduce
the complete first state of the selected counterexample: device modes and local variables,
shared environment values, trust/privacy labels, and concrete device/link attack choices.
Only the candidate parameters remain free. Missing or out-of-domain replay data fails model
generation closed, and failure to translate the selected negated specification is also a
generation error rather than a trivially true fallback. These candidate-only constraints are
removed for forward verification, which checks the proposed edit against the original full
initial-state and attack-selection semantics. Strategy/search details are owned by
[Automatic fix](auto-fix.md).

## Completeness and result interpretation

Generation returns:

- `disabledRuleCount` and `skippedSpecCount`;
- item-level `generationIssues` with type, display label, stable localization
  `reasonCode`, and an English technical diagnostic `reason`;
- emitted-spec identity and actual expression;
- `modelComplete`, computed from omissions and reliable result parsing;
- `modelSemantics`, describing attack/trust/privacy assumptions.

Only `outcome=SATISFIED` together with `modelComplete=true` supports the ordinary
"checked model satisfies all submitted specifications" conclusion. `SATISFIED` with an
incomplete model must be presented as reduced-model evidence. `INCONCLUSIVE` is neither
safe nor violated.

## Identifier handling

Mode/state/module identifiers are normalized through the generator's canonical helper.
Template variable and impacted-variable names are cross-referenced structurally and are
therefore rejected at persistence time if they are illegal rather than silently renamed.
The validator also rejects case-insensitive collisions with generated identifiers such
as environment aliases, trust/privacy labels, event signals, attack fields, and auto-fix
parameters.

Trace parsing reverses only known generated namespaces. A real user variable whose
literal name begins with `a_`, `trust_`, or `privacy_` remains that literal variable; it
is not guessed from its prefix.

## Related

- [Verification flow](verification-flow.md)
- [Specification templates](spec-templates.md)
- [Data authority model](data-authority-model.md)
- [Verification, simulation, and fix API](../api/verification.md)
- [Board storage API](../api/board.md)
