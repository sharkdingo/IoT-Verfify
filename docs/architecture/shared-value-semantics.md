# Shared value semantics

This page is the single authoritative semantic model for a **shared value** — a quantity that exists
in the scenario rather than inside one device, such as room temperature, illuminance, or weather.
Every other layer (JSON schema, template validation, board assembly, NuSMV generation, the bounded
explorer, trace presentation, `modelSemantics`) implements this page and nothing else. If a layer
disagrees with this page, the layer is wrong.

Each rule below is tagged with its origin:

- **[MEDIC]** — defined by MEDIC §3.1 (ISSTA '23). The local paper text is quoted where it matters.
- **[EXT]** — a deliberate product extension beyond the paper.
- **[EXACT]** — executable semantics that mean exactly what the user declared.
- **[ABSTRACTION]** — a deliberate over-approximation, disclosed in `modelSemantics`.
- **[REJECTED]** — a shape the product refuses to model rather than guess at.

## 1. Value identity and namespace

A shared value is identified by its **name**, in one flat scenario-wide namespace. Two devices naming
`temperature` mean the same physical quantity; that is the entire point of the concept. **[MEDIC]**
mirrors this: the paper generates "A Environment model for the variable `v`" — one model per value,
not per device.

The name is authored text. Generated NuSMV identifiers (`a_<name>`, `<device>.<name>_rate`) are
internal and never user aliases.

## 2. Who owns the definition

A shared value's **contract** is its type, domain, and natural-evolution interval. Every template
that participates in a shared value carries the full contract, and every participating template must
agree; disagreement is rejected at board assembly with a named mismatch. **[EXACT]**

This is a deliberate choice among three candidates:

| Candidate | Why not / why yes |
| :--- | :--- |
| Board Environment Pool owns the contract, templates reference it | **Rejected.** A template is a portable artifact that is imported, AI-generated, and validated with no board in scope (`DeviceTemplateServiceImpl` performs zero board reads). `WorkingStates.Dynamics` values are checked against the domain at persist time, so a template that carried no domain could not be validated standalone. |
| One template is the canonical owner, others reference it | **Rejected.** It makes template import order significant and leaves a scene broken when the owning template is deleted, replacing a visible disagreement with an invisible dangling reference. |
| **Every participant carries the contract; agreement is enforced** | **Chosen.** Each template stays independently valid and portable, and the redundancy is safe because it is *checked*, not assumed. Repetition is retained only because the invariant in §9 makes it verifiable. |

The Environment Pool owns the **runtime state** of a shared value — its current value, trust, and
privacy — not its contract. That split is why the pool table stores `value/trust/privacy` only.

## 3. Type and domain

A shared value is **numeric** (`LowerBound..UpperBound`, ascending) or **discrete** (an explicit
`Values` enum; booleans use `["TRUE", "FALSE"]`). Exactly one form must be declared; an omitted
domain is **[REJECTED]** rather than defaulted.

**[MEDIC]** models only integers — "`V` is a finite set of integer Variables". Discrete shared values
are therefore **[EXT]**, and every rule about them below is a product decision that must stand on the
user's mental model, not on paper authority.

Clamping to the declared domain is **[EXACT]**: the domain is what the user said the value can be.

## 4. Capabilities: read and affect

Two independent booleans per (device, shared value):

| reads | affects | Meaning | How declared |
| :---: | :---: | :---: | :--- |
| yes | no | A sensor observes the value | shared declaration, `Reads` omitted or true |
| no | yes | An actuator changes it without observing it | `Reads: false` + listed in `ImpactedVariables` |
| yes | yes | Observes and changes it | `Reads` true + listed in `ImpactedVariables` |
| no | no | Not a participant | not declared at all |

**[MEDIC]** supplies exactly this pair: Internal Variables are "variables that are supposed to be
sensed by the related sensors", Impacted Variables are "the environment variables that can be
affected by the devices".

*Read* capability governs two things together, and they may never diverge: whether the device gets a
`device.name := a_name` mirror in the model, and whether its rules and specifications may use the
value as a condition source. **[EXACT]**

No capability may be inferred from array placement, a missing field, a deprecated format, generator
behaviour, or a historical default. `Reads` is meaningful only on a shared declaration; on a
device-local variable it is **[REJECTED]** as a contradiction.

## 5. Natural evolution

A shared numeric value declares `NaturalChangeRate`, an integer interval constraining the per-step
change. **[MEDIC]** writes the environment self-loop as `v' - v ∈ [-1 + env.D.v, 1 + env.D.v]`, so
`[-1, 1]` reproduces the paper exactly and any other interval is **[EXT]** parameterization.

The interval means **exactly itself** — every integer in it, nothing added, nothing omitted.
**[EXACT]** An interval that excludes `0` is a *mandatory* per-step change; one that includes `0`
permits holding still. `0` alone means no independent evolution.

Discrete shared values have no natural-change interval: there is no ordering to move along.

## 6. Device effects

A device's effect on a shared value comes from `WorkingStates[].Dynamics`, evaluated against the
device's **current** state. **[MEDIC]** puts it in the device model — "a Variable `env.D.v` will be
generated to describe how the environment variable `v` will be changed by `D`" — so the effect is
emitted as a `DEFINE` over the live state and applies in the same step the device is acting.
**[EXACT]**

- Numeric: `ChangeRate`, an integer added to the value.
- Discrete: `Value`, an in-domain assignment. **[EXT]**

A state with no matching `Dynamics` entry contributes no effect.

## 7. Composition, and what happens when nothing fires

Per step, for a **numeric** shared value:

```
v' = clamp(v + Σ(active device effects) + δ),  δ ∈ declared NaturalChangeRate
```

Summing concurrent device effects is **[MEDIC]**-faithful (`env.D.v` is additive) and **[EXACT]**.

For a **discrete** shared value the composition depends on who participates — this is **[EXT]**:

| Situation | Behaviour |
| :--- | :--- |
| No device declares it affects the value (purely exogenous) | Free choice within the declared domain each step. **[ABSTRACTION]** — a value nobody in the scene controls may do anything the domain allows. Disclosed as `UNWRITTEN_DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN`. |
| Some device declares it affects the value, and one such effect is active | That declared value. **[EXACT]** |
| Some device declares it affects the value, and no effect is active this step | The value **holds**. **[EXACT]** — the same stutter-when-nothing-declared policy used for device-local variables. Free choice here would invent a change with no cause in the user's scene. Disclosed as `DEVICE_WRITTEN_DISCRETE_VALUES_HOLD_WHEN_NO_DECLARED_EFFECT_APPLIES`. |
| Two or more active effects assign the **same** value | That value. **[EXACT]** |
| Two or more active effects assign **conflicting** values | **[REJECTED]** at board assembly. See §8. |

## 8. Conflicting discrete writers

Two devices whose declared effects can be simultaneously active and assign different values to one
discrete shared value is a **modelling contradiction**, not a resolvable merge. There is no additive
composition for enums, so any resolution would be arbitrary.

Emitting sequential `case` branches silently resolved this by **device iteration order**: the same
scene produced `AX (airQuality = good)` *true* under one order and *false* under the other. That is
backend-specific behaviour the user cannot see, predict, or act on.

Such a scene is therefore **[REJECTED]** with both device names, the value, and both assignments. The
user resolves the contradiction — by changing a declaration or removing a device — rather than
receiving a verdict that depends on an internal ordering.

Numeric writers are never in conflict: they compose additively by §7.

## 9. Invariants

Checkable statements this model must satisfy. Each is enforced somewhere and tested.

1. **One namespace.** All participants in a name refer to one value with one contract.
2. **Contract agreement.** Participating templates declare identical type, domain, and natural rate;
   disagreement is rejected with a named mismatch.
3. **Capability is declared, never inferred.** No code path grants read or affect capability from
   placement, absence, or defaults.
4. **Read implies mirror, and only read implies mirror.** A device gets `device.name := a_name` if
   and only if it reads the value.
5. **Affect-only cannot be read.** An affect-only declaration is not a rule or specification source.
6. **Exact interval.** The admitted numeric delta set equals the declared interval.
7. **Contemporaneous effects.** A device's effect reaches the value in the step it is acting.
8. **Additive numeric composition.** Concurrent numeric effects sum.
9. **No uncaused discrete change.** A discrete value with a declared writer changes only when a
   declared effect is active.
10. **No order-dependent outcome.** No verdict depends on device iteration order.
11. **Both engines agree.** NuSMV and the bounded explorer implement one transition relation.
12. **Disclosure.** Every abstraction in this page appears in `modelSemantics`.

## 10. What is deliberately abstract

Only two things, both disclosed:

- A purely exogenous discrete value may take any declared value each step (§7). This is an
  over-approximation: it can produce counterexamples driven by an input nobody controls, which is
  correct for weather or an occupant but must be recognisable as such.
- A numeric interval wider than `[-1, 1]` weakens the physical assumption relative to MEDIC. It is
  the user's declaration, so it is exact with respect to what they wrote, and `[-1, 1]` recovers the
  paper baseline exactly.

Everything else on this page is exact: it means what the user declared, or it is rejected.
