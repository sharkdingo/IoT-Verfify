# Paper Authority Audit

## MEDIC §3.1 - What the Paper Actually Says

### Definition 3.1: Finite State Machine
"An finite state machine is a tuple F = (S, V, Σ, T), where:
- S is a finite set of States
- V is a finite set of integer Variables
- Σ is a finite set of labels
- T is a finite set of Transitions"

**Key Finding**: V is explicitly "a finite set of **integer Variables**" (emphasis in original analysis).

### Device Schema Elements (§3.1, translated to FSM)

**Internal Variables**: "variables that are supposed to be sensed by the related sensors"

**Impacted Variables**: "the environment variables that can be affected by the devices"

**Key Finding**: The paper defines exactly two categories for shared values - those that can be sensed (read) and those that can be affected (written). Both are integer variables.

### Environment Variable Evolution (Figure 2b, §3.1)

The paper shows: `env.bathtub.humidity = 5` in the model, and describes the constraint:

"If the change rate of variable v in the state s of Device D is r, we have constraint env.D.v = r on the transitions with the target state as s, in the model of Device D."

**For environment transitions**: The paper describes "A Environment model for the variable v is generated as well, which is a model with a single state 'idle', and a self-loop transition, which has a constraint v' - v ∈ [-1, 1] or env.D.v ∈ [-1, 1]"

**Key Finding**: The baseline assumption is `v' - v ∈ [-1, 1]` for natural evolution when no device affects it.

When a device impacts the environment: Figure 2b text describes combining device effect with environment drift contemporaneously in the same step.

### What MEDIC Does NOT Define

1. **Enum or boolean shared values**: Not mentioned anywhere in §3.1
2. **Discrete value semantics**: No treatment of non-numeric domains
3. **Multiple-writer composition**: Only individual device impacts described
4. **Conflict resolution**: Not addressed
5. **Purely exogenous discrete evolution**: No model for weather enums, occupancy booleans, etc.

---

## IoT-Verify's Relationship to MEDIC

### [PAPER] - Direct from MEDIC

1. **Integer variable model**: Numeric environment variables are integer-valued ✓
2. **Internal vs Impacted distinction**: Maps to Reads (sensed) vs Affects (impacted) ✓
3. **Contemporaneous device effects**: Device impact applies in the step it acts (Figure 2b) ✓
4. **Natural evolution baseline [-1, 1]**: Default physical drift assumption ✓
5. **Trust and privacy propagation**: Trust/privacy labels on variables and transitions ✓
6. **Attack modeling**: Boolean 'attacked' variable per device ✓

**Product Implementation**: All correctly implemented. NaturalChangeRate defaults to "stable" (implying [-1, 1] with only 0 permitted when no device effect active).

### [EXTENSION] - Beyond MEDIC Scope

1. **Discrete (enum/boolean) shared values**
   - **Justification**: Real smart home devices have discrete capabilities (door open/closed, mode auto/manual/off, weather sunny/cloudy/rainy)
   - **User mental model**: Users naturally declare enum states, not numeric encodings
   - **Product rule**: Must be explicitly justified by composition and user expectations

2. **User-declared natural evolution intervals wider than [-1, 1]**
   - **Justification**: MEDIC's [-1, 1] is "a physical assumption" about typical sensors. Large tanks, slow HVAC, or abstract time scales may need wider intervals.
   - **Product rule**: User declaration is authoritative; [-1, 1] is not mandatory
   - **Disclosed as**: Weakening the physical assumption (in modelSemantics)

3. **Mandatory natural evolution (intervals not containing 0)**
   - **Justification**: Tank always draining, irreversible processes
   - **Product rule**: Declared interval means itself; if 0 excluded, evolution cannot stutter
   - **Classification**: [EXACT] with respect to user declaration, [EXTENSION] relative to MEDIC baseline

4. **Additive composition for numeric multi-writer values**
   - **Justification**: Sum of heating/cooling effects is physically meaningful
   - **Product rule**: Multiple devices affecting same numeric value sum their impacts
   - **Not in paper**: MEDIC models individual devices, not multi-writer scenarios

5. **Structural rejection of conflicting discrete writers**
   - **Justification**: No meaningful composition rule for door_lock={locked, unlocked} with two writers assigning different values
   - **Product rule**: Refuse to model rather than guess at semantics
   - **Classification**: [REJECTED] - explicit non-support

6. **Purely exogenous discrete abstraction**
   - **Justification**: Weather, occupancy, external inputs not controlled by any device
   - **Product rule**: May take any declared value each step
   - **Classification**: [ABSTRACTION] - conservative over-approximation
   - **Disclosed**: Explicitly in modelSemantics and provenance

### [EXACT] - Faithful to User Declaration

1. **Declared interval means itself**: User writes [-3, 3], every integer from -3 to +3 is reachable
2. **Mandatory vs optional evolution**: Presence/absence of 0 in interval is semantically significant
3. **Read capability**: Reads=true means device can sense it; Reads=false means affect-only
4. **Device-controlled values evolve per device declaration**: Dynamics and guarded effects are authoritative

### [ABSTRACTION] - Deliberate Over-Approximation

Only two abstractions:

1. **Purely exogenous discrete values**: May take any declared value each step
   - **Rationale**: No device controls it, no physical evolution rule provided by user
   - **Conservative**: Permits all declared transitions, may produce counterexamples driven by uncontrolled external input
   - **Disclosed**: In modelSemantics, in provenance evolutionSummary, in frontend explanation

2. **Natural evolution intervals wider than [-1, 1]**: 
   - **Rationale**: User declaration overrides MEDIC baseline physical assumption
   - **Exact to declaration**: Not an abstraction of what user wrote
   - **Disclosed**: Noted as weakening the physical model constraint

### [REJECTED] - Explicitly Not Supported

1. **Multiple discrete writers with different assignments**: Both NuSMV and fuzz reject with named conflict
2. **Capability inference**: Reads field mandatory; omission never silently defaults
3. **Client-supplied scenes**: Verification/simulation read from Board only
4. **Affect-only values as rule conditions**: Refused at five enforcement boundaries

---

## Critical Findings

### Finding 1: Enum/Boolean Have No Paper Authority
**Implication**: Every semantic rule for discrete shared values must be justified by:
- User's mental model (what they naturally expect)
- Composition predictability (no surprising emergent behavior)
- Actionable counterexamples (user can understand and fix)
- Formal conservativeness (never claims safe when unsafe)

**Current Status**: Documented in shared-value-semantics.md with [EXT] tags. Exogenous discrete abstraction disclosed. Multi-writer rejection justified by lack of meaningful composition.

**Remaining Question**: Is "any declared value each step" the best model for purely exogenous discrete values? (Addressed in Phase 8)

### Finding 2: Interval Semantics Are [EXACT] Not [ABSTRACTION]
**Correction Needed**: Documentation sometimes describes wider intervals as "abstracting" MEDIC. Actually:
- MEDIC's [-1, 1] is "a physical assumption" (their words)
- User-declared [-5, 5] is exact to what user wrote
- Only noted as weakening one physical model assumption

**Action**: Clarify that intervals are [EXACT] to user declaration, [EXTENSION] in allowing user to override [-1, 1] baseline.

### Finding 3: Contemporaneous Effects Are [PAPER] Not Product Innovation
**Status**: Correctly cited as MEDIC Figure 2b. Implementation matches paper.

### Finding 4: Multi-Writer Composition Is [EXTENSION]
**Status**: Additive numeric composition and discrete conflict rejection both have no paper authority. Current documentation correctly marks as [EXT]. Justified by physical meaning (sum of effects) and rejection of ambiguous cases (discrete conflicts).

---

## Paper Conformance Score

| Aspect | Conformance | Notes |
|--------|-------------|-------|
| Integer variable model | ✓ Full | Numeric values are integers |
| Read/affect distinction | ✓ Full | Internal/Impacted maps to Reads/Affects |
| Contemporaneous effects | ✓ Full | DEFINE over current state |
| Natural evolution | ✓ Extended | Permits user override of [-1, 1] baseline |
| Trust propagation | ✓ Full | Implemented per paper |
| Attack modeling | ✓ Full | Boolean attacked per device |
| Discrete values | Extension | No paper coverage; must justify independently |
| Multi-writer cases | Extension | Paper models individual devices only |

## Conclusion

IoT-Verify correctly implements MEDIC where applicable and clearly marks extensions. The product does not misattribute extension semantics to the paper. Discrete value semantics require independent justification from user mental model and formal conservativeness, which is provided in shared-value-semantics.md.

**One documentation clarification needed**: Intervals wider than [-1, 1] should be described as [EXACT] to user declaration, not as an abstraction. The user wrote what they meant.
