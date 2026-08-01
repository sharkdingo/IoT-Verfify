# Discrete Value Semantics Deep Audit

## The Central Question

Is the current treatment of discrete (enum/boolean) shared values formally sound, faithful to user expectations, and productively actionable?

## Current Semantics

### 1. Purely Exogenous Discrete Values (No Device Writers)

**Implementation**: May take any declared value each step (nondeterministic choice)

**Classification**: [ABSTRACTION] - deliberately conservative

**Disclosure**: 
- modelSemantics field
- Provenance evolutionSummary
- Frontend SimulationTimeline annotation

**Examples**:
- Weather: {sunny, cloudy, rainy, stormy}
- Occupancy: {home, away}
- External mode: {auto, manual, emergency}

**Current Behavior in Traces**:
```
Step 1: weather=sunny
Step 2: weather=stormy  (arbitrary transition, no device caused it)
```

### 2. Device-Controlled Discrete Values (One Writer or Agreeing Writers)

**Implementation**: Device assignments only, no natural evolution

**Classification**: [EXACT] - device controls it per declaration

**Examples**:
- door_lock: {locked, unlocked} controlled by SmartLock device
- ac_mode: {off, cool, heat, fan} controlled by AC device

**Current Behavior in Traces**:
```
Step 1: door_lock=unlocked, SmartLock.mode=idle
Step 2: door_lock=locked, SmartLock.mode=locking  (device effect)
```

### 3. Conflicting Discrete Writers

**Implementation**: REJECTED - both NuSMV and fuzz refuse to model

**Classification**: [REJECTED] - no meaningful composition rule

**Example** (rejected):
- Device A: door_lock = locked when compromised
- Device B: door_lock = unlocked when fire_detected
- Conflict: Both could be active simultaneously

**Error message**: "Discrete value 'door_lock' has conflicting assignments: Device_A assigns 'locked', Device_B assigns 'unlocked'"

## Problems with Current Exogenous Abstraction

### Problem 1: Unintuitive Weather Behavior

**User Declaration**:
```json
{
  "Name": "weather",
  "Values": ["sunny", "cloudy", "rainy", "stormy"],
  "NaturalChangeRate": "stable"
}
```

**User Expectation**: Weather changes slowly; sunny → cloudy → rainy is plausible, but sunny → stormy in one step is extreme

**Current Model**: All transitions permitted equally:
- sunny → stormy ✓
- stormy → sunny ✓  
- sunny → sunny ✓

**Counterexample Issue**: Trace shows "attack succeeds because weather became stormy," but no device or physical process caused it - pure nondeterministic choice

### Problem 2: Unactionable Counterexamples

**Scenario**: Smart irrigation system

**Specification**: "Sprinklers must not run when weather=rainy"

**Verification Result**: VIOLATED

**Counterexample**:
```
Step 1: weather=sunny, sprinklers=off
Step 2: weather=rainy, sprinklers=on  (rule triggered by soil_moisture, ignores rain)
```

**User Question**: "Did my rule cause this or did the weather model?"

**Current Answer**: "The weather CAN become rainy each step (disclosed abstraction). Your rule should have checked weather."

**Actionability**: User learns their rule is incomplete, which is correct. But they may also ask "how likely is sunny→rainy?" which the model cannot answer.

### Problem 3: False Positives for Exclusive States

**User Declaration**:
```json
{
  "Name": "occupancy",
  "Values": ["home", "away", "vacation"]
}
```

**Real World**: Occupancy is stable for hours/days, not flickering

**Model**: Permits home → away → home → vacation in 4 steps

**Spec**: "When occupancy=vacation, door should be locked for 7+ consecutive steps"

**Counterexample**: occupancy flickers vacation for 1 step, door didn't lock, spec violated

**User Response**: "That's not realistic - I don't go on vacation for one timestep"

## Alternative Models Considered

### Alternative 1: Stable Until Updated

**Semantics**: Exogenous discrete value stays at current value unless explicitly updated by external event

**Implementation**: 
- Default transition: v' = v (stutter)
- Nondeterministic transitions only when triggered

**Pros**:
- Matches "weather doesn't change every second" intuition
- Reduces false positive rate
- Still conservative (permits any eventual change)

**Cons**:
- Requires defining "external event" trigger
- May miss attacks that rely on rapid environmental change
- Adds complexity to model

**Verdict**: Interesting but requires explicit external event model (out of scope for current product)

### Alternative 2: Explicit Transition System

**Semantics**: User declares allowed transitions, not just value set

**Example**:
```json
{
  "Name": "weather",
  "Values": ["sunny", "cloudy", "rainy", "stormy"],
  "Transitions": [
    ["sunny", "cloudy"],
    ["cloudy", "sunny"],
    ["cloudy", "rainy"],
    ["rainy", "cloudy"],
    ["rainy", "stormy"],
    ["stormy", "rainy"]
  ]
}
```

**Pros**:
- User controls realism
- Still conservative (they can add all transitions)
- Makes assumptions explicit

**Cons**:
- Significant UI/schema complexity
- Most users won't know what transitions to declare
- Doesn't solve "how likely" question

**Verdict**: Too complex for typical user; better suited to expert mode

### Alternative 3: Conservative Modes (Current + Flag)

**Semantics**: Keep current "any value" behavior, but let user opt into restrictions

**Example**:
```json
{
  "Name": "weather",
  "Values": ["sunny", "cloudy", "rainy", "stormy"],
  "EvolutionMode": "unrestricted"  // or "stable", "adjacent", "custom"
}
```

**Pros**:
- Backward compatible (default="unrestricted")
- Expert users can tighten model
- Beginner users get conservative check

**Cons**:
- Still requires defining what "adjacent" means for each domain
- Partial solution

**Verdict**: Possible incremental improvement, but doesn't fundamentally solve problem

### Alternative 4: Explicit Nondeterminism Disclosure (Current Approach)

**Semantics**: Model permits all transitions, disclosure makes this clear

**Implementation** (current):
- modelSemantics: "Purely exogenous discrete values may take any declared value each step"
- Provenance: "External input; may change to any declared value each step (deliberate abstraction)"
- Frontend annotation: "(external input)"

**Pros**:
- Formally sound (conservative)
- Explicit about what model does
- No user configuration needed
- Implementation complete

**Cons**:
- May produce unrealistic counterexamples
- User must understand abstraction to judge relevance
- "False positive" feel (though technically correct)

**Verdict**: Current approach - honest about model limitations

## Decision: Retain Current Approach with Improved Disclosure

### Rationale

1. **Formal Soundness**: Current model is conservative - never claims safe when unsafe

2. **User Education**: Problem is not the model but user understanding. If they declare exogenous discrete values, they must understand the model permits all transitions.

3. **Actionable Response**: When counterexample driven by exogenous discrete, user should:
   - Add rule conditions checking the exogenous value
   - Or convert to device-controlled if some device should manage it
   - Or accept that external uncontrolled inputs can cause spec violations

4. **No Silver Bullet**: Alternative models either:
   - Require complex user input (transition systems)
   - Make arbitrary realism assumptions (adjacent-only)
   - Or are equivalently abstract (stable-until-updated still needs trigger model)

5. **Product Consistency**: Current approach aligns with MEDIC's general philosophy: model what you know precisely, be conservative about what you don't

### Required Improvements

1. **Provenance evolutionSummary**: Already includes "may change to any declared value each step (deliberate abstraction)" ✓

2. **Frontend annotation**: SimulationTimeline shows "(external input)" for EXOGENOUS ✓

3. **modelSemantics disclosure**: Must explicitly state the abstraction ✓

4. **Documentation**: shared-value-semantics.md § 7 and § 10 clearly label as [ABSTRACTION] ✓

5. **User guidance**: When verification finds purely-exogenous-driven counterexample, suggest checking that value in rules

### Verification Tests

1. **Purely exogenous discrete can transition arbitrarily**: ✓ (by construction)
2. **Disclosure present in all three places**: ✓ (modelSemantics, provenance, UI)
3. **User guide documents this**: ✓ (shared-value-semantics.md)

## Discrete Writer Conflicts

### Current Approach: Structural Rejection

**Rule**: Two devices assigning different values to one discrete shared value → REJECTED

**Example**:
```
Device A Dynamics: mode=cool when temp>25
Device B Dynamics: mode=heat when temp<20
Conflict when temp in [20,25]? NO - guards mutually exclusive
Conflict when guards both true? YES - structural rejection doesn't analyze guards
```

**Rationale**: 
- Guard overlap analysis requires satisfiability checking
- Reachability analysis requires full state-space exploration
- Both are expensive and may be undecidable for complex guards
- Structural rejection is simple, fast, and never unsound

### Alternative: Guard Overlap Analysis

**Idea**: Reject only when guards can be simultaneously true

**Pros**:
- Permits more scenes
- Respects mutual exclusion

**Cons**:
- Requires SAT solver or conservative approximation
- Complex guard expressions may be undecidable
- Conservative approximation may still reject valid scenes
- Significant implementation complexity

**Verdict**: Not worth complexity for current product. Users can work around by making one device the coordinator.

### Alternative: Reachability-Based Rejection

**Idea**: Reject only when conflicting assignments reachable in same state

**Pros**:
- Most permissive
- Respects both guards and state evolution

**Cons**:
- Requires state-space exploration before generation
- Expensive, possibly exponential
- May still reject valid scenes if exploration incomplete

**Verdict**: Not feasible. This IS the verification problem we're trying to solve.

### Decision: Retain Structural Rejection

**Rationale**:
1. Simple, fast, deterministic
2. Never unsound (rejection is safe)
3. User workaround available: designate one device as coordinator
4. Complexity not justified by use case frequency

**Invariant preserved**: Device iteration order cannot affect verdict (no order-dependent resolution)

## Conclusion

**Discrete exogenous abstraction**: RETAIN with current disclosure
- Formally sound
- Explicitly disclosed in three places
- User-actionable (add rule conditions)
- No better alternative without complex user input

**Discrete writer conflicts**: RETAIN structural rejection
- Simple and deterministic
- Preserves order independence
- Workaround available
- Alternatives too complex

**Both behaviors**: Clearly marked [ABSTRACTION] and [REJECTED] in shared-value-semantics.md

**Status**: Semantically defensible, properly disclosed, no changes needed.
