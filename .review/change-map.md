# Cross-Round Change Map

## Round 1: Interval Semantics (Commit 282a576)

### Original Assumption
NaturalChangeRate [-3, 3] modeled as only three deltas: -3, 0, +3 (endpoints only).

### Why Changed
Endpoint-only under-approximation caused false SATISFIED verdicts. Real NuSMV proved:
- `AG (v = 5 -> AX v != 6)` returned TRUE (should be FALSE - interior value reachable)
- `AG (v = 5 -> AX v != 7)` returned TRUE (should be FALSE - interior value reachable)

The verifier claimed behavior impossible that the declaration permits - the one answer it must never give.

### Authoritative Rule After All Rounds
**[EXACT]** NaturalChangeRate [a, b] means the complete integer interval from a to b inclusive. Every integer delta in that range is admitted in the transition relation.

### Implementation Layers
1. **NaturalChangeRateParser.parseInterval()** - returns full List<Integer>
2. **SmvDeviceModuleBuilder** - emits complete disjunction for v'
3. **FuzzModel** - applies same full interval
4. **Frontend device.ts** - validates using same parser logic
5. **Test: NaturalChangeRateIntervalSoundnessTest** - proves old encoding fails, new succeeds

### Later Changes That Could Weaken
- None found. Interval generation is isolated in one parser utility.

### Falsifiable Test
`NaturalChangeRateIntervalSoundnessTest.testInteriorValuesAreReachable()` - verifies NuSMV reaches interior values with real NuSMV execution.

---

## Round 2: Contemporaneous Device Effects (Commit 517a912)

### Original Assumption
Device impact rate stored as state variable, so environment reads previous step's rate while device is in current mode. Switching AC on took two steps to affect temperature.

### Why Changed
MEDIC §3.1 Fig. 2b specifies: `v' - v ∈ [lower + env.D.v, upper + env.D.v]` for the SAME step. Device effect must be contemporaneous with its action.

Real NuSMV with AC initialized to cool mode:
- Old: `AG (temp = 30 -> AX temp <= 27)` = FALSE (only drift applied first step)
- New: `AG (temp = 30 -> AX temp <= 27)` = TRUE (cooling effect immediate)

### Authoritative Rule After All Rounds
**[MEDIC]** Device environment impact applies in the step the device acts, not one step later. Impact rate is a DEFINE over current device state, not a VAR lagging by one step.

### Implementation Layers
1. **SmvDeviceModuleBuilder** - impact rates as DEFINE, not VAR
2. **SmvMainModuleBuilder** - removed stale state variable emission
3. **FuzzModel** - reads current device mode for effect
4. **Test: NaturalChangeRateIntervalSoundnessTest** - includes first-step effect test

### Later Changes That Could Weaken
- None found. No code path recreates impact as state variable.

### Falsifiable Test
`NaturalChangeRateIntervalSoundnessTest.testFirstStepEffect()` - mutation test restores VAR encoding and requires it to fail.

---

## Round 3: Mandatory Natural Evolution (Commit bb87698)

### Original Assumption
Zero injected into every NaturalChangeRate interval to prevent stutter-caused false SATISFIED.

### Why Changed
Semantic faithfulness failure. Injecting 0 into [-4, -2] (mandatory drain) rewrites user's declaration:
- `AF (level = 0)` returned FALSE (should be TRUE - mandatory drain empties tank)
- `EG (level = 10)` returned TRUE (should be FALSE - cannot stay full)

User cannot act on counterexample showing behavior their declaration forbids.

### Authoritative Rule After All Rounds
**[EXACT]** NaturalChangeRate means exactly what the user wrote. If 0 is not in the declared interval, it is not in the transition relation. Intervals not containing 0 express mandatory evolution.

### Implementation Layers
1. **NaturalChangeRateParser** - does not inject 0
2. **SmvDeviceModuleBuilder** - uses raw interval
3. **FuzzModel** - samples from declared interval only
4. **Frontend device.ts** - describes mandatory vs optional evolution
5. **Reference model: EnvironmentRateSemanticsReferenceTest** - independent Scala FSM confirms NuSMV/fuzz agree

### Later Changes That Could Weaken
- None found. No fallback 0-injection path exists.

### Falsifiable Test
`EnvironmentRateSemanticsReferenceTest.testMandatoryDrain()` - three-way differential (NuSMV / fuzz / reference) on intervals not containing zero.

---

## Round 4: Board Authority (Commit 6e95a33)

### Original Assumption
POST /api/verify and /api/simulate accepted full scene in request body. Board was never consulted. Run history presented fabricated scenes as "this saved scene was checked."

### Why Changed
Proven exploitation: fresh account with empty board posted fabricated two-device scene, VIOLATED verdict persisted as genuine run history. Verdict was real, scene was not the user's.

### Authoritative Rule After All Rounds
**[EXACT]** The saved Board is the sole authority for verification and simulation. Request body carries only parameters (attack budget, privacy toggle). Scene is read server-side via `BoardDataConverter.getModelInputSnapshot()`.

### Implementation Layers
1. **VerificationServiceImpl.validateModelSemantics()** - reads from BoardStorageService
2. **SimulationServiceImpl.validateModelSemantics()** - reads from BoardStorageService
3. **VerificationRequestDto / SimulationRequestDto** - removed scene fields
4. **Frontend Board.vue** - removed scene serialization from request
5. **E2E test: testVerifyUsesAuthorityNotRequest()** - verifies empty request + board succeeds, fabricated request fails

### Later Changes That Could Weaken
- AI tools must use same BoardDataConverter path (checked in Phase 5)

### Falsifiable Test
Attempt to POST fabricated scene to /api/verify with non-empty board - must be rejected or ignored.

---

## Round 5: Read Capability Model (Commits 73e2c4a, eceaf2d, 523e063, 20593d8, 13fd433, fbf6104, 5537a59)

### Original Assumption
Capability implied by array membership: envVariables = rule source set, EnvironmentDomains = affect-only set. Boolean "does this device read it?" expressed as choosing between two array shapes.

### Why Changed
1. Deleting EnvironmentDomains would silently grant read to affect-only values
2. Two devices with different discrete assignments both passed validation (iteration-order dependent outcome)
3. Affect-only values used as rule conditions (semantic violation)
4. Five different enforcement points had different capability checks

### Authoritative Rule After All Rounds
**[EXACT]** InternalVariable with IsInside=false (shared) MUST carry explicit Reads boolean (no default). Missing Reads is rejected. Affect-only values (Reads=false) cannot be:
- Rule conditions
- Specification sources  
- Device local condition operands
- Assistant-created rule conditions
- Template validation operands

Enforcement at all five writer boundaries:
1. Frontend RuleEditor - disables affect-only values in condition dropdown
2. BoardSemanticValidator (AI tool gate) - rejects rules with affect-only conditions
3. SmvGenerator validation - rejects at model generation
4. Template validation - rejects at template persist
5. Assistant tool schemas - omit affect-only values from condition enums

### Implementation Layers
1. **device-template-schema.json** - Reads field required when IsInside=false
2. **DeviceSmvDataFactory** - enforces Reads presence
3. **RuleConditionValidator** (multiple call sites) - checks capability
4. **Frontend RuleEditor** - filters dropdown
5. **AI tool schemas** - condition enums computed from readable values only
6. **Template validator** - standalone validation enforces same rule

### Later Changes That Could Weaken
Round 6 authorship changes must preserve capability checks (verified below).

### Falsifiable Test
1. Template with missing Reads must be rejected at persist
2. Rule with affect-only condition must fail in UI, AI, and generation
3. Device order swap must produce identical verdict (order independence)

---

## Round 6: Unified Authorship Semantics (Commit eceaf2d, 3ff0b56)

### Original Assumption
Shared-value semantics described but not fully implemented. Fuzz used first-writer-wins for discrete conflicts.

### Why Changed
Re-review against MEDIC §3.1 found paper scope narrower than assumed:
- MEDIC defines only integer variables
- Enum/boolean are pure product extensions with no paper authority
- Two devices assigning different discrete values: NuSMV rejected, fuzz silently picked first writer
- Violation of Invariant 11: "NuSMV and bounded explorer implement one transition relation"

### Authoritative Rule After All Rounds
**[MEDIC for numeric, EXTENSION for discrete]**

Authorship categories:
1. **EXOGENOUS**: No device writes it
   - Numeric: natural evolution only (exact per MEDIC)
   - Discrete: may take any declared value each step (**[ABSTRACTION]** - disclosed in modelSemantics)
   
2. **DEVICE_CONTROLLED**: Exactly one device writes it (or multiple agree on assignments)
   - All types: device effect plus natural evolution
   
3. **COMPOSED**: Multiple devices write it (numeric only)
   - Additive composition: sum of effects plus natural evolution
   
4. **REJECTED**: Multiple devices assign different discrete values
   - Both NuSMV and fuzz reject with named conflict

### Implementation Layers
1. **shared-value-semantics.md** - authoritative semantic document
2. **SmvModelValidator** - rejects discrete conflicts
3. **FuzzModel** - rejects discrete conflicts (fixed in 3ff0b56)
4. **EnvironmentProvenanceCollector** - categorizes authorship for explanations
5. **Frontend SimulationTimeline** - displays category-specific explanations

### Later Changes That Could Weaken
Provenance must reflect these categories accurately (verified in Phase 4).

### Falsifiable Test
1. Conflicting discrete writers rejected by both engines
2. Order-swap produces identical verdict (invariant 10)
3. NuSMV and fuzz agree on transition relation (invariant 11)

---

## Round 7: Model Snapshot and Provenance (Recent commits)

### Original Assumption
Verification/simulation results relied on current Board state for explanation.

### Why Changed
Historical runs became unexplainable after Board edits. User asks "why did this counterexample happen?" but current Board no longer matches the verified scene.

### Authoritative Rule After All Rounds
**[EXACT]** Every verification/simulation run captures immutable ModelRunSnapshotDto including:
- Device/rule/spec counts
- Template fingerprints  
- Per-value EnvironmentValueProvenanceDto:
  - Authorship category (EXOGENOUS / DEVICE_CONTROLLED / COMPOSED)
  - Semantics tag (EXACT / ABSTRACTION)
  - Domain (bounds, rate, or discrete values)
  - Writers (device-controlled and composed)
  - Readers (capability tracking)
  - Evolution summary (human-readable)

Snapshot is frozen at run time, persisted in modelSnapshotJson, retrieved for history, and used for trace explanation independently of current Board.

### Implementation Layers
1. **EnvironmentProvenanceCollector.collectEnvironmentProvenance()** - captures at model generation
2. **ModelRunSnapshotDto.environmentProvenance** - persisted structure
3. **VerificationServiceImpl/SimulationServiceImpl.captureDeviceModelSnapshot()** - attaches to snapshot
4. **VerificationTaskPo.modelSnapshotJson / SimulationTaskPo.modelSnapshotJson** - TEXT column persistence
5. **Frontend SimulationTimeline.vue** - renders provenance annotations
6. **i18n keys** - app.traceVisualization.provenance.* translations

### Later Changes That Could Weaken
AI tools reading historical runs must use frozen snapshot, not current Board (check in Phase 5).

### Falsifiable Test
1. Run verification, edit Board, reload history - explanation unchanged
2. Provenance JSON round-trips through persistence
3. All authorship categories represented correctly in UI

---

## Cross-Round Invariants (Must Hold After All Rounds)

1. **Interval completeness**: Every integer in [a, b] is reachable
2. **Contemporaneous effects**: Device impact applies same step as mode change
3. **Exact semantics**: Declared interval means itself, no silent 0-injection
4. **Board authority**: Scene read from Board, not request body
5. **Explicit capability**: Reads field mandatory, affect-only values not usable in conditions
6. **Order independence**: Device iteration order cannot change verdict
7. **Engine agreement**: NuSMV and fuzz implement one transition relation
8. **Conflict rejection**: Discrete values with different writers rejected by both engines
9. **Frozen history**: Historical explanations independent of current Board
10. **Provenance completeness**: Every value's evolution rule captured and explainable

## Remaining Semantic Questions (To Audit)

1. **Discrete exogenous abstraction**: Is "any declared value each step" the right model for weather/occupancy? Alternative: stable-until-updated, transition system, explicit nondeterminism modes?

2. **Discrete conflict rejection**: Structural rejection even when guards may be mutually exclusive. Could guard-overlap or reachability analysis permit safe composition?

3. **AI tool capability enforcement**: Do all AI-created templates/rules respect the same capability and authorship rules as the UI?

4. **Provenance display scope**: Currently only SimulationTimeline shows provenance. Should VerificationResult counterexamples also display per-transition causation?
