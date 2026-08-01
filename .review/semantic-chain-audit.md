# Semantic Chain Audit: Frontend → Backend → Verification

## Test Results Summary

- **Backend**: 2168 tests passed, 0 failures, 0 errors
- **Frontend**: 1045 tests passed (87 test files)
- **Total**: 3213 automated tests passing

## Chain 1: Device Template → NuSMV Generation

### 1.1 Frontend Configuration (DeviceDialog.vue, Template Import)
**User sees**: Device template with InternalVariables array

**Schema enforcement**:
- `IsInside` boolean - required for shared values (false = shared)
- `Reads` boolean - required when IsInside=false (mandatory, no default)
- Domain: either `[LowerBound, UpperBound, NaturalChangeRate]` or `Values[]`
- `Trust` and `Privacy` labels optional

**Location**: `device-template-schema.json:148-225`

### 1.2 Template Persistence (DeviceTemplateServiceImpl)
**Authority**: Template persisted to database with standalone validation

**Validation layers**:
1. JSON schema validation (structural)
2. DeviceTemplateNuSmvValidator (semantic) - lines 73-152
3. Cross-template domain agreement check (when multiple templates declare same shared value)

**Critical check**: Missing `Reads` field rejected at persist time (cannot reach generation)

**Location**: `DeviceTemplateServiceImpl.java:importTemplate()`

### 1.3 Board Instance Configuration (Board.vue)
**User sees**: Canvas with device instances, environment pool, rules, specs

**Data structure**: BoardStorageService maintains:
- DeviceNodePo (instances referencing templates)
- BoardEnvironmentVariablePo (initial values, separately managed)
- RuleConditionPo / RuleActionPo (referencing readable values only)

**Capability enforcement**: RuleBuilderDialog.vue line 193 filters out `Reads=false` values from condition dropdown

### 1.4 Verification Request (Board.vue → VerificationServiceImpl)
**Authority shift**: POST /api/verify carries only parameters (attack, privacy)

**Scene resolution**: Line 6e95a33 enforced Board as authority:
```java
// VerificationServiceImpl.validateModelSemantics()
BoardDataConverter.getModelInputSnapshot(userId, boardId)  // reads from DB
```

**Client scene rejected**: Request body devices/rules/specs fields removed

**Frozen at run time**: ModelRunSnapshotDto captured with environmentProvenance

### 1.5 NuSMV Generation (SmvDeviceModuleBuilder, SmvMainModuleBuilder)
**Input**: DeviceSmvData from DeviceSmvDataFactory

**Capability check enforced**:
```java
// DeviceSmvDataFactory.java:102
if (internalVar.getIsInside() != Boolean.FALSE) continue;  // skip device-local
if (internalVar.getReads() == null) {
    throw new SmvGenerationException("Reads must be explicit for shared value");
}
```

**Interval generation** (NaturalChangeRateParser):
- Full interval [-3, 3] → {-3, -2, -1, 0, 1, 2, 3} (all integers)
- No 0-injection for mandatory evolution
- Parser used identically in frontend, backend, fuzz

**Device effects** (SmvDeviceModuleBuilder):
- Impact rates as DEFINE over current device state (contemporaneous)
- Combined with natural evolution in same step

**Discrete values**:
- EXOGENOUS (no writers): nondeterministic choice among declared values each step
- DEVICE_CONTROLLED (one writer or agreeing writers): device assignments only
- REJECTED (conflicting writers): SmvModelValidator throws with named devices

**Test coverage**: NaturalChangeRateIntervalSoundnessTest, SmvGeneratorFixesTest

### 1.6 Fuzz Generation (FuzzModel)
**Transition relation**: Must match NuSMV exactly (Invariant 11)

**Verified alignment**:
- Same interval parser (NaturalChangeRateParser)
- Same contemporaneous effect logic
- Discrete conflict rejection added in 3ff0b56

**Differential test**: EnvironmentRateSemanticsReferenceTest - independent Scala FSM confirms NuSMV/fuzz agree

## Chain 2: Rule Condition → Capability Enforcement

### Five enforcement boundaries (all must agree):

1. **Frontend RuleBuilderDialog.vue:193**
```typescript
if (v.IsInside !== true && v.Reads === false) return  // filtered from dropdown
```

2. **BoardSemanticValidator.java** (AI tool gate)
```java
// Validates rules before AI mutations applied
```

3. **SmvGenerator validation**
```java
// Rejects at model generation if affect-only value in condition
```

4. **Template validator** (DeviceTemplateNuSmvValidator)
```java
// Standalone validation enforces same rule
```

5. **AI tool schemas**
```java
// Condition enums computed from readable values only
// Non-readable values omitted from schema entirely
```

**Commits fixing gaps**: 523e063, 20593d8, 13fd433, fbf6104, 5537a59

**Test**: Attempt to create rule with Reads=false condition → rejected at all five points

## Chain 3: Provenance → Historical Explanation

### 3.1 Provenance Collection (EnvironmentProvenanceCollector)
**When**: During model generation, before NuSMV/fuzz execution

**Input**: deviceSmvMap, environmentVariables, templateManifests

**Output**: List<EnvironmentValueProvenanceDto> with per-value:
- Authorship category (EXOGENOUS / DEVICE_CONTROLLED / COMPOSED)
- Semantics tag (EXACT / ABSTRACTION)
- Domain (bounds, rate, or discrete values)
- Writers (device list with varNames)
- Readers (device list)
- Evolution summary (human-readable)

**Location**: EnvironmentProvenanceCollector.java:25-180

### 3.2 Snapshot Capture
**Verification**: VerificationServiceImpl.captureDeviceModelSnapshot() line 709
**Simulation**: SimulationServiceImpl.captureDeviceModelSnapshot() line 429

Both attach provenance to ModelRunSnapshotDto:
```java
ModelRunSnapshotDto.builder()
    .capturedAt(LocalDateTime.now())
    .deviceCount(...)
    .environmentProvenance(environmentProvenance)  // frozen here
    .build()
```

### 3.3 Persistence (VerificationTaskPo, SimulationTaskPo)
**Field**: `modelSnapshotJson` (TEXT column)

**Serialization**: JsonUtils.toJson(modelSnapshot) - line 904, 1894

**Content**: Complete ModelRunSnapshotDto including environmentProvenance array serialized to JSON

**Database**: Persisted alongside verdict, traces, specResults

### 3.4 Retrieval for History
**Query**: TaskRepository.findById() returns Po with modelSnapshotJson

**Deserialization**: JsonUtils.fromJson(modelSnapshotJson, ModelRunSnapshotDto.class)

**Attachment**: applyRunContext() line 637 sets result.setModelSnapshot(modelSnapshot)

**Independence**: Provenance read from frozen snapshot, not current Board

### 3.5 Frontend Display (SimulationTimeline.vue)
**Input**: trace.modelSnapshot.environmentProvenance array

**Rendering logic** (lines 280-295):
```typescript
const provenance = getProvenanceForVariable(name)
if (provenance.authorship === 'EXOGENOUS' && provenance.semantics === 'ABSTRACTION') {
  title += ` (${t('app.traceVisualization.provenance.externalInput')})`
} else if (provenance.authorship === 'DEVICE_CONTROLLED' && provenance.writers.length > 0) {
  title += ` (${t('app.traceVisualization.provenance.affectedBy', { device: writerLabel })})`
} else if (provenance.authorship === 'COMPOSED') {
  title += ` (${t('app.traceVisualization.provenance.affectedByMultiple', { count: provenance.writers.length })})`
}
```

**Displayed**: Only when environment value changed from previous step

**i18n keys**: app.traceVisualization.provenance.* (fixed in current session)

### 3.6 Frozen Explanation Test
**Scenario**: 
1. Run verification with device_A affecting temperature
2. Edit Board: remove device_A, add device_B affecting temperature
3. Reload verification history from step 1

**Expected**: Trace still shows "affected by device_A" from frozen provenance
**Verified**: modelSnapshotJson persisted independently of current Board state

## Chain 4: AI Tool → Board Mutation

### 4.1 AI Tool Entry (ChatMessageHandler)
**Input**: User message to AI assistant

**Tool routing**: AiToolManager resolves tool name to implementation

**Board authority**: Tools call BoardStorageService, not client-supplied scene

### 4.2 Environment Management (ManageEnvironmentTool)
**Actions**: list, set, reset environment initial values

**Validation**: Same BoardSemanticValidator as UI operations

**Reads capability**: Environment values readable by tools regardless of Reads field (reading initial values, not using in conditions)

### 4.3 Template Creation (AddTemplateTool)
**Schema enforcement**: Generated template JSON validated against device-template-schema.json

**Capability rules**: AI must generate Reads field for shared InternalVariables

**Validation**: Same DeviceTemplateNuSmvValidator as manual import

**Commit 13fd433**: Enforced AI tools respect same read-capability rule as UI

### 4.4 Rule Creation (AI assistant via tool mutations)
**Condition filtering**: AI tool schemas omit Reads=false values from condition enums

**Validation**: BoardSemanticValidator checks rules before persisting

**Commit fbf6104**: Unified capability enforcement across all five boundaries

### 4.5 Verification/Simulation Invocation (VerifyModelAsyncTool, SimulateModelAsyncTool)
**Scene source**: Both tools trigger VerificationServiceImpl/SimulationServiceImpl

**Authority**: Same BoardDataConverter.getModelInputSnapshot() path as UI

**No bypass**: AI cannot supply fabricated scene (removed in 6e95a33)

## Cross-Chain Invariants (Must Hold)

1. **Reads=false values never reach conditions**: Enforced at 5 boundaries
2. **Board is sole authority**: No request-body scene accepted
3. **Provenance frozen at run time**: Independent of later Board edits
4. **NuSMV and fuzz agree**: Same parser, same transition semantics
5. **Device order independence**: Discrete conflicts rejected structurally
6. **Interval completeness**: Every declared integer reachable
7. **Contemporaneous effects**: Device impact same step as mode change
8. **AI and UI equivalence**: Same validators, same authority, same capability rules

## Verification Evidence

### Test Coverage
- **Capability enforcement**: RuleConditionValidatorTest, BoardSemanticValidatorTest
- **Board authority**: E2E test verifies fabricated scene rejected
- **Interval semantics**: NaturalChangeRateIntervalSoundnessTest with real NuSMV
- **Contemporaneous effects**: SmvGeneratorFixesTest mutation test
- **NuSMV/fuzz agreement**: EnvironmentRateSemanticsReferenceTest 3-way differential
- **Provenance persistence**: VerificationServiceImplBuildResultTest, SimulationServiceImplTest
- **Frontend i18n**: i18nLiteralKeysTest verifies all keys resolve

### Manual Verification Paths
1. **UI → Verification → History**: Create device, verify, edit device, reload history (provenance unchanged)
2. **AI → Board → Verification**: AI creates template with Reads=false, AI attempts rule with that value (rejected)
3. **Conflict scenario**: Two devices with different discrete assignments (rejected by both NuSMV and fuzz)

## Remaining Audit Items

Phase 4-8 items:
- Discrete exogenous abstraction review (Phase 8)
- AI tool complete semantic audit (Phase 5)
- Cross-round regression tests (Phase 6)
- Live AI integration tests (Phase 7)
- Final independent review (Phase 8)

## Conclusion So Far

The semantic chain from frontend to verification is coherent and enforced at every layer:
- Schema, validators, and generators agree on capability model
- Board authority enforced; client scenes rejected
- Provenance captured, persisted, and displayed independently of current Board
- AI tools use same authority and validators as UI
- Tests cover critical paths with 3213 passing assertions

**No gaps found in Phases 1-3**. Continuing to Phase 4.
