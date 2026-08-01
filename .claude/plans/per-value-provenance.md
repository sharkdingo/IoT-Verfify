# Per-value provenance for self-explanatory counterexamples

## Problem

A historical counterexample cannot explain why a specific shared value changed in a specific transition. The current `modelSemantics.environmentEvolutionEffects` is a global constant set disclosed before a run, not per-value provenance. A user who skips the Environment Pool panel can meet a weather-driven counterexample without understanding why the value changed.

## Requirements

1. **Frozen snapshot must be self-explanatory.** A historical run must not derive explanations from the current Board.
2. **Per-value authorship.** The snapshot must distinguish exogenous values, device-controlled values, and composed values.
3. **Abstraction vs exact semantics.** The snapshot must mark whether evolution is user-declared or a product abstraction.
4. **Transition justification.** Every trace transition must be attributable to either a user declaration or a disclosed abstraction.
5. **Progressive disclosure in UI.** Concise inline explanation with access to the precise rule or abstraction.
6. **Frontend and AI alignment.** Both paths use the same frozen snapshot, not live Board derivation.

## Domain model

From `shared-value-semantics.md`:

**Value types:**
- Numeric: `LowerBound`/`UpperBound` + optional `NaturalChangeRate`
- Discrete: `Values` list (enum or boolean)

**Authorship categories** (§6-7):
- **Purely exogenous:** no device declares it in `ImpactedVariables`; may take any declared value each step (ABSTRACTION)
- **Device-controlled:** at least one device declares `ImpactedVariables`; stutter when no effect applies (EXACT)
- **Composed:** multiple devices declare `ImpactedVariables`; summed for numeric, last-writer-wins for discrete (EXACT)

**Per-value metadata needed:**
- Identity: `name`, `type` (NUMERIC | DISCRETE_ENUM | DISCRETE_BOOLEAN)
- Domain: numeric bounds + rate, or discrete values list
- Authorship: `EXOGENOUS | DEVICE_CONTROLLED | COMPOSED`
- Writers: list of `{deviceId, deviceVarName, templateName}` that declare `ImpactedVariables` for this value
- Read capability: list of `{deviceId, deviceVarName}` that declare `Reads=true` for this value
- Natural evolution: the `NaturalChangeRate` if numeric and declared
- Semantics tag: `EXACT | ABSTRACTION`

## Design

### 1. New DTO: `EnvironmentValueProvenanceDto`

```java
package cn.edu.nju.Iot_Verify.dto.model;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class EnvironmentValueProvenanceDto {
    
    public enum ValueType {
        NUMERIC,
        DISCRETE_ENUM,
        DISCRETE_BOOLEAN
    }
    
    public enum AuthorshipCategory {
        /** No device affects it; may take any value each step (deliberate abstraction). */
        EXOGENOUS,
        /** At least one device affects it; stutters when no effect applies (exact). */
        DEVICE_CONTROLLED,
        /** Multiple devices affect it; effects are composed (exact). */
        COMPOSED
    }
    
    public enum SemanticsTag {
        /** Means what the user declared, or what the device template explicitly states. */
        EXACT,
        /** Deliberate conservative over-approximation disclosed in modelSemantics. */
        ABSTRACTION
    }
    
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceWriter {
        private String deviceId;
        private String deviceVarName;
        private String templateName;
        private ModelTokenSource templateSource;
    }
    
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceReader {
        private String deviceId;
        private String deviceVarName;
    }
    
    /** User-facing environment variable name. */
    private String name;
    
    private ValueType type;
    
    /** For numeric: bounds and optional rate. */
    private Integer lowerBound;
    private Integer upperBound;
    private String naturalChangeRate;
    
    /** For discrete: the declared values. */
    private List<String> values;
    
    private AuthorshipCategory authorship;
    
    /** Devices that declare ImpactedVariables for this value. */
    private List<DeviceWriter> writers;
    
    /** Devices that declare Reads=true for this value. */
    private List<DeviceReader> readers;
    
    /** EXACT when user-declared; ABSTRACTION for purely exogenous discrete. */
    private SemanticsTag semantics;
    
    /** Human-readable explanation of the evolution rule. */
    private String evolutionSummary;
}
```

### 2. Extend `ModelRunSnapshotDto`

Add:
```java
/** Per-value provenance for every environment variable in this run. */
private List<EnvironmentValueProvenanceDto> environmentProvenance;
```

### 3. Capture provenance at generation time

In `SmvMainModuleBuilder` or a new `EnvironmentProvenanceCollector`:

```java
public List<EnvironmentValueProvenanceDto> collectEnvironmentProvenance(
        List<BoardEnvironmentVariableDto> environmentVariables,
        List<DeviceVerificationDto> devices,
        Map<String, DeviceSmvData> deviceSmvMap) {
    
    List<EnvironmentValueProvenanceDto> result = new ArrayList<>();
    
    for (BoardEnvironmentVariableDto envVar : environmentVariables) {
        String varName = envVar.getName();
        
        // Find the canonical domain declaration from any device that declares this value
        EnvironmentDomain domain = findEnvironmentDomain(varName, devices, deviceSmvMap);
        if (domain == null) continue;
        
        // Collect writers
        List<EnvironmentValueProvenanceDto.DeviceWriter> writers = new ArrayList<>();
        for (DeviceVerificationDto dev : devices) {
            DeviceSmvData smv = deviceSmvMap.get(dev.getVarName());
            if (smv != null && smv.getImpactedVariables() != null 
                    && smv.getImpactedVariables().contains(varName)) {
                writers.add(EnvironmentValueProvenanceDto.DeviceWriter.builder()
                        .deviceId(dev.getId())
                        .deviceVarName(dev.getVarName())
                        .templateName(smv.getTemplateName())
                        .templateSource(ModelTokenSource.fromDefaultTemplate(dev.getDefaultTemplate()))
                        .build());
            }
        }
        
        // Collect readers
        List<EnvironmentValueProvenanceDto.DeviceReader> readers = new ArrayList<>();
        for (DeviceVerificationDto dev : devices) {
            DeviceSmvData smv = deviceSmvMap.get(dev.getVarName());
            if (smv != null && smv.getReadsSharedVariable(varName)) {
                readers.add(EnvironmentValueProvenanceDto.DeviceReader.builder()
                        .deviceId(dev.getId())
                        .deviceVarName(dev.getVarName())
                        .build());
            }
        }
        
        // Determine authorship
        AuthorshipCategory authorship;
        SemanticsTag semantics;
        if (writers.isEmpty()) {
            authorship = AuthorshipCategory.EXOGENOUS;
            semantics = domain.isDiscrete() ? SemanticsTag.ABSTRACTION : SemanticsTag.EXACT;
        } else if (writers.size() == 1) {
            authorship = AuthorshipCategory.DEVICE_CONTROLLED;
            semantics = SemanticsTag.EXACT;
        } else {
            authorship = AuthorshipCategory.COMPOSED;
            semantics = SemanticsTag.EXACT;
        }
        
        String evolutionSummary = buildEvolutionSummary(domain, authorship, writers, readers);
        
        result.add(EnvironmentValueProvenanceDto.builder()
                .name(varName)
                .type(determineValueType(domain))
                .lowerBound(domain.getLowerBound())
                .upperBound(domain.getUpperBound())
                .naturalChangeRate(domain.getNaturalChangeRate())
                .values(domain.getValues())
                .authorship(authorship)
                .writers(writers)
                .readers(readers)
                .semantics(semantics)
                .evolutionSummary(evolutionSummary)
                .build());
    }
    
    return result;
}
```

### 4. Persist provenance with verification/simulation results

In `VerificationServiceImpl.verify()` and `SimulationServiceImpl.simulate()`, after NuSMV generation:

```java
List<EnvironmentValueProvenanceDto> provenance = 
    provenanceCollector.collectEnvironmentProvenance(
        board.getEnvironmentVariables(), devices, deviceSmvMap);

ModelRunSnapshotDto snapshot = ModelRunSnapshotDto.captured(...)
    .toBuilder()
    .environmentProvenance(provenance)
    .build();
```

Serialize `environmentProvenance` into `TraceDto.modelSnapshot` and `SimulationResultDto.modelSnapshot`.

### 5. Frontend provenance type

In `frontend/src/types/modelSemantics.ts`:

```typescript
export type ValueType = 'NUMERIC' | 'DISCRETE_ENUM' | 'DISCRETE_BOOLEAN'
export type AuthorshipCategory = 'EXOGENOUS' | 'DEVICE_CONTROLLED' | 'COMPOSED'
export type SemanticsTag = 'EXACT' | 'ABSTRACTION'

export interface DeviceWriter {
  deviceId: string
  deviceVarName: string
  templateName: string
  templateSource: 'BUNDLED' | 'CUSTOM' | 'UNKNOWN'
}

export interface DeviceReader {
  deviceId: string
  deviceVarName: string
}

export interface EnvironmentValueProvenance {
  name: string
  type: ValueType
  lowerBound?: number | null
  upperBound?: number | null
  naturalChangeRate?: string | null
  values?: string[]
  authorship: AuthorshipCategory
  writers: DeviceWriter[]
  readers: DeviceReader[]
  semantics: SemanticsTag
  evolutionSummary: string
}

export interface ModelRunSnapshot {
  // existing fields...
  environmentProvenance?: EnvironmentValueProvenance[]
}
```

### 6. Counterexample UI: progressive disclosure

In `SimulationTimeline.vue`, extend `environmentVariableTitle()`:

```typescript
const getProvenanceForVariable = (name: string): EnvironmentValueProvenance | null => {
  return props.modelSnapshot?.environmentProvenance?.find(p => p.name === name) || null
}

const environmentVariableTitle = (name: string, value: string) => {
  const previous = getPreviousEnvValue(name)
  const displayName = formatEnvironmentModelToken(name, name)
  const displayValue = formatEnvironmentModelToken(name, value)
  
  const provenance = getProvenanceForVariable(name)
  
  let title = previous === undefined || previous === value
    ? `${displayName}: ${displayValue}`
    : `${displayName}: ${formatEnvironmentModelToken(name, previous)} -> ${displayValue}`
  
  if (provenance && previous !== undefined && previous !== value) {
    // Add concise cause
    if (provenance.authorship === 'EXOGENOUS' && provenance.semantics === 'ABSTRACTION') {
      title += ` (external input, may change freely)`
    } else if (provenance.authorship === 'DEVICE_CONTROLLED') {
      const writer = provenance.writers[0]
      title += ` (affected by ${formatDeviceLabel(writer.deviceVarName)})`
    } else if (provenance.authorship === 'COMPOSED') {
      title += ` (affected by ${provenance.writers.length} devices)`
    }
  }
  
  return title
}
```

Add a detail panel or tooltip that shows `provenance.evolutionSummary`, the full writers list, and the semantics tag.

### 7. AI tool alignment

In AI tool result builders (e.g., `GetTraceToolPresenter`, `GetSimulationTraceToolPresenter`), include provenance in the formatted trace so the assistant can explain transitions:

```java
if (snapshot.getEnvironmentProvenance() != null) {
    sb.append("\n\n## Environment value semantics\n\n");
    for (EnvironmentValueProvenanceDto prov : snapshot.getEnvironmentProvenance()) {
        sb.append(String.format("- **%s** (%s, %s): %s\n",
                prov.getName(),
                prov.getAuthorship(),
                prov.getSemantics(),
                prov.getEvolutionSummary()));
    }
}
```

The assistant will then attribute transitions to either user declarations or disclosed abstractions rather than inventing causes.

### 8. Tests

**Backend:**
- `EnvironmentProvenanceCollectorTest`: numeric/discrete, exogenous/device-controlled/composed cases
- `ModelRunSnapshotPersistenceTest`: provenance survives JSON round-trip
- `VerificationServiceProvenanceTest`: provenance captured and frozen at verification time
- `SimulationServiceProvenanceTest`: same for simulation
- `TraceReplayProvenanceTest`: historical trace uses frozen provenance, not current Board

**Frontend:**
- `modelSemantics.spec.ts`: provenance type guards and helpers
- `SimulationTimeline.spec.ts`: provenance-aware title rendering
- Contract test: flattening provenance to a global constant fails

**E2E:**
- Create a scene with one exogenous value and one device-controlled value
- Verify the property, get a counterexample
- Check that the exogenous transition shows "external input" and the device-controlled transition names the device
- Modify the Board (delete the device), reload the historical trace
- Verify the explanation still names the deleted device from the frozen snapshot

### 9. Live-AI test correction

**Current test 2 ambiguity:** It asserts `rule_list`, count delta, and undo, but never `executionStatus`. It passes on `PARTIAL` when `manage_rule` succeeds but response writing fails. This is valid if the test's purpose is mutation+journal correctness.

**Fix:**
1. Rename test 2 to `assistant-rule-mutation-journalled.spec.ts` and document that `PARTIAL` is acceptable.
2. Add a new `assistant-terminal-completion.spec.ts` that requires `COMPLETED`.
3. Add deterministic degradation tests:
   - Mock provider returning 503 → verify `FAILED` and error message
   - Mock provider succeeding for tool call, failing for response → verify `PARTIAL` and tool result present
4. Keep the real-endpoint test but clarify it proves integration when the provider is healthy, not provider stability.

## Implementation phases

1. **Backend provenance capture:** `EnvironmentValueProvenanceDto`, collector, snapshot persistence
2. **Frontend types and rendering:** progressive disclosure in counterexample UI
3. **AI tool alignment:** include provenance in formatted traces
4. **Tests:** unit, contract, E2E, live-AI correction
5. **Verification:** clean stacks, commit, push, CI, independent review

## Open questions

None — the domain model is authoritative, the snapshot contract is mutable, and the requirement is explicit.
