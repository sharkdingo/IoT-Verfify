# Cross-Round Pre-Release Review Plan

## Scope
Comprehensive audit of the accumulated semantic model across all implementation rounds, from pre-domain-model baseline through current HEAD.

## Key Questions to Answer
1. Does one coherent formal model exist across all layers?
2. Are paper citations accurate and product extensions clearly marked?
3. Is "what the user sees" identical to "what gets verified"?
4. Do AI tools use the same authoritative model as the frontend?
5. Is provenance complete, persistent, and self-explanatory?
6. Have previous fixes held across subsequent rounds?

## Execution Phases

### Phase 1: Change Map Reconstruction [IN PROGRESS]
- [x] Identify key semantic commits
- [x] Map interval semantics changes
- [x] Map contemporaneous effects changes
- [x] Map Board authority changes
- [x] Map capability model changes
- [x] Map discrete writer conflict handling
- [ ] Map natural evolution semantics
- [ ] Map shared value ownership model
- [ ] Complete cross-round change matrix

### Phase 2: Paper Authority Audit
- [ ] Read MEDIC §3.1 directly (not summaries)
- [ ] Identify [PAPER] vs [EXTENSION] boundaries
- [ ] Verify numeric variable paper conformance
- [ ] Audit enum/boolean extension justification
- [ ] Check discrete exogenous abstraction disclosure
- [ ] Verify conflict rejection rationale

### Phase 3: Semantic Chain Audit (Frontend → Backend → Verification)
- [ ] Audit device template schema
- [ ] Audit frontend configuration UI
- [ ] Audit Board serialization
- [ ] Audit model snapshot capture
- [ ] Audit NuSMV generation
- [ ] Audit fuzz generation
- [ ] Audit trace presentation
- [ ] Verify frontend/backend alignment

### Phase 4: Provenance Contract Audit
- [ ] Examine provenance DTO completeness
- [ ] Verify collection at snapshot time
- [ ] Verify persistence in modelSnapshotJson
- [ ] Verify retrieval for history
- [ ] Verify frontend display
- [ ] Test frozen snapshot independence
- [ ] Verify verification vs simulation consistency

### Phase 5: AI Tool Semantic Audit
- [ ] Audit environment management tool
- [ ] Audit template creation tools
- [ ] Audit verification/simulation tools
- [ ] Audit trace explanation tools
- [ ] Verify capability enforcement
- [ ] Verify Board authority usage
- [ ] Check for stale assumptions

### Phase 6: Cross-Round Regression Check
- [ ] Verify interval endpoints don't return
- [ ] Verify one-step-late effects don't return
- [ ] Verify client scenes don't become authoritative
- [ ] Verify missing capabilities don't grant access
- [ ] Verify device order independence holds
- [ ] Verify NuSMV/fuzz agreement holds

### Phase 7: Evidence Strengthening
- [ ] Run clean backend tests
- [ ] Run clean frontend tests
- [ ] Run NuSMV differential tests
- [ ] Run mutation tests for historical bugs
- [ ] Run full E2E with real services
- [ ] Verify CI Fast/Full routing
- [ ] Check Live AI integration

### Phase 8: Final Cross-Review
- [ ] Independent frontend→verification path check
- [ ] Independent AI tool path check
- [ ] Independent history/replay path check
- [ ] Discrete exogenous behavior review
- [ ] Discrete writer conflict review
- [ ] Final semantic consistency check

## Current Status
Working on Phase 1: Change map reconstruction
Next: Complete natural evolution and ownership analysis
