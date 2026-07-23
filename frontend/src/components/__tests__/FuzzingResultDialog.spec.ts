// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import FuzzingResultDialog from '../FuzzingResultDialog.vue'
import type { AvailableFuzzingRunSummary } from '@/types/fuzzing'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        fuzzViolationFound: 'Candidate violation found',
        fuzzViolationFoundDetail: 'Inspect and verify this candidate.',
        fuzzBudgetExhausted: 'Search budget exhausted',
        fuzzNoViolationWithinBudget: 'No violation was found within this budget. This is not a safety proof.',
        fuzzInconclusive: 'Search inconclusive',
        fuzzInconclusiveDetail: 'No usable conclusion.',
        unknownSpecification: 'Unknown specification',
        fuzzRunResult: 'Counterexample search result',
        fuzzResultHeuristicNotice: 'This is not a formal safety proof.',
        fuzzExplorationMode: 'Exploration initial state',
        fuzzModeBoard: 'Board snapshot',
        fuzzModePaper: 'Random state and events',
        fuzzModeBoardDescription: 'Starts from the frozen Board initial state.',
        fuzzModePaperDescription: 'Starts from a legal random state and searches reproducible inputs. It is not a proof and may not represent the authored initial state.',
        close: 'Close',
        loadingFuzzRun: 'Loading',
        runSummary: 'Run summary',
        fuzzIterations: 'Iterations',
        fuzzGeneratedPaths: 'Generated paths',
        fuzzElapsed: 'Elapsed',
        fuzzElapsedSecond: '{count} second',
        fuzzElapsedSeconds: '{count} seconds',
        fuzzEffectiveSeed: 'Effective seed',
        fuzzReproductionSettings: 'Reproduction settings',
        fuzzReproductionHint: 'Same settings and Board snapshot required.',
        fuzzReuseSettings: 'Use these settings',
        fuzzMaxIterations: 'Iteration budget',
        fuzzPathLength: 'Path length',
        fuzzPopulationSize: 'Candidate paths per iteration',
        fuzzTargetSpecifications: 'Target specifications',
        fuzzReproductionSelectedTargets: 'Explicit targets: {count}',
        fuzzReproductionAllTargets: 'All frozen targets ({count})',
        runScopeAndSnapshot: 'Run scope and snapshot',
        modelRunSnapshotSummary: 'Captured {time}: {devices} devices, {rules} rules, {specs} specs, {variables} variables, {templates} templates',
        fuzzBoardScopeChanged: 'Current Board scope changed.',
        fuzzBoardScopeCurrent: 'Current Board scope counts match.',
        fuzzIneligibleSpecifications: '{count} ineligible specifications',
        fuzzEligibilityUnsupportedTemplate: 'This template is not supported by the explorer.',
        fuzzEligibilityUnknown: 'The eligibility reason is not recognized.',
        fuzzLimitations: 'Limitations',
        fuzzPaperCapabilitiesAndBoundaries: 'Random-state mode capabilities and boundaries',
        fuzzLimitationFiniteTraceTemplates: 'The search checks only states within the configured path length; it does not replace unbounded temporal verification.',
        fuzzLimitationUnsupportedConcepts: 'Attack, trust, privacy, and content semantics are unsupported.',
        fuzzLimitationFinalAntecedent: 'A final antecedent without a successor is inconclusive.',
        fuzzLimitationPaperEventFsmDistanceEnabled: 'Candidate ranking considers the current specification state and remaining steps toward a violation.',
        fuzzLimitationPaperRandomInitialStateEnabled: 'Each candidate uses a legal initial state derived from its random seed.',
        fuzzLimitationPaperStructuredLtlOnly: 'Only Always, Never, and Immediate response structured specifications are supported.',
        fuzzLimitationPaperIntegerNumericOnly: 'Numeric ranges use integers; decimals are not supported.',
        fuzzLimitationPaperDiscreteEnvironmentExtension: 'Discrete environment variables may use direct-value inputs.',
        fuzzLimitationNuSmvProofAuthority: 'Only formal verification can establish a safety conclusion.',
        fuzzLimitationPaperPredecessorOutputsThreeLevels: 'Automation conditions are traced back by up to three levels.',
        fuzzLimitationPaperMultiTargetExtension: 'Multiple targets keep separate candidate guidance.',
        fuzzLimitationUnknown: 'An unrecognized limitation applies.',
        fuzzFindings: 'Candidate violations',
        fuzzTargetResults: 'Results by target',
        fuzzTargetResultsSummary: '{found} of {total} targets have a candidate',
        fuzzTargetCandidateFound: 'Candidate found; verify formally.',
        fuzzTargetNoCandidateWithinBudget: 'No candidate within this budget; not a proof.',
        fuzzNoReplayableFindings: 'No replayable findings.',
        fuzzFindingMeta: 'First violation: step {step}, seed {seed}',
        replay: 'Replay',
        verifyFormally: 'Verify formally',
        verifyCurrentBoard: 'Verify current Board',
        fuzzFormalVerificationCurrentBoardNotice: 'Formal verification checks the complete current Board and does not import historical inputs.',
        fuzzFindingNotFixable: 'Run formal verification before any fix.'
      }
    }
  }
})

const snapshot = {
  capturedAt: '2026-07-14T10:00:00',
  deviceCount: 1,
  ruleCount: 1,
  specificationCount: 1,
  environmentVariableCount: 0,
  deviceTemplateCount: 1,
  modelFingerprint: 'a'.repeat(64),
  templatesFrozen: true as const
}

const run: AvailableFuzzingRunSummary & { targetSpecIds: string[] } = {
  id: 10,
  explorationMode: 'PAPER_COMPATIBLE',
  outcome: 'FOUND_VIOLATION',
  effectiveSeed: 42,
  iterations: 20,
  generatedPaths: 200,
  elapsedMs: 900,
  modelSnapshot: snapshot,
  eligibility: {
    eligibleSpecIds: ['spec-1', 'spec-3'],
    eligibleSpecLabels: {
      'spec-1': 'Door remains closed',
      'spec-3': 'Window remains closed'
    },
    ineligibleSpecs: [{
      specId: 'spec-2',
      specificationLabel: 'Unsupported response',
      reasonCode: 'UNSUPPORTED_TEMPLATE',
      reason: 'backend-only English diagnostic'
    }],
    requestedSpecCount: 3,
    eligibleSpecCount: 2
  },
  limitations: [
    'FINITE_TRACE_TEMPLATES_1_3_4_ONLY',
    'ATTACK_TRUST_PRIVACY_CONTENT_UNSUPPORTED',
    'FINAL_ANTECEDENT_WITHOUT_SUCCESSOR_INCONCLUSIVE',
    'PAPER_EVENT_FSM_DISTANCE_ENABLED',
    'PAPER_RANDOM_INITIAL_STATE_ENABLED',
    'PAPER_STRUCTURED_LTL_TEMPLATES_ONLY',
    'PAPER_INTEGER_NUMERIC_DOMAIN_ONLY',
    'PAPER_DISCRETE_ENVIRONMENT_DIRECT_VALUE_EXTENSION',
    'NUSMV_REMAINS_PROOF_AUTHORITY',
    'PAPER_PREDECESSOR_STATE_OUTPUTS_THREE_LEVELS_ONLY',
    'PAPER_MULTI_TARGET_PRODUCT_EXTENSION',
    'FUTURE_LIMITATION'
  ],
  maxIterations: 20,
  pathLength: 10,
  populationSize: 10,
  createdAt: '2026-07-14T10:00:00',
  completedAt: '2026-07-14T10:00:01',
  findingCount: 1,
  dataAvailable: true,
  targetSpecIds: ['spec-1', 'spec-3'],
  findings: [{
    id: 11,
    fuzzTaskId: 10,
    violatedSpecId: 'spec-1',
    violatedSpec: {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Door remains closed',
      aConditions: [],
      ifConditions: [],
      thenConditions: []
    },
    firstViolationStep: 3,
    seed: 42,
    createdAt: '2026-07-14T10:00:01',
    stateCount: 4
  }]
}

describe('FuzzingResultDialog', () => {
  it('offers replay and formal verification without exposing automatic fix', async () => {
    const wrapper = mount(FuzzingResultDialog, {
      props: { visible: true, run, boardDrifted: true },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Candidate violation found')
    expect(wrapper.text()).toContain('1 second')
    expect(wrapper.text()).not.toContain('1s')
    expect(wrapper.get('[role="dialog"]').classes()).toEqual(expect.arrayContaining([
      'dark:border-slate-700',
      'dark:bg-slate-900'
    ]))
    expect(wrapper.get('[data-testid="fuzzing-result-mode"]').classes()).toEqual(expect.arrayContaining([
      'dark:border-amber-800',
      'dark:bg-amber-950/50',
      'dark:text-amber-100'
    ]))
    expect(wrapper.text()).toContain('7/14/2026')
    expect(wrapper.get('[data-testid="fuzzing-result-mode"]').text()).toContain('Random state and events')
    expect(wrapper.get('[data-testid="fuzzing-result-mode"]').text()).toContain('legal random state')
    expect(wrapper.get('[data-testid="fuzzing-result-mode"]').text()).toContain('not a proof')
    expect(wrapper.text()).toContain('Run formal verification before any fix.')
    expect(wrapper.text()).toContain('This template is not supported by the explorer.')
    expect(wrapper.text()).toContain('The search checks only states within the configured path length; it does not replace unbounded temporal verification.')
    expect(wrapper.text()).toContain('Random-state mode capabilities and boundaries')
    expect(wrapper.text()).toContain('Candidate ranking considers the current specification state and remaining steps toward a violation.')
    expect(wrapper.text()).toContain('Each candidate uses a legal initial state derived from its random seed.')
    expect(wrapper.text()).toContain('Only Always, Never, and Immediate response structured specifications are supported.')
    expect(wrapper.text()).not.toMatch(/paper subset|Event quadruple|monitor FSM|GetPrevConditions|BFS|NuSMV|HAFuzz/i)
    expect(wrapper.text()).toContain('Numeric ranges use integers; decimals are not supported.')
    expect(wrapper.text()).toContain('Discrete environment variables may use direct-value inputs.')
    expect(wrapper.text()).toContain('Only formal verification can establish a safety conclusion.')
    expect(wrapper.text()).toContain('Automation conditions are traced back by up to three levels.')
    expect(wrapper.text()).toContain('An unrecognized limitation applies.')
    expect(wrapper.text()).toContain('First violation: step 4, seed 42')
    expect(wrapper.text()).toContain('Reproduction settings')
    expect(wrapper.text()).toContain('Explicit targets: 2')
    expect(wrapper.text()).toContain('Candidate found; verify formally.')
    expect(wrapper.text()).toContain('No candidate within this budget; not a proof.')
    expect(wrapper.text()).toContain('Window remains closed')
    expect(wrapper.text()).toContain('Formal verification checks the complete current Board')
    expect(wrapper.text()).toContain('Captured')
    expect(wrapper.get('[data-testid="fuzzing-board-drift-warning"]').text()).toContain('Current Board scope changed.')
    expect(wrapper.text()).not.toContain('backend-only English diagnostic')
    expect(wrapper.find('[data-testid="fuzz-eligibility-technical-spec-2"]').exists()).toBe(false)
    expect(wrapper.text()).not.toContain('FINITE_TRACE_TEMPLATES_1_3_4_ONLY')
    expect(wrapper.findAll('button').some(button => button.text() === 'Fix')).toBe(false)

    await wrapper.get('[data-testid="replay-fuzzing-finding-11"]').trigger('click')
    await wrapper.get('[data-testid="verify-fuzzing-finding-11"]').trigger('click')
    await wrapper.get('[data-testid="reuse-fuzzing-settings"]').trigger('click')
    expect(wrapper.emitted('replay')).toEqual([[11]])
    expect(wrapper.emitted('verify')?.[0]?.[0]).toMatchObject({ id: 11, violatedSpecId: 'spec-1' })
    expect(wrapper.emitted('reuseSettings')).toHaveLength(1)
  })

  it('offers current-Board verification when the budget finds no candidate', async () => {
    const wrapper = mount(FuzzingResultDialog, {
      props: {
        visible: true,
        run: {
          ...run,
          outcome: 'BUDGET_EXHAUSTED',
          findings: [],
          findingCount: 0
        }
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('No candidate within this budget; not a proof.')
    const formalNotice = wrapper.get('[data-testid="fuzz-formal-verification-current-board-notice"]')
    expect(formalNotice.text()).toContain('Formal verification checks the complete current Board')
    expect(formalNotice.classes()).toEqual(expect.arrayContaining([
      'border-indigo-200',
      'bg-indigo-50',
      'text-indigo-950',
      'dark:border-indigo-800',
      'dark:bg-indigo-950/50',
      'dark:text-indigo-100'
    ]))
    expect(formalNotice.attributes('class')).not.toMatch(/emerald|green/)
    await wrapper.get('[data-testid="verify-current-board-without-finding"]').trigger('click')
    expect(wrapper.emitted('verifyCurrentBoard')).toHaveLength(1)
  })

  it('uses the frozen specification label when a lightweight finding omits violatedSpec', () => {
    const wrapper = mount(FuzzingResultDialog, {
      props: {
        visible: true,
        run: {
          ...run,
          findings: [{
            ...run.findings[0],
            violatedSpec: undefined,
            specificationLabel: 'Frozen door safety label'
          }]
        }
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Frozen door safety label')
    expect(wrapper.text()).not.toContain('Unknown specification')
  })

  it('traps focus, closes with Escape, restores focus, and ignores backdrop clicks', async () => {
    const opener = document.createElement('button')
    opener.dataset.testid = 'open-fuzzing-panel'
    document.body.appendChild(opener)
    opener.focus()

    const wrapper = mount(FuzzingResultDialog, {
      attachTo: document.body,
      props: { visible: false, run },
      global: { plugins: [i18n] }
    })

    await wrapper.setProps({ visible: true })
    await new Promise(resolve => setTimeout(resolve, 0))
    const close = wrapper.get('[data-testid="close-fuzzing-result"]')
    expect(document.activeElement).toBe(close.element)

    await wrapper.get('[data-testid="fuzzing-result-dialog"]').trigger('click')
    expect(wrapper.emitted('close')).toBeUndefined()

    await close.trigger('keydown', { key: 'Escape' })
    expect(wrapper.emitted('close')).toHaveLength(1)
    await wrapper.setProps({ visible: false })
    expect(document.activeElement).toBe(opener)

    wrapper.unmount()
    opener.remove()
  })
})
