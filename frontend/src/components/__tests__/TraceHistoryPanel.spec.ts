// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import TraceHistoryPanel from '../TraceHistoryPanel.vue'
import type { TraceSummary, VerificationRunSummary, VerificationTaskSummary } from '@/types/verify'
import type { SimulationTaskSummary, SimulationTraceSummary } from '@/types/simulation'
import type { FuzzingRunSummary, FuzzingTaskSummary } from '@/types/fuzzing'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        runHistory: 'Run History',
        runHistorySubtitle: 'Task status and completed results',
        close: 'Close',
        taskStatusLayer: 'Task Status',
        historyResultsLayer: 'History Results',
        pendingTaskSummary: '{active} active, {unresolved} without a result',
        refresh: 'Refresh',
        loadingTasks: 'Loading tasks',
        noPendingTasks: 'No tasks need attention',
        noPendingTasksHint: 'Completed runs move to history.',
        runningTasks: 'Running Tasks',
        tasksWithoutResults: 'No Result Produced',
        verification: 'Verification',
        fuzzSearch: 'Counterexample Search',
        simulation: 'Simulation',
        taskStatusRunning: 'Running',
        taskStatusFailed: 'Failed',
        taskStatusCancelled: 'Cancelled',
        taskInitializing: 'Initializing',
        progress: 'Progress',
        watchTask: 'Watch',
        cancel: 'Cancel',
        failedTaskNoResult: 'The task failed without a result.',
        cancelledTaskNoResult: 'The task was cancelled without a result.',
        technicalDetails: 'Technical Details',
        dismissTask: 'Dismiss',
        allResults: 'All',
        loadingRunResults: 'Loading history results',
        loadMoreFuzzingResults: 'Load more counterexample results',
        loadingMoreFuzzingResults: 'Loading more counterexample results',
        noRunResults: 'No history results',
        noRunResultsHint: 'Completed results appear here.',
        verificationRunResult: 'Verification Result',
        simulationRunResult: 'Simulation Result',
        fuzzRunResult: 'Counterexample search result',
        fuzzModeBoard: 'Board snapshot',
        fuzzModePaper: 'Random state and events',
        fuzzModeBoardDescription: 'Starts from the frozen Board initial state.',
        fuzzModePaperDescription: 'Starts from a legal random state and searches reproducible inputs; it is not a proof.',
        fuzzViolationFound: 'Candidate violation found',
        fuzzBudgetExhausted: 'Search budget exhausted',
        fuzzInconclusive: 'Search inconclusive',
        fuzzRunCounts: '{iterations} iterations, {paths} paths, {elapsed}s',
        fuzzBoardScopeChanged: 'Current Board scope changed.',
        fuzzNoViolationWithinBudget: 'No violation was found within this budget. This is not a safety proof.',
        fuzzFindingsCount: '{count} candidate findings',
        fuzzFirstViolationStep: 'First violation: step {step}',
        verifyFormally: 'Verify formally',
        verificationPassed: 'Checked specifications passed',
        verificationPassedWithGenerationWarnings: 'Checked specifications satisfied; model incomplete',
        verificationFailedWithViolations: 'Found {count} specification violation(s)',
        verificationInconclusiveSummary: 'Verification inconclusive',
        allRulesModeled: 'All rules included',
        incompleteModel: 'Incomplete model',
        runScopeCounts: '{devices} devices, {rules} rules, {specs} specs',
        simulationHistoryCounts: 'Requested {requested}, produced {steps}, {states} states',
        openResult: 'Open Result',
        delete: 'Delete',
        violationEvidenceSummary: '{violations} violations, {counterexamples} counterexamples',
        someViolationsHaveNoReplayableCounterexample: 'Some violations have no replayable counterexample.',
        unknownSpecification: 'Unknown specification',
        statesCount: '{count} states',
        replay: 'Replay',
        fix: 'Fix',
        unknownModelItem: 'Unknown item',
        unknownOmissionReason: 'Unknown reason',
        generationIssueSpecUnknownDevice: 'The referenced device is unavailable.',
        historyActionsLockedHint: 'Close playback first.',
        historyItemUnavailable: 'History item unavailable',
        historyItemUnavailableDetail: 'This saved result is damaged and cannot be opened.',
        historyTraceUnavailableDetail: 'This counterexample is damaged and cannot be replayed.',
        historyResultsPartialFailure: 'Some history sources could not be loaded.',
        retry: 'Retry'
      }
    }
  }
})

const snapshot = (specificationCount: number) => ({
  capturedAt: '2026-07-13T10:00:00',
  deviceCount: 4,
  ruleCount: 3,
  specificationCount,
  environmentVariableCount: 0,
  deviceTemplateCount: 4,
  templatesFrozen: true as const
})

const semantics = {
  attackPointUnit: 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK' as const,
  attackSelectionPolicy: 'NOT_MODELED' as const,
  attackEffects: [],
  modeledDeviceAttackPointCount: 0,
  modeledFalsifiableReadingDeviceCount: 0,
  modeledAutomationLinkAttackPointCount: 0,
  modeledAttackPointCount: 0,
  trustPropagationPolicy: 'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED' as const,
  privacyPropagationPolicy: 'NOT_MODELED' as const,
  labelPropagationScope: 'AUTOMATION_RULE_COMMANDS_ONLY' as const,
  environmentEvolutionEffects: [],
  localVariableFallbackPolicy: 'STUTTER_WHEN_NO_DECLARED_EVOLUTION' as const
}

const baseProps = {
  resultFilter: 'all' as const,
  verificationTasks: [] as VerificationTaskSummary[],
  fuzzingTasks: [] as FuzzingTaskSummary[],
  simulationTasks: [] as SimulationTaskSummary[],
  verificationRuns: [] as VerificationRunSummary[],
  fuzzingRuns: [] as FuzzingRunSummary[],
  simulationRuns: [] as SimulationTraceSummary[],
  loadingTasks: false,
  loadingResults: false,
  hasMoreFuzzingRuns: false,
  loadingMoreFuzzingRuns: false,
  actionLocked: false
}

describe('TraceHistoryPanel two-layer semantics', () => {
  it('exposes a labelled dialog, focuses close, and closes on Escape', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      attachTo: document.body,
      props: { ...baseProps, activeLayer: 'tasks' },
      global: { plugins: [i18n] }
    })

    const panel = wrapper.get('[data-testid="trace-history-panel"]')
    expect(panel.attributes('role')).toBe('dialog')
    expect(panel.attributes('aria-labelledby')).toBe('trace-history-title')
    expect(wrapper.get('[data-testid="history-layer-tasks"]').attributes('aria-pressed')).toBe('true')
    expect(wrapper.get('[data-testid="history-layer-results"]').attributes('aria-pressed')).toBe('false')
    await wrapper.vm.$nextTick()
    expect(document.activeElement).toBe(wrapper.get('[data-testid="close-history-panel"]').element)

    await panel.trigger('keydown', { key: 'Escape' })
    expect(wrapper.emitted('close')).toHaveLength(1)
    wrapper.unmount()
  })

  it('exposes selected result filters to assistive technology', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: { ...baseProps, activeLayer: 'results', resultFilter: 'fuzzing' },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="history-layer-results"]').attributes('aria-pressed')).toBe('true')
    expect(wrapper.get('[data-testid="history-result-filter-fuzzing"]').attributes('aria-pressed')).toBe('true')
    expect(wrapper.get('[data-testid="history-result-filter-all"]').attributes('aria-pressed')).toBe('false')

    await wrapper.setProps({ resultFilter: 'all' })
    expect(wrapper.get('[data-testid="history-result-filter-fuzzing"]').attributes('aria-pressed')).toBe('false')
    expect(wrapper.get('[data-testid="history-result-filter-all"]').attributes('aria-pressed')).toBe('true')
  })

  it('keeps completed work out of the task-status layer', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'tasks',
        verificationTasks: [
          {
            id: 1,
            status: 'RUNNING',
            createdAt: '2026-07-13T10:00:00',
            startedAt: '2026-07-13T10:00:01',
            progress: 40,
            isAttack: false,
            attackBudget: 0,
            enablePrivacy: false,
            modelSemantics: semantics,
            modelSnapshot: snapshot(1)
          },
          {
            id: 2,
            status: 'COMPLETED',
            createdAt: '2026-07-13T09:00:00',
            startedAt: '2026-07-13T09:00:01',
            completedAt: '2026-07-13T09:00:02',
            progress: 100,
            isAttack: false,
            attackBudget: 0,
            enablePrivacy: false,
            modelSemantics: semantics,
            modelSnapshot: snapshot(1),
            outcome: 'SATISFIED',
            modelComplete: true,
            violatedSpecCount: 0,
            disabledRuleCount: 0,
            skippedSpecCount: 0,
            generationIssues: []
          }
        ] as VerificationTaskSummary[],
        simulationTasks: [{
          id: 3,
          status: 'FAILED',
          createdAt: '2026-07-13T08:00:00',
          completedAt: '2026-07-13T08:00:02',
          progress: 100,
          errorMessage: 'NuSMV could not start',
          requestedSteps: 5,
          isAttack: false,
          attackBudget: 0,
          enablePrivacy: false,
          modelSemantics: semantics,
          modelSnapshot: snapshot(0)
        }] as SimulationTaskSummary[],
        pendingTaskActionKeys: new Set([
          'cancel:verification:1',
          'dismiss:simulation:3'
        ])
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('1 active, 1 without a result')
    expect(wrapper.text()).toContain('The task failed without a result.')
    expect(wrapper.text()).toContain('NuSMV could not start')
    expect(wrapper.find('details').attributes('open')).toBeUndefined()
    expect(wrapper.text()).not.toContain('Checked specifications passed')
    expect(wrapper.findAll('button').some(button => button.text().includes('Dismiss'))).toBe(true)
    const cancelButton = wrapper.findAll('button').find(button => button.text().includes('Cancel'))!
    const dismissButton = wrapper.findAll('button').find(button => button.text().includes('Dismiss'))!
    expect(cancelButton.attributes('disabled')).toBeDefined()
    expect(cancelButton.attributes('aria-busy')).toBe('true')
    expect(dismissButton.attributes('disabled')).toBeDefined()
    expect(dismissButton.attributes('aria-busy')).toBe('true')
    const progressbar = wrapper.get('[role="progressbar"]')
    expect(progressbar.attributes('aria-label')).toBe('Verification Progress')
    expect(progressbar.attributes('aria-valuenow')).toBe('40')
    expect(wrapper.text()).toContain('7/13/2026')
  })

  it('groups counterexamples under one verification result and distinguishes violations from replayable evidence', () => {
    const run: VerificationRunSummary = {
      id: 11,
      createdAt: '2026-07-13T10:00:00',
      startedAt: '2026-07-13T10:00:00',
      completedAt: '2026-07-13T10:00:02',
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false,
      modelSemantics: semantics,
      modelSnapshot: snapshot(2),
      outcome: 'VIOLATED',
      modelComplete: true,
      violatedSpecCount: 2,
      counterexampleCount: 1,
      disabledRuleCount: 0,
      skippedSpecCount: 0,
      generationIssues: [],
      dataAvailable: true,
      counterexamples: []
    }
    const trace = {
      id: 21,
      verificationTaskId: 11,
      violatedSpecId: 'spec_1',
      stateCount: 1,
      createdAt: '2026-07-13T10:00:02',
      dataAvailable: true
    } as TraceSummary
    run.counterexamples = [trace]

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Found 2 specification violation(s)')
    expect(wrapper.text()).toContain('2 violations, 1 counterexamples')
    expect(wrapper.text()).toContain('Some violations have no replayable counterexample.')
    expect(wrapper.findAll('button').some(button => button.text() === 'Replay')).toBe(true)
    expect(wrapper.findAll('button').some(button => button.text() === 'Fix')).toBe(true)
  })

  it('shows the selected exploration mode on active fuzz tasks', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'tasks',
        fuzzingTasks: [{
          id: 7,
          explorationMode: 'PAPER_COMPATIBLE',
          status: 'RUNNING',
          progress: 25,
          createdAt: '2026-07-13T10:00:00',
          modelSnapshot: snapshot(1),
          maxIterations: 500,
          pathLength: 20,
          populationSize: 10,
          targetSpecIds: ['spec-1']
        }]
      },
      global: { plugins: [i18n] }
    })

    const badge = wrapper.get('[data-testid="fuzzing-task-mode-7"]')
    expect(badge.text()).toContain('Random state and events')
    expect(badge.attributes('title')).toContain('legal random state')
  })

  it('renders localized omission copy instead of the backend technical diagnostic', () => {
    const run: VerificationRunSummary = {
      id: 12,
      createdAt: '2026-07-13T10:00:00',
      startedAt: '2026-07-13T10:00:01',
      completedAt: '2026-07-13T10:00:02',
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false,
      modelSemantics: semantics,
      modelSnapshot: snapshot(1),
      outcome: 'INCONCLUSIVE',
      modelComplete: false,
      violatedSpecCount: 0,
      counterexampleCount: 0,
      disabledRuleCount: 0,
      skippedSpecCount: 1,
      generationIssues: [{
        issueType: 'SPECIFICATION_SKIPPED',
        itemLabel: 'Keep camera off',
        reasonCode: 'SPEC_UNKNOWN_DEVICE',
        reason: "device 'camera_7' not found in deviceSmvMap"
      }],
      dataAvailable: true,
      counterexamples: []
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('The referenced device is unavailable.')
    expect(wrapper.text()).not.toContain('deviceSmvMap')
  })

  it('keeps an unavailable history item visible but exposes only deletion', () => {
    const unavailableRun: VerificationRunSummary = {
      id: 99,
      createdAt: '2026-07-13T10:00:00',
      completedAt: '2026-07-13T10:00:02',
      counterexampleCount: 0,
      counterexamples: [],
      dataAvailable: false,
      unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID'
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [unavailableRun]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('History item unavailable')
    expect(wrapper.text()).toContain('This saved result is damaged and cannot be opened.')
    expect(wrapper.findAll('button').some(button => button.text() === 'Delete')).toBe(true)
    expect(wrapper.findAll('button').some(button => button.text() === 'Open Result')).toBe(false)
    expect(wrapper.findAll('button').some(button => button.text() === 'Replay')).toBe(false)
  })

  it('keeps an unavailable fuzz run deletable without exposing result or finding actions', () => {
    const unavailableRun: FuzzingRunSummary = {
      id: 100,
      createdAt: '2026-07-13T10:00:00',
      completedAt: '2026-07-13T10:00:02',
      findings: [],
      dataAvailable: false,
      unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID'
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        fuzzingRuns: [unavailableRun]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('History item unavailable')
    expect(wrapper.findAll('button').some(button => button.text() === 'Delete')).toBe(true)
    expect(wrapper.findAll('button').some(button => button.text() === 'Open Result')).toBe(false)
    expect(wrapper.findAll('button').some(button => button.text() === 'Replay')).toBe(false)
    expect(wrapper.findAll('button').some(button => button.text() === 'Verify formally')).toBe(false)
  })

  it('presents budget exhaustion as a neutral heuristic result, not a proof or fix target', () => {
    const run: FuzzingRunSummary = {
      id: 41,
      explorationMode: 'BOARD_SNAPSHOT',
      outcome: 'BUDGET_EXHAUSTED',
      effectiveSeed: 42,
      iterations: 500,
      generatedPaths: 5000,
      elapsedMs: 1200,
      modelSnapshot: snapshot(1),
      eligibility: {
        eligibleSpecIds: ['spec-1'],
        eligibleSpecLabels: { 'spec-1': 'Door remains closed' },
        ineligibleSpecs: [],
        requestedSpecCount: 1,
        eligibleSpecCount: 1
      },
      limitations: ['Finite heuristic search.'],
      maxIterations: 500,
      pathLength: 20,
      populationSize: 10,
      createdAt: '2026-07-13T11:00:00',
      completedAt: '2026-07-13T11:00:02',
      findingCount: 0,
      findings: [],
      dataAvailable: true
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        currentBoardScope: {
          deviceCount: 4,
          ruleCount: 3,
          specificationCount: 2,
          environmentVariableCount: 0,
          deviceTemplateCount: 4
        },
        fuzzingRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Search budget exhausted')
    expect(wrapper.get('[data-testid="fuzzing-history-mode-41"]').text()).toContain('Board snapshot')
    expect(wrapper.text()).toContain('This is not a safety proof.')
    expect(wrapper.get('[data-testid="fuzzing-history-board-drift"]').text()).toContain('Current Board scope changed.')
    expect(wrapper.findAll('button').some(button => button.text() === 'Fix')).toBe(false)
    expect(wrapper.findAll('button').some(button => button.text() === 'Verify formally')).toBe(false)
  })

  it('offers an explicit next page only for fuzzing history', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        hasMoreFuzzingRuns: true,
        fuzzingRuns: [{
          id: 101,
          createdAt: '2026-07-13T10:00:00',
          findings: [],
          dataAvailable: false,
          unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID'
        }]
      },
      global: { plugins: [i18n] }
    })

    const loadMore = wrapper.get('[data-testid="load-more-fuzzing-runs"]')
    expect(loadMore.text()).toContain('Load more counterexample results')
    await loadMore.trigger('click')
    expect(wrapper.emitted('load-more-fuzzing-runs')).toHaveLength(1)

    await wrapper.setProps({ resultFilter: 'all' })
    expect(wrapper.find('[data-testid="load-more-fuzzing-runs"]').exists()).toBe(false)
  })

  it('keeps a source load failure visible instead of presenting an empty history', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        resultErrors: { fuzzing: 'Request timed out' }
      },
      global: { plugins: [i18n] }
    })

    const alert = wrapper.get('[data-testid="history-results-load-error"]')
    expect(alert.text()).toContain('Request timed out')
    expect(wrapper.text()).not.toContain('No history results')
    await alert.get('button').trigger('click')
    expect(wrapper.emitted('refresh-results')).toHaveLength(1)
  })
})
