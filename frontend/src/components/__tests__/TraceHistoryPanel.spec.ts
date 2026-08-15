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
        runInitiatedByAssistant: 'Started by AI assistant',
        runInitiatorUnknown: 'Source unavailable',
        // Real copy, so assertions read the sentence the user sees rather than a raw key: with
        // these absent, `t()` echoed the key and the tests passed on untranslated output.
        runAssumptionsLabel: 'Run assumptions',
        runAssumptionNoAttack: 'No attack modeled',
        runAssumptionAttackBudget: 'Up to {count} of {total} compromised',
        runAssumptionAttackPoints: '{count} chosen attack points',
        runAssumptionPrivacy: 'Sensitivity propagation tracked',
        historicalFixMayFailIfBoardChanged:
          'This fix was found for the board as it was; it may no longer apply.',
        runHistorySubtitle: 'Task status and completed results',
        // Real copy for the same reason as the block above: without it, `t()` echoes the key and intlify
        // logs a missing-key warning that reads exactly like a product defect. It is not — both locales
        // carry this key — but the warning was reported as one, which is the cost of a partial fixture.
        adjustAndRunAgain: 'Adjust and run again',
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
        // Real copy, for the reason recorded above: a stub that omits a key makes `t()` echo the key,
        // and an assertion on the raw key passes against untranslated output. Both drift notices are
        // here so a test can distinguish "the board changed" from "only the counts were compared".
        historicalRunBoardScopeChanged:
          'The current Board differs from this run scope. Replay temporarily shows the historical scene '
          + 'without replacing the live Board; this conclusion does not apply to the live Board.',
        historicalRunScopeCountsOnly:
          'This run has the same number of devices, rules, specifications and environment variables as '
          + 'the current Board, but their contents were not compared. Re-run to conclude anything about '
          + 'the live Board.',
        fuzzNoViolationWithinBudget: 'No violation was found within this budget. This is not a safety proof.',
        fuzzFindingsCount: '{count} candidate findings',
        fuzzFirstViolationStep: 'First violation: step {step}',
        verifyFormally: 'Verify formally',
        verificationPassed: 'Checked specifications passed',
        verificationPassedWithGenerationWarnings: 'Checked specifications satisfied; model incomplete',
        verificationFailedWithViolations: 'Found {count} specification violation(s)',
        verificationInconclusiveSummary: 'Verification inconclusive',
        inconclusiveEvidenceSummary: '{counterexamples} saved counterexample(s) are partial evidence, not a complete verdict.',
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
        fixRules: 'Fix rules',
        unknownModelItem: 'Unknown item',
        unknownOmissionReason: 'Unknown reason',
        generationIssueSpecUnknownDevice: 'The referenced device is unavailable.',
        historyActionsLockedHint: 'Close playback first.',
        historyItemUnavailable: 'History item unavailable',
        historyItemUnavailableDetail: 'This saved result is damaged and cannot be opened.',
        historyTraceUnavailableDetail: 'This counterexample is damaged and cannot be replayed.',
        historyFindingUnavailableDetail: 'This candidate trace is damaged and cannot be used.',
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
  modelFingerprint: 'a'.repeat(64),
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
  it('exposes a labelled non-modal region, focuses close, and closes on Escape', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      attachTo: document.body,
      props: { ...baseProps, activeLayer: 'tasks' },
      global: { plugins: [i18n] }
    })

    const panel = wrapper.get('[data-testid="trace-history-panel"]')
    // Non-modal tool panel: the canvas behind it stays interactive, so it is a region
    // rather than a dialog.
    expect(panel.attributes('role')).toBe('region')
    expect(panel.attributes('aria-modal')).toBeUndefined()
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
            initiator: 'AI_ASSISTANT',
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
            initiator: 'USER',
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
          initiator: 'UNKNOWN',
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
    // The reported cause must be visible, not folded into a collapsed disclosure. It previously sat
    // inside `<details>`; `wrapper.text()` includes collapsed content, so this file asserted the
    // message was "shown" while a real browser showed only the summary — two reviews of an actual
    // failed run reported the cause as missing. Assert on the element that renders it.
    const failureReason = wrapper.get('[data-testid="task-failure-reason-simulation-3"]')
    expect(failureReason.text()).toContain('NuSMV could not start')
    expect(wrapper.find('details').exists()).toBe(false)
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
    expect(wrapper.text()).toContain('Started by AI assistant')
    expect(wrapper.text()).toContain('Source unavailable')
  })

  // A failed run must offer a way forward. Dismiss only hides it, so without this the user's only
  // options were to hide the failure or reconstruct the settings from memory.
  it('offers a route back to the launching panel for a failed run', async () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'tasks',
        fuzzingTasks: [{
          id: 12,
          initiator: 'USER' as const,
          status: 'FAILED' as const,
          progress: 40,
          createdAt: '2026-08-02T10:00:00',
          startedAt: '2026-08-02T10:00:01',
          completedAt: '2026-08-02T10:00:09',
          errorMessage: 'The counterexample search stopped before the task completed',
          explorationMode: 'BOARD_SNAPSHOT' as const,
          modelSnapshot: snapshot(1),
          maxIterations: 40,
          pathLength: 6,
          populationSize: 4,
          targetSpecIds: []
        }]
      },
      global: { plugins: [i18n] }
    })

    // The cause is stated outright rather than folded away.
    expect(wrapper.get('[data-testid="task-failure-reason-fuzzing-12"]').text())
      .toContain('stopped before the task completed')

    await wrapper.get('[data-testid="reopen-task-settings-fuzzing-12"]').trigger('click')
    // Emits the kind, not the stale request: the owning panel re-validates against the current board.
    expect(wrapper.emitted('reopen-task-settings')).toEqual([['fuzzing']])
  })

  // A running task that has not reported progress yet must read 0, not full. The bar is rendered
  // only for PENDING/RUNNING tasks, so there is no honest reading of "complete" available here.
  it('reports zero progress for a running task that has not reported any yet', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'tasks',
        verificationTasks: [
          {
            id: 9,
            initiator: 'USER' as const,
            status: 'RUNNING' as const,
            createdAt: '2026-08-02T10:00:00',
            startedAt: '2026-08-02T10:00:01',
            isAttack: false,
            attackBudget: 0,
            enablePrivacy: false,
            modelSemantics: semantics,
            modelSnapshot: snapshot(1)
          }
        ]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[role="progressbar"]').attributes('aria-valuenow')).toBe('0')
    expect(wrapper.text()).not.toContain('100%')
  })

  it('distinguishes what each passing run actually covered, and warns before a historical fix', () => {
    // Two green runs with identical counts used to render identical rows: attack modeling off and
    // exhaustive compromise up to a budget are very different safety claims.
    const base = {
      initiator: 'USER' as const,
      createdAt: '2026-07-13T10:00:00',
      startedAt: '2026-07-13T10:00:00',
      completedAt: '2026-07-13T10:00:02',
      modelSnapshot: snapshot(2),
      outcome: 'SATISFIED' as const,
      modelComplete: true,
      violatedSpecCount: 0,
      counterexampleCount: 0,
      disabledRuleCount: 0,
      skippedSpecCount: 0,
      generationIssues: [],
      dataAvailable: true as const,
      counterexamples: []
    }
    const noAttack: VerificationRunSummary = {
      ...base, id: 11, isAttack: false, attackBudget: 0, enablePrivacy: false,
      modelSemantics: semantics
    }
    const budgeted: VerificationRunSummary = {
      ...base, id: 12, isAttack: true, attackBudget: 2, enablePrivacy: true,
      modelSemantics: {
        ...semantics,
        attackSelectionPolicy: 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC',
        modeledAttackPointCount: 5
      }
    }
    // An exact-points run arrives with attackBudget == points.size(), so only the policy
    // distinguishes "these two points" from "any two of five".
    const pinned: VerificationRunSummary = {
      ...base, id: 13, isAttack: true, attackBudget: 2, enablePrivacy: false,
      modelSemantics: {
        ...semantics,
        attackSelectionPolicy: 'EXACT_ATTACK_POINTS',
        modeledAttackPointCount: 2
      }
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [noAttack, budgeted, pinned]
      },
      global: { plugins: [i18n] }
    })

    const plain = wrapper.get('[data-testid="verification-run-assumptions-11"]')
    expect(plain.text()).toContain('No attack modeled')
    expect(plain.attributes('aria-label')).toBe('Run assumptions')

    const attacked = wrapper.get('[data-testid="verification-run-assumptions-12"]')
    expect(attacked.text()).toContain('Up to 2 of 5 compromised')
    expect(attacked.text()).toContain('Sensitivity propagation tracked')

    const exact = wrapper.get('[data-testid="verification-run-assumptions-13"]')
    expect(exact.text()).toContain('2 chosen attack points')
    // Must not claim an exhaustive search the run never performed.
    expect(exact.text()).not.toContain('Up to')

    // The rows must no longer read identically.
    expect(new Set([plain.text(), attacked.text(), exact.text()]).size).toBe(3)
    wrapper.unmount()
  })

  /*
   * A history row may not claim "unchanged" by staying silent.
   *
   * The row compares five integers against the current canvas. Inverting a rule's relation operator,
   * changing an environment variable's value or moving a specification's threshold leaves all five equal
   * — and the row previously rendered nothing at all, which a reader takes as "this verdict still
   * describes my canvas". That is the one claim this product never makes: `runBoardNotCompared` says a
   * result applies only to its snapshot, an open verdict withdraws its Fix action when the board
   * changes, and the fuzz predicate beside this one is explicitly written so an un-comparable state
   * reads as drift rather than as a match.
   *
   * A real fingerprint is not available here: `modelFingerprint` is fuzz-only by *contract* — the
   * backend's `PersistedModelContextIntegrity` rejects a verification or simulation snapshot that
   * carries one — so the honest fix is to say what was and was not compared.
   */
  const runWithSnapshot = (
    id: number,
    modelSnapshot: ReturnType<typeof snapshot>
  ): VerificationRunSummary => ({
    id,
    initiator: 'USER',
    createdAt: '2026-07-13T10:00:00',
    startedAt: '2026-07-13T10:00:00',
    completedAt: '2026-07-13T10:00:02',
    isAttack: false,
    attackBudget: 0,
    enablePrivacy: false,
    modelSemantics: semantics,
    modelSnapshot,
    outcome: 'SATISFIED',
    modelComplete: true,
    violatedSpecCount: 0,
    counterexampleCount: 0,
    disabledRuleCount: 0,
    skippedSpecCount: 0,
    generationIssues: [],
    dataAvailable: true,
    counterexamples: []
  })

  const currentScopeMatching = {
    deviceCount: 4,
    ruleCount: 3,
    specificationCount: 2,
    environmentVariableCount: 0,
    deviceTemplateCount: 4,
    modelFingerprint: null
  }

  it('says the contents were not compared when only the counts match', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [runWithSnapshot(60, snapshot(2))],
        currentBoardScope: currentScopeMatching
      },
      global: { plugins: [i18n] }
    })

    // Not the drift warning — the counts genuinely match, so claiming a change would be false too.
    expect(wrapper.find('[data-testid="verification-history-board-drift"]').exists()).toBe(false)
    const notice = wrapper.get('[data-testid="verification-history-scope-counts-only"]')
    expect(notice.text()).toContain('contents were not compared')
    expect(notice.text()).toContain('Re-run')
    wrapper.unmount()
  })

  it('still warns about drift, and only that, when a count differs', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        // One more rule on the canvas than the run was given.
        verificationRuns: [runWithSnapshot(61, { ...snapshot(2), ruleCount: 2 })],
        currentBoardScope: currentScopeMatching
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="verification-history-board-drift"]').text())
      .toContain('differs from this run scope')
    // The two notices are mutually exclusive; showing both would say "changed" and "matches" at once.
    expect(wrapper.find('[data-testid="verification-history-scope-counts-only"]').exists()).toBe(false)
    wrapper.unmount()
  })

  it('tells the user a historical fix may not apply to the current board', () => {
    const run: VerificationRunSummary = {
      id: 30,
      initiator: 'USER',
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
      violatedSpecCount: 1,
      counterexampleCount: 1,
      disabledRuleCount: 0,
      skippedSpecCount: 0,
      generationIssues: [],
      dataAvailable: true,
      counterexamples: []
    }
    run.counterexamples = [{
      id: 41,
      verificationTaskId: 30,
      violatedSpecId: 'spec_1',
      stateCount: 3,
      createdAt: '2026-07-13T10:00:02',
      dataAvailable: true
    } as TraceSummary]

    const wrapper = mount(TraceHistoryPanel, {
      props: { ...baseProps, activeLayer: 'results', verificationRuns: [run] },
      global: { plugins: [i18n] }
    })

    // An enabled Fix button reads as "this applies to my board now"; the caveat has to be adjacent
    // and programmatically linked, not left as an unused translation.
    const caveat = wrapper.get('[data-testid="historical-fix-caveat-30"]')
    expect(caveat.text()).toContain('it may no longer apply')
    expect(wrapper.get('[data-testid="fix-verification-trace-41"]').attributes('aria-describedby'))
      .toBe('historical-fix-caveat-30')
    wrapper.unmount()
  })

  it('groups counterexamples under one verification result and distinguishes violations from replayable evidence', () => {
    const run: VerificationRunSummary = {
      id: 11,
      initiator: 'USER',
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
    expect(wrapper.findAll('button').some(button => button.text() === 'Fix rules')).toBe(true)
  })

  /**
   * The zero-counterexample case, which is where the explanation is most needed and was unreachable.
   *
   * The sibling test above covers 2 violations / 1 counterexample. At 2 / **0** the whole evidence block
   * was gated on the trace list being non-empty, so the run showed its violation count with nothing
   * saying why none could be replayed — while the sentence written for exactly that
   * (`counterexampleCount < violatedSpecCount`, true at zero) sat inside the hidden block.
   *
   * Reachable from the backend: `VerificationServiceImpl` logs "violated (no counterexample)" when
   * NuSMV returns none, and skips the trace when the parsed state list comes back empty — both count the
   * specification as violated.
   */
  it('explains a violated run that produced no replayable counterexample', () => {
    const run: VerificationRunSummary = {
      id: 15,
      initiator: 'USER',
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
      counterexampleCount: 0,
      disabledRuleCount: 0,
      skippedSpecCount: 0,
      generationIssues: [],
      dataAvailable: true,
      counterexamples: []
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: { ...baseProps, activeLayer: 'results', verificationRuns: [run] },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text(), 'the violation count must still be stated')
      .toContain('2 violations, 0 counterexamples')
    expect(wrapper.text(), 'and the reason nothing is replayable must be stated too')
      .toContain('Some violations have no replayable counterexample.')
    expect(
      wrapper.findAll('button').some(button => button.text() === 'Replay'),
      'with no trace there is nothing to replay'
    ).toBe(false)
  })

  it('keeps replayable counterexamples visible when the overall verification is inconclusive', () => {
    const run: VerificationRunSummary = {
      id: 14,
      initiator: 'USER',
      createdAt: '2026-07-13T10:00:00',
      startedAt: '2026-07-13T10:00:00',
      completedAt: '2026-07-13T10:00:02',
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false,
      modelSemantics: semantics,
      modelSnapshot: snapshot(2),
      outcome: 'INCONCLUSIVE',
      modelComplete: false,
      violatedSpecCount: 1,
      counterexampleCount: 1,
      disabledRuleCount: 0,
      skippedSpecCount: 1,
      generationIssues: [{
        issueType: 'SPECIFICATION_SKIPPED',
        itemLabel: 'Missing device',
        reasonCode: 'SPEC_UNKNOWN_DEVICE',
        reason: 'The referenced device is unavailable.'
      }],
      dataAvailable: true,
      counterexamples: [{
        id: 22,
        verificationTaskId: 14,
        violatedSpecId: 'spec_1',
        stateCount: 2,
        createdAt: '2026-07-13T10:00:02',
        dataAvailable: true
      } as TraceSummary]
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        verificationRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Verification inconclusive')
    expect(wrapper.text()).toContain('1 saved counterexample(s) are partial evidence')
    expect(wrapper.find('[data-testid="view-verification-trace-22"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="fix-verification-trace-22"]').exists()).toBe(true)
    expect(wrapper.text()).not.toContain('1 violations, 1 counterexamples')
  })

  it('shows the selected exploration mode on active fuzz tasks', () => {
    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'tasks',
        fuzzingTasks: [{
          id: 7,
          initiator: 'AI_ASSISTANT',
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
      initiator: 'USER',
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
      initiator: 'UNKNOWN',
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

  it('disables a result delete action while that exact deletion is pending', async () => {
    const unavailableRun: VerificationRunSummary = {
      id: 99,
      initiator: 'USER',
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
        verificationRuns: [unavailableRun],
        pendingResultDeleteKeys: new Set(['verification:99'])
      },
      global: { plugins: [i18n] }
    })

    const deleteButton = wrapper.get('[data-testid="delete-verification-run-99"]')
    expect(deleteButton.attributes('disabled')).toBeDefined()
    expect(deleteButton.attributes('aria-busy')).toBe('true')
    await deleteButton.trigger('click')
    expect(wrapper.emitted('delete-verification-run')).toBeUndefined()
  })

  it('keeps an unavailable fuzz run deletable without exposing result or finding actions', () => {
    const unavailableRun: FuzzingRunSummary = {
      id: 100,
      initiator: 'AI_ASSISTANT',
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

  it('treats fuzz findings as metadata-only summaries and validates evidence on action', async () => {
    const run: FuzzingRunSummary = {
      id: 40,
      initiator: 'USER',
      explorationMode: 'BOARD_SNAPSHOT',
      outcome: 'FOUND_VIOLATION',
      effectiveSeed: 42,
      iterations: 1,
      generatedPaths: 1,
      elapsedMs: 10,
      modelSnapshot: snapshot(1),
      eligibility: {
        eligibleSpecIds: ['spec-1'],
        eligibleSpecLabels: { 'spec-1': 'Frozen door safety label' },
        ineligibleSpecs: [],
        requestedSpecCount: 1,
        eligibleSpecCount: 1
      },
      limitations: [],
      maxIterations: 10,
      pathLength: 2,
      populationSize: 1,
      createdAt: '2026-07-13T11:00:00',
      completedAt: '2026-07-13T11:00:01',
      findingCount: 1,
      findings: [{
        id: 401,
        fuzzTaskId: 40,
        violatedSpecId: 'spec-1',
        specificationLabel: 'Frozen door safety label',
        firstViolationStep: 0,
        seed: 42,
        createdAt: '2026-07-13T11:00:01',
        stateCount: 1
      }],
      dataAvailable: true
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        fuzzingRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Frozen door safety label')
    const replay = wrapper.get('[data-testid="view-fuzzing-finding-401"]')
    const verifyButton = wrapper.get('[data-testid="verify-fuzzing-finding-401"]')
    expect(replay.attributes('disabled')).toBeUndefined()
    expect(verifyButton.attributes('disabled')).toBeUndefined()
    await replay.trigger('click')
    await verifyButton.trigger('click')
    expect(wrapper.emitted('view-fuzzing-finding')).toEqual([[401, 40]])
    expect(wrapper.emitted('verify-fuzzing-finding')).toEqual([[run.findings[0]]])
  })

  it('keeps an intact fuzz finding usable when a sibling finding is unavailable', async () => {
    const unavailableFinding = {
      id: 402,
      fuzzTaskId: 40,
      violatedSpecId: 'spec-1',
      specificationLabel: 'Damaged candidate',
      firstViolationStep: 0,
      seed: 42,
      createdAt: '2026-07-13T11:00:01',
      stateCount: 1,
      dataAvailable: false as const,
      unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID'
    }
    const availableFinding = {
      ...unavailableFinding,
      id: 403,
      specificationLabel: 'Intact candidate',
      dataAvailable: true as const,
      unavailableReasonCode: undefined
    }
    const run: FuzzingRunSummary = {
      id: 40,
      initiator: 'USER',
      explorationMode: 'BOARD_SNAPSHOT',
      outcome: 'FOUND_VIOLATION',
      effectiveSeed: 42,
      iterations: 1,
      generatedPaths: 1,
      elapsedMs: 10,
      modelSnapshot: snapshot(1),
      eligibility: {
        eligibleSpecIds: ['spec-1'],
        eligibleSpecLabels: { 'spec-1': 'Frozen door safety label' },
        ineligibleSpecs: [],
        requestedSpecCount: 1,
        eligibleSpecCount: 1
      },
      limitations: [],
      maxIterations: 10,
      pathLength: 2,
      populationSize: 1,
      createdAt: '2026-07-13T11:00:00',
      completedAt: '2026-07-13T11:00:01',
      findingCount: 2,
      findings: [unavailableFinding, availableFinding],
      dataAvailable: true
    }

    const wrapper = mount(TraceHistoryPanel, {
      props: {
        ...baseProps,
        activeLayer: 'results',
        resultFilter: 'fuzzing',
        fuzzingRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('This candidate trace is damaged and cannot be used.')
    expect(wrapper.get('[data-testid="view-fuzzing-finding-402"]').attributes('disabled')).toBeDefined()
    expect(wrapper.get('[data-testid="verify-fuzzing-finding-402"]').attributes('disabled')).toBeDefined()
    const replay = wrapper.get('[data-testid="view-fuzzing-finding-403"]')
    const verifyButton = wrapper.get('[data-testid="verify-fuzzing-finding-403"]')
    expect(replay.attributes('disabled')).toBeUndefined()
    expect(verifyButton.attributes('disabled')).toBeUndefined()
    await replay.trigger('click')
    await verifyButton.trigger('click')
    expect(wrapper.emitted('view-fuzzing-finding')).toEqual([[403, 40]])
    expect(wrapper.emitted('verify-fuzzing-finding')).toEqual([[availableFinding]])
  })

  it('presents budget exhaustion as a neutral heuristic result, not a proof or fix target', () => {
    const run: FuzzingRunSummary = {
      id: 41,
      initiator: 'USER',
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
    expect(wrapper.findAll('button').some(button => button.text() === 'Fix rules')).toBe(false)
    expect(wrapper.findAll('button').some(button => button.text() === 'Verify formally')).toBe(false)
  })

  it('detects semantic drift when counts match but model fingerprints differ', () => {
    const run: FuzzingRunSummary = {
      id: 42,
      initiator: 'USER',
      explorationMode: 'BOARD_SNAPSHOT',
      outcome: 'BUDGET_EXHAUSTED',
      effectiveSeed: 42,
      iterations: 10,
      generatedPaths: 20,
      elapsedMs: 100,
      modelSnapshot: { ...snapshot(1), modelFingerprint: 'a'.repeat(64) },
      eligibility: {
        eligibleSpecIds: ['spec-1'],
        eligibleSpecLabels: { 'spec-1': 'Door remains closed' },
        ineligibleSpecs: [],
        requestedSpecCount: 1,
        eligibleSpecCount: 1
      },
      limitations: [],
      maxIterations: 10,
      pathLength: 5,
      populationSize: 2,
      createdAt: '2026-07-13T11:00:00',
      completedAt: '2026-07-13T11:00:01',
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
          specificationCount: 1,
          environmentVariableCount: 0,
          deviceTemplateCount: 4,
          modelFingerprint: 'b'.repeat(64)
        },
        fuzzingRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="fuzzing-history-board-drift"]').text())
      .toContain('Current Board scope changed.')
  })

  it('does not claim a fingerprinted run is unchanged when the current fingerprint is unavailable', () => {
    const run: FuzzingRunSummary = {
      id: 43,
      initiator: 'USER',
      explorationMode: 'BOARD_SNAPSHOT',
      outcome: 'BUDGET_EXHAUSTED',
      effectiveSeed: 43,
      iterations: 10,
      generatedPaths: 20,
      elapsedMs: 100,
      modelSnapshot: { ...snapshot(1), modelFingerprint: 'a'.repeat(64) },
      eligibility: {
        eligibleSpecIds: ['spec-1'],
        eligibleSpecLabels: { 'spec-1': 'Door remains closed' },
        ineligibleSpecs: [],
        requestedSpecCount: 1,
        eligibleSpecCount: 1
      },
      limitations: [],
      maxIterations: 10,
      pathLength: 5,
      populationSize: 2,
      createdAt: '2026-07-13T11:00:00',
      completedAt: '2026-07-13T11:00:01',
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
          specificationCount: 1,
          environmentVariableCount: 0,
          deviceTemplateCount: 4
        },
        fuzzingRuns: [run]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="fuzzing-history-board-drift"]').text())
      .toContain('Current Board scope changed.')
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
          initiator: 'UNKNOWN',
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
