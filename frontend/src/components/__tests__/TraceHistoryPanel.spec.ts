// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import TraceHistoryPanel from '../TraceHistoryPanel.vue'
import type { TraceSummary, VerificationRunSummary, VerificationTaskSummary } from '@/types/verify'
import type { SimulationTaskSummary, SimulationTraceSummary } from '@/types/simulation'

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
        simulation: 'Simulation',
        taskStatusRunning: 'Running',
        taskStatusFailed: 'Failed',
        taskStatusCancelled: 'Cancelled',
        taskInitializing: 'Initializing',
        watchTask: 'Watch',
        cancel: 'Cancel',
        failedTaskNoResult: 'The task failed without a result.',
        cancelledTaskNoResult: 'The task was cancelled without a result.',
        technicalDetails: 'Technical Details',
        dismissTask: 'Dismiss',
        allResults: 'All',
        loadingRunResults: 'Loading history results',
        noRunResults: 'No history results',
        noRunResultsHint: 'Completed results appear here.',
        verificationRunResult: 'Verification Result',
        simulationRunResult: 'Simulation Result',
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
        historyTraceUnavailableDetail: 'This counterexample is damaged and cannot be replayed.'
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
  simulationTasks: [] as SimulationTaskSummary[],
  verificationRuns: [] as VerificationRunSummary[],
  simulationRuns: [] as SimulationTraceSummary[],
  loadingTasks: false,
  loadingResults: false,
  actionLocked: false
}

describe('TraceHistoryPanel two-layer semantics', () => {
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
        }] as SimulationTaskSummary[]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('1 active, 1 without a result')
    expect(wrapper.text()).toContain('The task failed without a result.')
    expect(wrapper.text()).toContain('NuSMV could not start')
    expect(wrapper.find('details').attributes('open')).toBeUndefined()
    expect(wrapper.text()).not.toContain('Checked specifications passed')
    expect(wrapper.findAll('button').some(button => button.text() === 'Dismiss')).toBe(true)
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
})
