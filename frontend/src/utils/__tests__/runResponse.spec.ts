import { describe, expect, it } from 'vitest'
import type { ModelSemantics } from '@/types/modelSemantics'
import {
  RUN_RESPONSE_INCOMPLETE_CODE,
  activeTaskProgressStage,
  validateInteractiveOperationStatus,
  validateSimulationResult,
  validateSimulationTask,
  validateSimulationTraceSummary,
  validateTaskCancellationResult,
  validateTaskProgress,
  validateTaskSubmissionId,
  validateVerificationRun,
  validateVerificationRunSummary,
  validateVerificationTask,
  validateVerificationResult
} from '../runResponse'

const modelSemantics: ModelSemantics = {
  attackPointUnit: 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK',
  attackSelectionPolicy: 'NOT_MODELED',
  attackEffects: [],
  modeledDeviceAttackPointCount: 2,
  modeledFalsifiableReadingDeviceCount: 1,
  modeledAutomationLinkAttackPointCount: 3,
  modeledAttackPointCount: 5,
  trustPropagationPolicy: 'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED',
  privacyPropagationPolicy: 'NOT_MODELED',
  labelPropagationScope: 'AUTOMATION_RULE_COMMANDS_ONLY',
  environmentEvolutionEffects: [
    'DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN',
    'DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
  ],
  localVariableFallbackPolicy: 'STUTTER_WHEN_NO_DECLARED_EVOLUTION'
}

const state = (stateIndex: number) => ({
  stateIndex,
  devices: [{
    deviceId: 'device_1',
    deviceLabel: 'Hall sensor',
    templateName: 'Motion Detector',
    state: 'idle',
    variables: []
  }],
  triggeredRules: [],
  compromisedAutomationLinks: [],
  trustPrivacies: [],
  envVariables: [],
  globalVariables: []
})

const modelSnapshot = (specificationCount: number) => ({
  capturedAt: '2026-07-12T00:00:00',
  deviceCount: 2,
  ruleCount: 3,
  specificationCount,
  environmentVariableCount: 1,
  deviceTemplateCount: 2,
  templatesFrozen: true
})

const validVerification = () => ({
  isAttack: false,
  attackBudget: 0,
  enablePrivacy: false,
  modelSemantics,
  modelSnapshot: modelSnapshot(1),
  historyPersistence: { status: 'SAVED', runId: 7 },
  outcome: 'SATISFIED',
  modelComplete: true,
  traces: [],
  specResults: [{
    specId: 'spec_1',
    templateId: '1',
    specificationLabel: 'Always',
    formulaPreview: 'CTL AG("Hall sensor".state = "active")',
    formulaKind: 'CTL',
    outcome: 'SATISFIED',
    expression: 'CTLSPEC AG motion'
  }],
  checkLogs: [],
  disabledRuleCount: 0,
  skippedSpecCount: 0,
  generationIssues: [],
  nusmvOutput: '-- specification is true'
})

const validSimulation = () => ({
  isAttack: false,
  attackBudget: 0,
  enablePrivacy: false,
  modelSemantics,
  modelSnapshot: modelSnapshot(0),
  historyPersistence: { status: 'NOT_REQUESTED' },
  modelComplete: true,
  disabledRuleCount: 0,
  generationIssues: [],
  states: [state(1), state(2)],
  steps: 1,
  requestedSteps: 1,
  nusmvOutput: 'Trace Type: Simulation',
  logs: []
})

const validCompletedVerificationTask = () => ({
  id: 7,
  status: 'COMPLETED',
  createdAt: '2026-07-12T00:00:00',
  startedAt: '2026-07-12T00:00:01',
  completedAt: '2026-07-12T00:00:02',
  processingTimeMs: 1000,
  progress: 100,
  isAttack: false,
  attackBudget: 0,
  enablePrivacy: false,
  modelSemantics,
  modelSnapshot: modelSnapshot(1),
  outcome: 'SATISFIED',
  modelComplete: true,
  violatedSpecCount: 0,
  disabledRuleCount: 0,
  skippedSpecCount: 0,
  generationIssues: [],
  specResults: validVerification().specResults,
  checkLogs: [],
  nusmvOutput: '-- specification is true'
})

const validVerificationRun = () => ({
  id: 7,
  createdAt: '2026-07-12T00:00:00',
  startedAt: '2026-07-12T00:00:01',
  completedAt: '2026-07-12T00:00:02',
  processingTimeMs: 1000,
  isAttack: false,
  attackBudget: 0,
  enablePrivacy: false,
  modelSemantics,
  modelSnapshot: modelSnapshot(1),
  outcome: 'SATISFIED',
  modelComplete: true,
  violatedSpecCount: 0,
  counterexampleCount: 0,
  disabledRuleCount: 0,
  skippedSpecCount: 0,
  generationIssues: [],
  specResults: validVerification().specResults,
  checkLogs: [],
  nusmvOutput: '-- specification is true'
})

const validCompletedSimulationTask = () => ({
  id: 8,
  status: 'COMPLETED',
  createdAt: '2026-07-12T00:00:00',
  startedAt: '2026-07-12T00:00:01',
  completedAt: '2026-07-12T00:00:02',
  processingTimeMs: 1000,
  progress: 100,
  isAttack: false,
  attackBudget: 0,
  enablePrivacy: false,
  modelSemantics,
  modelSnapshot: modelSnapshot(0),
  requestedSteps: 2,
  steps: 2,
  modelComplete: true,
  disabledRuleCount: 0,
  generationIssues: [],
  simulationTraceId: 21,
  checkLogs: []
})

describe('verification and simulation response contracts', () => {
  it('accepts an explicitly complete verification result', () => {
    expect(validateVerificationResult(validVerification())).toEqual(validVerification())
  })

  it('does not infer verification completeness from missing fields', () => {
    const result = validVerification() as Record<string, unknown>
    delete result.modelComplete

    expect(() => validateVerificationResult(result)).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('requires omission counts to have matching itemized generation issues', () => {
    expect(() => validateVerificationResult({
      ...validVerification(),
      modelComplete: false,
      skippedSpecCount: 1
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('does not accept an overall satisfied conclusion that contradicts per-spec results', () => {
    expect(() => validateVerificationResult({
      ...validVerification(),
      specResults: [{
        specId: 'spec_1',
        templateId: '1',
        specificationLabel: 'Always',
        formulaPreview: 'CTL AG("Hall sensor".state = "active")',
        formulaKind: 'CTL',
        outcome: 'VIOLATED',
        expression: 'CTLSPEC AG motion'
      }]
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('accepts a playable simulation whose step count matches its states', () => {
    expect(validateSimulationResult(validSimulation())).toEqual(validSimulation())
  })

  it.each([
    { label: 'zero-based', indexes: [0, 1] },
    { label: 'duplicate', indexes: [1, 1] },
    { label: 'gapped', indexes: [1, 3] }
  ])('rejects $label formal state indexes', ({ indexes }) => {
    expect(() => validateSimulationResult({
      ...validSimulation(),
      states: indexes.map(state)
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('does not treat missing simulation completeness as a complete model', () => {
    const result = validSimulation() as Record<string, unknown>
    delete result.modelComplete

    expect(() => validateSimulationResult(result)).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('rejects a simulation history summary with contradictory attack context', () => {
    expect(() => validateSimulationTraceSummary({
      id: 3,
      requestedSteps: 2,
      steps: 2,
      modelComplete: true,
      disabledRuleCount: 0,
      generationIssues: [],
      isAttack: false,
      attackBudget: 1,
      enablePrivacy: false,
      modelSnapshot: modelSnapshot(0),
      createdAt: '2026-07-12T00:00:00',
      dataAvailable: true
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('validates completed task conclusions and requires a saved simulation trace', () => {
    expect(validateVerificationTask(validCompletedVerificationTask())).toEqual(validCompletedVerificationTask())
    expect(validateSimulationTask(validCompletedSimulationTask())).toEqual(validCompletedSimulationTask())

    expect(() => validateSimulationTask({
      ...validCompletedSimulationTask(),
      simulationTraceId: undefined
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('validates completed verification history independently from task lifecycle', () => {
    expect(validateVerificationRun(validVerificationRun())).toEqual(validVerificationRun())
    const { specResults: _specResults, checkLogs: _checkLogs, nusmvOutput: _nusmvOutput, ...runSummary } = validVerificationRun()
    const summary = { ...runSummary, dataAvailable: true, counterexamples: [] }
    expect(validateVerificationRunSummary(summary)).toEqual(summary)

    expect(() => validateVerificationRunSummary({
      ...summary,
      counterexampleCount: undefined
    })).toThrow(expect.objectContaining({ code: RUN_RESPONSE_INCOMPLETE_CODE }))

    const traceSummary = {
      id: 17,
      verificationTaskId: summary.id,
      violatedSpecId: 'spec-1',
      violatedSpec: {
        id: 'spec-1',
        templateId: '1',
        aConditions: [],
        ifConditions: [],
        thenConditions: []
      },
      stateCount: 2,
      createdAt: '2026-07-12T00:00:00',
      dataAvailable: true
    }
    expect(validateVerificationRunSummary({
      ...summary,
      outcome: 'VIOLATED',
      violatedSpecCount: 1,
      counterexampleCount: 1,
      counterexamples: [traceSummary]
    }).counterexamples).toEqual([traceSummary])

    const unavailableTraceSummary = {
      id: 18,
      verificationTaskId: summary.id,
      dataAvailable: false,
      unavailableReasonCode: 'PERSISTED_SEMANTIC_DATA_INVALID'
    } as const
    const mixedCounterexamples = [traceSummary, unavailableTraceSummary]
    expect(validateVerificationRunSummary({
      ...summary,
      outcome: 'VIOLATED',
      violatedSpecCount: 1,
      counterexampleCount: 1,
      counterexamples: mixedCounterexamples
    }).counterexamples).toEqual(mixedCounterexamples)

    expect(() => validateVerificationRunSummary({
      ...summary,
      outcome: 'VIOLATED',
      violatedSpecCount: 1,
      counterexampleCount: 2,
      counterexamples: mixedCounterexamples
    })).toThrow(expect.objectContaining({ code: RUN_RESPONSE_INCOMPLETE_CODE }))

    const { createdAt: _createdAt, ...traceWithoutTimestamp } = traceSummary
    expect(() => validateVerificationRunSummary({
      ...summary,
      outcome: 'VIOLATED',
      violatedSpecCount: 1,
      counterexampleCount: 1,
      counterexamples: [traceWithoutTimestamp]
    })).toThrow(expect.objectContaining({ code: RUN_RESPONSE_INCOMPLETE_CODE }))
  })

  it('rejects results that cannot prove templates were frozen at submission', () => {
    expect(() => validateVerificationResult({
      ...validVerification(),
      modelSnapshot: {
        ...modelSnapshot(1),
        templatesFrozen: false
      }
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('does not allow an active task to publish a premature conclusion', () => {
    expect(() => validateVerificationTask({
      ...validCompletedVerificationTask(),
      status: 'RUNNING',
      completedAt: undefined,
      progress: 40
    })).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('validates task ids, progress, and cancellation outcomes before the UI acts on them', () => {
    expect(validateTaskSubmissionId(9, 'Task submission')).toBe(9)
    expect(validateTaskProgress(63, 'Task progress')).toBe(63)
    expect(validateTaskCancellationResult({
      taskId: 9,
      cancellationAccepted: true,
      cancellationOutcome: 'ACCEPTED',
      taskStatus: 'CANCELLED',
      executionMayStillBeStopping: true
    }, 9, 'Task cancellation')).toMatchObject({ cancellationAccepted: true })

    expect(() => validateTaskProgress(101, 'Task progress')).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
    expect(() => validateTaskCancellationResult({
      taskId: 10,
      cancellationAccepted: false,
      cancellationOutcome: 'ALREADY_COMPLETED',
      taskStatus: 'COMPLETED',
      executionMayStillBeStopping: false
    }, 9, 'Task cancellation')).toThrow(expect.objectContaining({
      code: RUN_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('validates server-observed interactive operation stages', () => {
    const status = {
      requestId: 'request-123',
      state: 'RUNNING',
      stage: 'REQUESTING_MODEL',
      elapsedMs: 1250
    }

    expect(validateInteractiveOperationStatus(status)).toEqual(status)
    expect(() => validateInteractiveOperationStatus({
      ...status,
      stage: 'THINKING_FOR_A_WHILE'
    })).toThrow(expect.objectContaining({ code: RUN_RESPONSE_INCOMPLETE_CODE }))
  })

  it('does not present a stale active phase after a task reaches a terminal state', () => {
    expect(activeTaskProgressStage('PERSISTING_RESULT', 'RUNNING')).toBe('PERSISTING_RESULT')
    expect(activeTaskProgressStage('PERSISTING_RESULT', 'COMPLETED')).toBeNull()
    expect(activeTaskProgressStage('EXPLORING_CANDIDATES', 'FAILED')).toBeNull()
    expect(activeTaskProgressStage('STARTING', 'CANCELLED')).toBeNull()
  })
})
