import { describe, expect, it } from 'vitest'
import {
  RECOMMENDATION_RESPONSE_INCOMPLETE_CODE,
  validateScenarioRecommendationResponse,
  validateStandaloneRecommendationResponse
} from '../recommendationResponse'

const validStandalone = () => ({
  message: 'One candidate was kept.',
  count: 1,
  requestedCount: 3,
  validatedCount: 1,
  filteredCount: 1,
  filteredItems: [{
    type: 'rule',
    index: 2,
    reasonCode: 'unknownAction',
    reason: 'Unknown action'
  }],
  rawCandidateCount: 3,
  inspectedCount: 2,
  truncatedCount: 1,
  recommendations: [{ description: 'Keep this one' }]
})

describe('recommendation candidate accounting', () => {
  it('accepts kept, rejected, and uninspected candidates when all counts reconcile', () => {
    expect(validateStandaloneRecommendationResponse(validStandalone(), 'Rules')).toEqual(validStandalone())
  })

  it('runs candidate validation before returning a kept recommendation', () => {
    expect(() => validateStandaloneRecommendationResponse(
      validStandalone(),
      'Rules',
      () => { throw new Error('candidate is not applicable') }
    )).toThrow('candidate is not applicable')
  })

  it('requires adjustment accounting when the endpoint contract promises normalized candidates', () => {
    expect(() => validateStandaloneRecommendationResponse(
      validStandalone(),
      'Rules',
      undefined,
      true
    )).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))

    const withAdjustments = {
      ...validStandalone(),
      adjustedCount: 1,
      adjustedItems: [{
        type: 'rule',
        index: 1,
        reasonCode: 'apiEventSyntaxNormalized',
        reason: 'Equivalent event syntax normalized.',
        label: 'Keep this one',
        appliedValues: { sourceApi: 'motionDetected' }
      }]
    }
    expect(validateStandaloneRecommendationResponse(
      withAdjustments,
      'Rules',
      undefined,
      true
    )).toEqual(withAdjustments)
  })

  it('rejects a filtered count without the same number of itemized reasons', () => {
    expect(() => validateStandaloneRecommendationResponse({
      ...validStandalone(),
      filteredItems: []
    }, 'Rules')).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('rejects candidates that disappear from raw-to-inspected accounting', () => {
    expect(() => validateStandaloneRecommendationResponse({
      ...validStandalone(),
      rawCandidateCount: 4
    }, 'Rules')).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('accepts a scenario whose final count includes a synthesized environment value', () => {
    const result = {
      message: 'Scenario generated.',
      count: 2,
      requestedCount: 3,
      validatedCount: 1,
      filteredCount: 0,
      filteredItems: [],
      adjustedCount: 1,
      adjustedItems: [{
        type: 'environment',
        reasonCode: 'missingEnvironmentAdded',
        reason: 'A required environment value was added.',
        label: 'temperature',
        appliedValues: { value: '20', trust: 'trusted', privacy: 'public' }
      }],
      rawCandidateCount: 1,
      inspectedCount: 1,
      truncatedCount: 0,
      scenarioName: 'Home',
      rationale: '',
      verificationReady: false,
      readinessIssues: [{ code: 'NO_SPECIFICATIONS', message: 'Add a specification.' }],
      scene: {
        templates: [],
        devices: [{}],
        environmentVariables: [{}],
        rules: [],
        specs: []
      }
    }

    expect(validateScenarioRecommendationResponse(result, 'Scenario')).toEqual(result)
  })

  it('requires scenario adjustment details to match their count', () => {
    expect(() => validateScenarioRecommendationResponse({
      message: 'Scenario generated.',
      count: 1,
      requestedCount: 3,
      validatedCount: 1,
      filteredCount: 0,
      filteredItems: [],
      adjustedCount: 1,
      adjustedItems: [],
      rawCandidateCount: 1,
      inspectedCount: 1,
      truncatedCount: 0,
      scenarioName: 'Home',
      rationale: '',
      verificationReady: false,
      readinessIssues: [{ code: 'NO_SPECIFICATIONS', message: 'Add a specification.' }],
      scene: { templates: [], devices: [{}], environmentVariables: [], rules: [], specs: [] }
    }, 'Scenario')).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('rejects scenario readiness that contradicts the scene', () => {
    expect(() => validateScenarioRecommendationResponse({
      message: 'Scenario generated.',
      count: 1,
      requestedCount: 3,
      validatedCount: 1,
      filteredCount: 0,
      filteredItems: [],
      adjustedCount: 0,
      adjustedItems: [],
      rawCandidateCount: 1,
      inspectedCount: 1,
      truncatedCount: 0,
      scenarioName: 'Home',
      rationale: '',
      verificationReady: true,
      readinessIssues: [],
      scene: { templates: [], devices: [{}], environmentVariables: [], rules: [], specs: [] }
    }, 'Scenario')).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))
  })

  it('rejects a filtered candidate without an itemized reason code', () => {
    expect(() => validateStandaloneRecommendationResponse({
      ...validStandalone(),
      filteredItems: [{ type: 'rule', index: 2, reason: 'Unknown action' }]
    }, 'Rules')).toThrow(expect.objectContaining({
      code: RECOMMENDATION_RESPONSE_INCOMPLETE_CODE
    }))
  })
})
