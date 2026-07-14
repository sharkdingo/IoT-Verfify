import { describe, expect, it } from 'vitest'
import { getVerificationOutcome, normalizeSpecResult } from '../verificationResult'

describe('verification result semantics', () => {
  it('does not turn an unknown or legacy boolean result into a violation', () => {
    expect(normalizeSpecResult({ specId: 's1', passed: false })).toEqual({
      specId: 's1',
      templateId: '',
      specificationLabel: '',
      formulaPreview: '',
      formulaKind: 'CTL',
      outcome: 'INCONCLUSIVE',
      expression: ''
    })
    expect(getVerificationOutcome({
      specResults: [{ specId: 's1', passed: false }],
      traces: []
    })).toBe('INCONCLUSIVE')
  })

  it('reports a violation only from an explicit violated result or counterexample', () => {
    expect(getVerificationOutcome({
      specResults: [{ specId: 's1', outcome: 'VIOLATED', expression: 'CTLSPEC AG(x)' }],
      traces: []
    })).toBe('VIOLATED')
    expect(getVerificationOutcome({ specResults: [], traces: [{ id: 1 }] })).toBe('VIOLATED')
  })

  it('keeps a mixed satisfied and inconclusive result set inconclusive', () => {
    expect(getVerificationOutcome({
      specResults: [
        { specId: 's1', outcome: 'SATISFIED' },
        { specId: 's2', outcome: 'INCONCLUSIVE' }
      ],
      traces: []
    })).toBe('INCONCLUSIVE')
  })
})
