import { describe, expect, it } from 'vitest'
import type { Specification } from '@/types/spec'
import {
  getKnownFuzzingSpecificationIssue,
  getFuzzingConfigurationIssue,
  isKnownFuzzingSpecificationSupported,
  isKnownFuzzingTemplateSupported
} from '../fuzzingConfig'

const config = {
  maxIterations: 500,
  pathLength: 20,
  populationSize: 10,
  targetSpecIds: [] as string[]
}

describe('fuzzing configuration limits', () => {
  it('recognizes only the finite-trace templates supported by the current explorer', () => {
    expect(isKnownFuzzingTemplateSupported('1')).toBe(true)
    expect(isKnownFuzzingTemplateSupported(3)).toBe(true)
    expect(isKnownFuzzingTemplateSupported('4')).toBe(true)
    expect(isKnownFuzzingTemplateSupported('2')).toBe(false)
    expect(isKnownFuzzingTemplateSupported('7')).toBe(false)
  })

  it('keeps typed trust and privacy conditions outside the finite explorer', () => {
    const specification: Specification = {
      id: 'security-spec',
      templateId: '1',
      templateLabel: 'Security',
      aConditions: [{
        id: 'condition-1',
        side: 'a',
        deviceId: 'device-1',
        deviceLabel: 'Device',
        targetType: 'trust',
        key: 'PowerMode',
        propertyScope: 'state',
        relation: '=',
        value: 'trusted'
      }],
      ifConditions: [],
      thenConditions: []
    }
    expect(getKnownFuzzingSpecificationIssue(specification))
      .toBe('TRUST_PRIVACY_UNSUPPORTED')
    expect(isKnownFuzzingSpecificationSupported(specification)).toBe(false)
    expect(isKnownFuzzingSpecificationSupported({
      ...specification,
      aConditions: [{ ...specification.aConditions[0], targetType: 'state' }]
    })).toBe(true)
  })

  it('rejects invalid integer fields instead of relying on silent normalization', () => {
    expect(getFuzzingConfigurationIssue({ ...config, maxIterations: 0 }, 1))
      .toMatchObject({ code: 'INVALID_INTEGER_FIELD', field: 'maxIterations' })
    expect(getFuzzingConfigurationIssue({ ...config, pathLength: 1.5 }, 1))
      .toMatchObject({ code: 'INVALID_INTEGER_FIELD', field: 'pathLength' })
    expect(getFuzzingConfigurationIssue({ ...config, seed: -1 }, 1))
      .toMatchObject({ code: 'INVALID_INTEGER_FIELD', field: 'seed' })
  })

  it('requires an explicit bounded selection when the board has over 100 specifications', () => {
    expect(getFuzzingConfigurationIssue(config, 101)).toMatchObject({
      code: 'TARGET_SELECTION_REQUIRED',
      availableSpecCount: 101,
      limit: 100
    })
    expect(getFuzzingConfigurationIssue({ ...config, targetSpecIds: ['spec-1'] }, 101)).toBeNull()
  })

  it('uses only the backend assessment for the frozen-model workload ceiling', () => {
    expect(getFuzzingConfigurationIssue(config, 2)).toBeNull()
    expect(getFuzzingConfigurationIssue({
      maxIterations: 5_000,
      pathLength: 50,
      populationSize: 50,
      targetSpecIds: ['spec-1', 'spec-2']
    }, 2, {
      workload: 12_740_000,
      limit: 12_500_000
    })).toEqual({
      code: 'WORKLOAD_EXCEEDED',
      workload: 12_740_000,
      limit: 12_500_000
    })
  })
})
