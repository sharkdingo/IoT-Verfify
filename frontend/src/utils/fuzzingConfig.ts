import type { Specification } from '@/types/spec'

export const FUZZ_ITERATIONS_MIN = 1
export const FUZZ_ITERATIONS_MAX = 5_000
export const FUZZ_PATH_LENGTH_MIN = 1
export const FUZZ_PATH_LENGTH_MAX = 50
export const FUZZ_POPULATION_MIN = 1
export const FUZZ_POPULATION_MAX = 50
export const FUZZ_TARGET_SPEC_MAX = 100
export const FUZZ_SEED_MAX = Number.MAX_SAFE_INTEGER
export const FUZZ_SUPPORTED_TEMPLATE_IDS = new Set(['1', '3', '4'])

export const isKnownFuzzingTemplateSupported = (templateId: unknown): boolean =>
  FUZZ_SUPPORTED_TEMPLATE_IDS.has(String(templateId ?? '').trim())

export type KnownFuzzingSpecificationIssue =
  | 'UNSUPPORTED_TEMPLATE'
  | 'TRUST_PRIVACY_UNSUPPORTED'

export const getKnownFuzzingSpecificationIssue = (
  specification: Pick<Specification, 'templateId' | 'aConditions' | 'ifConditions' | 'thenConditions'>
): KnownFuzzingSpecificationIssue | null => {
  if (!isKnownFuzzingTemplateSupported(specification.templateId)) return 'UNSUPPORTED_TEMPLATE'
  const conditions = [
    ...(specification.aConditions || []),
    ...(specification.ifConditions || []),
    ...(specification.thenConditions || [])
  ]
  return conditions.some(condition => {
    const targetType = String(condition?.targetType ?? '').trim().toLowerCase()
    return targetType === 'trust' || targetType === 'privacy'
  })
    ? 'TRUST_PRIVACY_UNSUPPORTED'
    : null
}

export const isKnownFuzzingSpecificationSupported = (
  specification: Pick<Specification, 'templateId' | 'aConditions' | 'ifConditions' | 'thenConditions'>
): boolean => getKnownFuzzingSpecificationIssue(specification) === null

export interface FuzzingWorkloadConfig {
  maxIterations: number
  pathLength: number
  populationSize: number
  seed?: number | null
  targetSpecIds: string[]
}

export interface FuzzingWorkloadAssessment {
  workload: number
  limit: number
}

export type FuzzingConfigurationIssue =
  | {
      code: 'INVALID_INTEGER_FIELD'
      field: 'maxIterations' | 'pathLength' | 'populationSize' | 'seed'
      minimum: number
      maximum: number
    }
  | { code: 'TARGET_SELECTION_REQUIRED'; availableSpecCount: number; limit: number }
  | { code: 'TOO_MANY_TARGETS'; selectedSpecCount: number; limit: number }
  | { code: 'WORKLOAD_EXCEEDED'; workload: number; limit: number }

export const getFuzzingConfigurationIssue = (
  config: FuzzingWorkloadConfig,
  availableSpecCount: number,
  workloadAssessment?: FuzzingWorkloadAssessment | null
): FuzzingConfigurationIssue | null => {
  const integerFields = [
    ['maxIterations', config.maxIterations, FUZZ_ITERATIONS_MIN, FUZZ_ITERATIONS_MAX],
    ['pathLength', config.pathLength, FUZZ_PATH_LENGTH_MIN, FUZZ_PATH_LENGTH_MAX],
    ['populationSize', config.populationSize, FUZZ_POPULATION_MIN, FUZZ_POPULATION_MAX]
  ] as const
  for (const [field, value, minimum, maximum] of integerFields) {
    if (!Number.isSafeInteger(value) || value < minimum || value > maximum) {
      return { code: 'INVALID_INTEGER_FIELD', field, minimum, maximum }
    }
  }
  if (config.seed !== undefined && config.seed !== null
    && (!Number.isSafeInteger(config.seed) || config.seed < 0 || config.seed > FUZZ_SEED_MAX)) {
    return {
      code: 'INVALID_INTEGER_FIELD',
      field: 'seed',
      minimum: 0,
      maximum: FUZZ_SEED_MAX
    }
  }
  if (availableSpecCount > FUZZ_TARGET_SPEC_MAX && config.targetSpecIds.length === 0) {
    return {
      code: 'TARGET_SELECTION_REQUIRED',
      availableSpecCount,
      limit: FUZZ_TARGET_SPEC_MAX
    }
  }
  if (config.targetSpecIds.length > FUZZ_TARGET_SPEC_MAX) {
    return {
      code: 'TOO_MANY_TARGETS',
      selectedSpecCount: config.targetSpecIds.length,
      limit: FUZZ_TARGET_SPEC_MAX
    }
  }
  if (workloadAssessment
    && (!Number.isSafeInteger(workloadAssessment.workload)
      || workloadAssessment.workload > workloadAssessment.limit)) {
    return {
      code: 'WORKLOAD_EXCEEDED',
      workload: workloadAssessment.workload,
      limit: workloadAssessment.limit
    }
  }
  return null
}
