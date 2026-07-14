export const RECOMMENDATION_RESPONSE_INCOMPLETE_CODE = 'RECOMMENDATION_RESPONSE_INCOMPLETE'

class RecommendationResponseContractError extends Error {
  readonly code = RECOMMENDATION_RESPONSE_INCOMPLETE_CODE

  constructor(context: string, detail: string) {
    super(`${context} returned inconsistent candidate accounting: ${detail}`)
    this.name = 'RecommendationResponseContractError'
  }
}

const requireRecord = (value: unknown, context: string): Record<string, any> => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new RecommendationResponseContractError(context, 'result must be an object')
  }
  return value as Record<string, any>
}

const requireArray = (result: Record<string, any>, field: string, context: string): any[] => {
  if (!Array.isArray(result[field])) {
    throw new RecommendationResponseContractError(context, `${field} must be an array`)
  }
  return result[field]
}

const requireCount = (result: Record<string, any>, field: string, context: string): number => {
  const value = result[field]
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new RecommendationResponseContractError(context, `${field} must be a non-negative integer`)
  }
  return value
}

const requireNonBlankText = (value: unknown, field: string, context: string): string => {
  if (typeof value !== 'string' || !value.trim()) {
    throw new RecommendationResponseContractError(context, `${field} must be non-blank text`)
  }
  return value
}

const validateFilteredItems = (items: any[], context: string) => {
  items.forEach((item, index) => {
    const prefix = `filteredItems[${index}]`
    const row = requireRecord(item, context)
    requireNonBlankText(row.type, `${prefix}.type`, context)
    if (!Number.isSafeInteger(row.index) || row.index < 1) {
      throw new RecommendationResponseContractError(context, `${prefix}.index must be a positive integer`)
    }
    requireNonBlankText(row.reasonCode, `${prefix}.reasonCode`, context)
    requireNonBlankText(row.reason, `${prefix}.reason`, context)
    if (row.label !== undefined && row.label !== null && typeof row.label !== 'string') {
      throw new RecommendationResponseContractError(context, `${prefix}.label must be text when present`)
    }
  })
}

const validateAdjustmentItems = (items: any[], context: string) => {
  items.forEach((item, index) => {
    const prefix = `adjustedItems[${index}]`
    const row = requireRecord(item, context)
    requireNonBlankText(row.type, `${prefix}.type`, context)
    if (row.index !== undefined && row.index !== null
      && (!Number.isSafeInteger(row.index) || row.index < 1)) {
      throw new RecommendationResponseContractError(context, `${prefix}.index must be a positive integer when present`)
    }
    requireNonBlankText(row.reasonCode, `${prefix}.reasonCode`, context)
    requireNonBlankText(row.reason, `${prefix}.reason`, context)
    if (row.label !== undefined && row.label !== null && typeof row.label !== 'string') {
      throw new RecommendationResponseContractError(context, `${prefix}.label must be text when present`)
    }
    if (!row.appliedValues || typeof row.appliedValues !== 'object' || Array.isArray(row.appliedValues)) {
      throw new RecommendationResponseContractError(context, `${prefix}.appliedValues must be an object`)
    }
  })
}

const validateAccounting = (
  result: Record<string, any>,
  expectedFinalCount: number,
  context: string,
  requireAdjustments: boolean,
  expectedValidatedCount?: number
) => {
  if (typeof result.message !== 'string' || !result.message.trim()) {
    throw new RecommendationResponseContractError(context, 'message is required')
  }
  const count = requireCount(result, 'count', context)
  requireCount(result, 'requestedCount', context)
  const validatedCount = requireCount(result, 'validatedCount', context)
  const filteredCount = requireCount(result, 'filteredCount', context)
  const rawCandidateCount = requireCount(result, 'rawCandidateCount', context)
  const inspectedCount = requireCount(result, 'inspectedCount', context)
  const truncatedCount = requireCount(result, 'truncatedCount', context)
  const filteredItems = requireArray(result, 'filteredItems', context)

  if (count !== expectedFinalCount) {
    throw new RecommendationResponseContractError(context, 'count must match final returned items')
  }
  if (expectedValidatedCount !== undefined && validatedCount !== expectedValidatedCount) {
    throw new RecommendationResponseContractError(context, 'validatedCount must match kept raw candidates')
  }
  if (filteredCount !== filteredItems.length) {
    throw new RecommendationResponseContractError(context, 'filteredCount must match filteredItems')
  }
  validateFilteredItems(filteredItems, context)
  if (inspectedCount !== validatedCount + filteredCount) {
    throw new RecommendationResponseContractError(context, 'inspectedCount must equal kept plus rejected candidates')
  }
  if (rawCandidateCount !== inspectedCount + truncatedCount) {
    throw new RecommendationResponseContractError(context, 'rawCandidateCount must equal inspected plus uninspected candidates')
  }

  const hasAdjustmentFields = Object.prototype.hasOwnProperty.call(result, 'adjustedCount')
    || Object.prototype.hasOwnProperty.call(result, 'adjustedItems')
  if (requireAdjustments || hasAdjustmentFields) {
    const adjustedCount = requireCount(result, 'adjustedCount', context)
    const adjustedItems = requireArray(result, 'adjustedItems', context)
    if (adjustedCount !== adjustedItems.length) {
      throw new RecommendationResponseContractError(context, 'adjustedCount must match adjustedItems')
    }
    validateAdjustmentItems(adjustedItems, context)
  }
}

export const validateStandaloneRecommendationResponse = <T>(
  value: unknown,
  context: string,
  validateCandidate?: (value: unknown, index: number) => void,
  requireAdjustments = false
): T => {
  const result = requireRecord(value, context)
  const recommendations = requireArray(result, 'recommendations', context)
  validateAccounting(result, recommendations.length, context, requireAdjustments, recommendations.length)
  recommendations.forEach((candidate, index) => validateCandidate?.(candidate, index))
  return result as T
}

export const validateScenarioRecommendationResponse = <T>(
  value: unknown,
  context: string
): T => {
  const result = requireRecord(value, context)
  if (!result.scene || typeof result.scene !== 'object' || Array.isArray(result.scene)) {
    throw new RecommendationResponseContractError(context, 'scene is required')
  }
  const scene = result.scene as Record<string, any>
  const devices = requireArray(scene, 'devices', context)
  const environmentVariables = requireArray(scene, 'environmentVariables', context)
  const rules = requireArray(scene, 'rules', context)
  const specs = requireArray(scene, 'specs', context)
  requireArray(scene, 'templates', context)
  const finalItemCount = devices.length + environmentVariables.length + rules.length + specs.length
  validateAccounting(result, finalItemCount, context, true)
  if (typeof result.scenarioName !== 'string' || typeof result.rationale !== 'string') {
    throw new RecommendationResponseContractError(context, 'scenarioName and rationale are required')
  }
  return result as T
}
