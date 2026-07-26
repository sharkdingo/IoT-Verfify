import type { SpecResult, VerificationOutcome } from '@/types/verify'

export const normalizeSpecResult = (value: unknown): SpecResult => {
  const candidate = value as Partial<SpecResult> | undefined
  const expression = candidate?.expression || ''
  return {
    specId: candidate?.specId || '',
    templateId: candidate?.templateId || '',
    specificationLabel: candidate?.specificationLabel || '',
    formulaPreview: candidate?.formulaPreview || '',
    formulaKind: candidate?.formulaKind === 'LTL'
      || String(expression).trim().toUpperCase().startsWith('LTLSPEC') ? 'LTL' : 'CTL',
    outcome: candidate?.outcome === 'SATISFIED' || candidate?.outcome === 'VIOLATED'
      || candidate?.outcome === 'INCONCLUSIVE'
      ? candidate.outcome
      : 'INCONCLUSIVE',
    expression
  }
}

export const normalizeSpecResults = (results?: unknown[]): SpecResult[] =>
  (results || []).map(result => normalizeSpecResult(result))

export const getVerificationOutcome = (result: any): VerificationOutcome => {
  if (result?.outcome === 'SATISFIED' || result?.outcome === 'VIOLATED' || result?.outcome === 'INCONCLUSIVE') {
    return result.outcome
  }
  if ((result?.checkLogs || []).some((log: unknown) => String(log).includes('[verification-inconclusive]'))) {
    return 'INCONCLUSIVE'
  }
  if ((result?.traces?.length || 0) > 0) return 'VIOLATED'

  const specResults = normalizeSpecResults(result?.specResults)
  if (specResults.some(specResult => specResult.outcome === 'VIOLATED')) return 'VIOLATED'
  if (specResults.some(specResult => specResult.outcome === 'INCONCLUSIVE')) return 'INCONCLUSIVE'
  if (specResults.length > 0 && specResults.every(specResult => specResult.outcome === 'SATISFIED')) {
    return 'SATISFIED'
  }
  return 'INCONCLUSIVE'
}
