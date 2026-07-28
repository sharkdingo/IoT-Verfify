import type { RecommendationFilteredItem } from '@/types/recommendation'
import { localizedTextOrFallback } from '@/utils/userMessage'

/**
 * User-facing wording for candidates the server filtered out of a recommendation.
 *
 * Pure presentation: it takes the translator and locale as arguments instead of reading them from a
 * component, so the wording rules — which candidate kinds exist, and that a backend `reason` is only
 * shown when it matches the active locale — can be tested without mounting the board.
 */

export type RecommendationFilteredType =
  | 'device'
  | 'rule'
  | 'spec'
  | 'specification'
  | 'environment'
  | 'environmentVariable'

export interface RecommendationTextContext {
  t: (key: string, named?: Record<string, unknown>) => string
  locale: string
}

/** Translation keys per candidate kind. `spec`/`specification` and the two environment spellings are both accepted because the backend has used each. */
const TYPE_KEYS: Record<string, string> = {
  device: 'app.filteredCandidateDevice',
  rule: 'app.filteredCandidateRule',
  spec: 'app.filteredCandidateSpecification',
  specification: 'app.filteredCandidateSpecification',
  environment: 'app.filteredCandidateEnvironment',
  environmentvariable: 'app.filteredCandidateEnvironment'
}

export const formatRecommendationFilteredType = (
  type: unknown,
  { t }: RecommendationTextContext
): string => t(TYPE_KEYS[String(type || '').toLowerCase()] || 'app.filteredCandidateItem')

/**
 * One filtered candidate as a single sentence.
 *
 * The backend `reason` is free text, so it is only surfaced when it matches the active locale;
 * otherwise a translated fallback is used rather than showing the user the wrong language.
 */
export const formatRecommendationFilteredItem = (
  item: RecommendationFilteredItem,
  context: RecommendationTextContext
): string => {
  const { t, locale } = context
  const index = item.index || '?'
  const reason = localizedTextOrFallback(
    item.reason,
    t('app.recommendationFilteredUnknownReason'),
    locale
  )
  const type = formatRecommendationFilteredType(item.type, context)
  const label = item.label?.trim()
  return label
    ? t('app.recommendationFilteredReasonWithLabel', { type, index, label, reason })
    : t('app.recommendationFilteredReason', { type, index, reason })
}
