export type RecommendationCategoryTranslator = (key: string) => string

export const RULE_RECOMMENDATION_CATEGORY_OPTIONS = [
  { value: 'all', labelKey: 'app.recommendationCategoryAll' },
  { value: 'security', labelKey: 'app.recommendationCategorySecurity' },
  { value: 'energy_saving', labelKey: 'app.recommendationCategoryEnergySaving' },
  { value: 'comfort', labelKey: 'app.recommendationCategoryComfort' },
  { value: 'automation', labelKey: 'app.recommendationCategoryAutomation' }
] as const

export const SPEC_RECOMMENDATION_CATEGORY_OPTIONS = [
  { value: 'all', labelKey: 'app.recommendationCategoryAll' },
  { value: 'safety', labelKey: 'app.recommendationCategorySafety' },
  { value: 'response', labelKey: 'app.recommendationCategoryResponse' },
  { value: 'consistency', labelKey: 'app.recommendationCategoryConsistency' },
  { value: 'privacy', labelKey: 'app.recommendationCategoryPrivacy' }
] as const

const RECOMMENDATION_CATEGORY_LABEL_KEYS: Readonly<Record<string, string>> = Object.fromEntries(
  [...RULE_RECOMMENDATION_CATEGORY_OPTIONS, ...SPEC_RECOMMENDATION_CATEGORY_OPTIONS]
    .map(option => [option.value, option.labelKey])
)

export const formatRecommendationCategory = (
  value: unknown,
  translate: RecommendationCategoryTranslator
): string => {
  const raw = value === null || value === undefined ? '' : String(value)
  const key = RECOMMENDATION_CATEGORY_LABEL_KEYS[raw]
  return key ? translate(key) : raw
}
