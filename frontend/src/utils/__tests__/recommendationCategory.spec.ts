import { describe, expect, it } from 'vitest'
import { formatRecommendationCategory } from '@/utils/recommendationCategory'

const labels: Record<string, string> = {
  'app.recommendationCategorySecurity': 'Security label',
  'app.recommendationCategoryEnergySaving': 'Energy-saving label'
}

describe('recommendation category display', () => {
  it('localizes canonical recommendation categories', () => {
    const translate = (key: string) => labels[key] || key

    expect(formatRecommendationCategory('security', translate)).toBe('Security label')
    expect(formatRecommendationCategory('energy_saving', translate)).toBe('Energy-saving label')
  })

  it('preserves unknown model-provided categories exactly', () => {
    expect(formatRecommendationCategory('custom_category', key => key)).toBe('custom_category')
    expect(formatRecommendationCategory(' Security ', key => key)).toBe(' Security ')
  })
})
