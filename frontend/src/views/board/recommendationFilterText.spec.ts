import { describe, expect, it } from 'vitest'

import type { RecommendationFilteredItem } from '@/types/recommendation'
import {
  formatRecommendationFilteredItem,
  formatRecommendationFilteredType
} from './recommendationFilterText'

const filtered = (over: Partial<RecommendationFilteredItem>): RecommendationFilteredItem => ({
  type: 'device',
  index: 1,
  reasonCode: 'FILTERED',
  reason: 'Duplicate of an existing device',
  ...over
})

/** Echoes the key plus its interpolations, so tests assert wording *rules*, not copy. */
const context = (locale = 'en') => ({
  locale,
  t: (key: string, named?: Record<string, unknown>) =>
    named ? `${key}(${JSON.stringify(named)})` : key
})

describe('formatRecommendationFilteredType', () => {
  it('names each candidate kind the backend can report', () => {
    const ctx = context()
    expect(formatRecommendationFilteredType('device', ctx)).toBe('app.filteredCandidateDevice')
    expect(formatRecommendationFilteredType('rule', ctx)).toBe('app.filteredCandidateRule')
    expect(formatRecommendationFilteredType('environment', ctx)).toBe('app.filteredCandidateEnvironment')
  })

  it('accepts both spellings the backend has used for the same kind', () => {
    const ctx = context()
    expect(formatRecommendationFilteredType('spec', ctx))
      .toBe(formatRecommendationFilteredType('specification', ctx))
    expect(formatRecommendationFilteredType('environmentVariable', ctx))
      .toBe(formatRecommendationFilteredType('environment', ctx))
  })

  it('is case-insensitive and falls back to a generic label', () => {
    const ctx = context()
    expect(formatRecommendationFilteredType('DEVICE', ctx)).toBe('app.filteredCandidateDevice')
    // An unknown kind must still produce readable text rather than leaking the raw token.
    for (const unknown of ['', null, undefined, 'wat', 42]) {
      expect(formatRecommendationFilteredType(unknown, ctx)).toBe('app.filteredCandidateItem')
    }
  })
})

describe('formatRecommendationFilteredItem', () => {
  it('includes the label when the candidate has one', () => {
    const text = formatRecommendationFilteredItem(
      filtered({ index: 2, label: ' Kitchen Light ' }),
      context()
    )
    expect(text).toContain('app.recommendationFilteredReasonWithLabel')
    // Trimmed, so stray whitespace from the model does not reach the sentence.
    expect(text).toContain('"label":"Kitchen Light"')
    expect(text).toContain('"index":2')
  })

  it('omits the label form when there is no usable label', () => {
    for (const label of [undefined, '', '   ']) {
      const text = formatRecommendationFilteredItem(
        filtered({ type: 'rule', label, reason: 'Not applicable' }),
        context()
      )
      expect(text, String(label)).toContain('app.recommendationFilteredReason(')
      expect(text, String(label)).not.toContain('WithLabel')
    }
  })

  it('shows a missing index as a placeholder rather than a bare zero', () => {
    const text = formatRecommendationFilteredItem(
      filtered({ type: 'rule', index: 0 as never, reason: 'Not applicable' }),
      context()
    )
    expect(text).toContain('"index":"?"')
  })

  it('only surfaces a backend reason that matches the active locale', () => {
    const english = 'Duplicate of an existing device'
    expect(formatRecommendationFilteredItem(
      filtered({ reason: english }), context('en')
    )).toContain(english)

    // A reason in the wrong language is replaced by a translated fallback: showing the user text
    // they cannot read is worse than showing a generic explanation.
    expect(formatRecommendationFilteredItem(
      filtered({ reason: english }), context('zh-CN')
    )).toContain('app.recommendationFilteredUnknownReason')
  })

  it('falls back when the reason is absent or blank', () => {
    for (const reason of [undefined, '', '  ']) {
      expect(formatRecommendationFilteredItem(
        filtered({ reason: reason as string }), context()
      ), String(reason)).toContain('app.recommendationFilteredUnknownReason')
    }
  })
})
