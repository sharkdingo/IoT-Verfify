import { beforeEach, describe, expect, it, vi } from 'vitest'

vi.mock('./http', () => ({
  default: {
    get: vi.fn()
  }
}))

import http from './http'
import { cancelRecommendRules, recommendRules } from './rules'

const resultEnvelope = (data: unknown) => ({ data: { data } })

const emptyRecommendationResponse = () => ({
  message: 'No applicable recommendations.',
  count: 0,
  requestedCount: 5,
  validatedCount: 0,
  filteredCount: 0,
  filteredItems: [],
  adjustedCount: 0,
  adjustedItems: [],
  rawCandidateCount: 0,
  inspectedCount: 0,
  truncatedCount: 0,
  recommendations: []
})

describe('rule recommendation request ownership', () => {
  beforeEach(() => {
    cancelRecommendRules()
    vi.clearAllMocks()
  })

  it('does not let an older request clear the controller owned by a newer request', async () => {
    let resolveFirst!: (value: unknown) => void
    let resolveSecond!: (value: unknown) => void
    vi.mocked(http.get)
      .mockImplementationOnce(() => new Promise(resolve => { resolveFirst = resolve }))
      .mockImplementationOnce(() => new Promise(resolve => { resolveSecond = resolve }))

    const first = recommendRules()
    const firstSignal = vi.mocked(http.get).mock.calls[0][1]?.signal as AbortSignal
    const second = recommendRules()
    const secondSignal = vi.mocked(http.get).mock.calls[1][1]?.signal as AbortSignal

    expect(firstSignal.aborted).toBe(true)
    expect(secondSignal.aborted).toBe(false)

    resolveFirst(resultEnvelope(emptyRecommendationResponse()))
    await first

    cancelRecommendRules()
    expect(secondSignal.aborted).toBe(true)

    resolveSecond(resultEnvelope(emptyRecommendationResponse()))
    await second
  })
})
