import { beforeEach, describe, expect, it, vi } from 'vitest'

vi.mock('./http', () => ({
  default: {
    post: vi.fn()
  }
}))

import http from './http'
import { cancelRecommendRules, recommendRules } from './rules'
import { isRecommendationPostOutcomeUnknown } from '@/utils/recommendationRequestRecovery'

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
    vi.mocked(http.post)
      .mockImplementationOnce(() => new Promise(resolve => { resolveFirst = resolve }))
      .mockImplementationOnce(() => new Promise(resolve => { resolveSecond = resolve }))

    const first = recommendRules({ authToken: 'alice-token', requestId: 'rule-request-1' })
    const firstSignal = vi.mocked(http.post).mock.calls[0][2]?.signal as AbortSignal
    const second = recommendRules({ authToken: 'alice-token', requestId: 'rule-request-2' })
    const secondSignal = vi.mocked(http.post).mock.calls[1][2]?.signal as AbortSignal

    expect(vi.mocked(http.post).mock.calls[0][1]).toMatchObject({ requestId: 'rule-request-1' })
    expect(vi.mocked(http.post).mock.calls[0][2]).toMatchObject({
      timeout: 0,
      headers: { Authorization: 'Bearer alice-token' }
    })
    expect(vi.mocked(http.post).mock.calls[1][2]).toMatchObject({
      headers: { Authorization: 'Bearer alice-token' }
    })

    expect(firstSignal.aborted).toBe(true)
    expect(secondSignal.aborted).toBe(false)

    resolveFirst(resultEnvelope(emptyRecommendationResponse()))
    await first

    cancelRecommendRules()
    expect(secondSignal.aborted).toBe(true)

    resolveSecond(resultEnvelope(emptyRecommendationResponse()))
    await second
  })

  it('distinguishes transport loss from a malformed body received over HTTP', async () => {
    const transportError = new Error('connection reset')
    vi.mocked(http.post).mockRejectedValueOnce(transportError)

    await expect(recommendRules({
      authToken: 'alice-token',
      requestId: 'rule-transport-loss'
    })).rejects.toSatisfy(isRecommendationPostOutcomeUnknown)

    vi.mocked(http.post).mockResolvedValueOnce(resultEnvelope({ message: 'malformed response' }))
    let validationError: unknown
    try {
      await recommendRules({
        authToken: 'alice-token',
        requestId: 'rule-malformed-response'
      })
    } catch (error) {
      validationError = error
    }
    expect(validationError).toBeInstanceOf(Error)
    expect(isRecommendationPostOutcomeUnknown(validationError)).toBe(false)
  })
})
