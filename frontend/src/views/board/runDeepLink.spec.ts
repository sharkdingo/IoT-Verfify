import { describe, expect, it } from 'vitest'

import {
  applyBoardRunTarget,
  hasUnusableBoardRunParams,
  isSameBoardRunTarget,
  parseBoardRunTarget
} from './runDeepLink'

describe('parseBoardRunTarget', () => {
  it('reads each supported run kind', () => {
    expect(parseBoardRunTarget({ run: 'verification:12' })).toEqual({ kind: 'verification', runId: 12 })
    expect(parseBoardRunTarget({ run: 'simulation:3' })).toEqual({ kind: 'simulation', runId: 3 })
    expect(parseBoardRunTarget({ run: 'exploration:7' })).toEqual({ kind: 'exploration', runId: 7 })
  })

  it('reads the sub-artifact that belongs to the run kind', () => {
    expect(parseBoardRunTarget({ run: 'verification:12', trace: '34' }))
      .toEqual({ kind: 'verification', runId: 12, traceId: 34 })
    expect(parseBoardRunTarget({ run: 'exploration:7', finding: '9' }))
      .toEqual({ kind: 'exploration', runId: 7, findingId: 9 })
  })

  it('rejects a sub-artifact that does not belong to the run kind', () => {
    // Dropping the mismatched param instead would restore a surface the link never described.
    expect(parseBoardRunTarget({ run: 'verification:12', finding: '9' })).toBeNull()
    expect(parseBoardRunTarget({ run: 'exploration:7', trace: '34' })).toBeNull()
    expect(parseBoardRunTarget({ run: 'simulation:3', trace: '34' })).toBeNull()
    expect(parseBoardRunTarget({ run: 'simulation:3', finding: '9' })).toBeNull()
  })

  it('rejects malformed, unknown, and out-of-domain values', () => {
    for (const run of [
      '', 'verification', 'verification:', ':12', 'verification:0', 'verification:-1',
      'verification:1.5', 'verification:abc', 'unknown:12', 'VERIFICATION:12',
      'verification:12:34', 'verification:99999999999999999999'
    ]) {
      expect(parseBoardRunTarget({ run }), run).toBeNull()
    }
  })

  it('ignores an absent deep link and unrelated params', () => {
    expect(parseBoardRunTarget({})).toBeNull()
    expect(parseBoardRunTarget({ trace: '34' })).toBeNull()
    expect(parseBoardRunTarget({ mode: 'login' })).toBeNull()
  })

  it('treats a repeated param as its first occurrence', () => {
    expect(parseBoardRunTarget({ run: ['verification:12', 'simulation:3'] }))
      .toEqual({ kind: 'verification', runId: 12 })
  })

  it('drops a non-numeric sub-artifact but keeps the valid run it hangs off', () => {
    // Deliberate: a malformed `trace` must not invalidate the run the user actually opened.
    expect(parseBoardRunTarget({ run: 'verification:12', trace: 'abc' }))
      .toEqual({ kind: 'verification', runId: 12 })
  })
})

describe('applyBoardRunTarget', () => {
  it('writes the target and preserves unrelated params', () => {
    expect(applyBoardRunTarget({ locale: 'en' }, { kind: 'verification', runId: 12, traceId: 34 }))
      .toEqual({ locale: 'en', run: 'verification:12', trace: '34' })
  })

  it('omits a sub-artifact that the kind does not own', () => {
    expect(applyBoardRunTarget({}, { kind: 'simulation', runId: 3, traceId: 34 }))
      .toEqual({ run: 'simulation:3' })
    expect(applyBoardRunTarget({}, { kind: 'exploration', runId: 7, findingId: 9 }))
      .toEqual({ run: 'exploration:7', finding: '9' })
  })

  it('clears every deep-link param when the target is null', () => {
    expect(applyBoardRunTarget({ run: 'verification:1', trace: '2', finding: '3', keep: 'yes' }, null))
      .toEqual({ keep: 'yes' })
  })

  it('round-trips every target it can encode', () => {
    for (const target of [
      { kind: 'verification' as const, runId: 12 },
      { kind: 'verification' as const, runId: 12, traceId: 34 },
      { kind: 'simulation' as const, runId: 3 },
      { kind: 'exploration' as const, runId: 7 },
      { kind: 'exploration' as const, runId: 7, findingId: 9 }
    ]) {
      expect(parseBoardRunTarget(applyBoardRunTarget({}, target))).toEqual(target)
    }
  })
})

describe('isSameBoardRunTarget', () => {
  it('compares identity including sub-artifacts', () => {
    const base = { kind: 'verification' as const, runId: 12, traceId: 34 }
    expect(isSameBoardRunTarget(base, { ...base })).toBe(true)
    expect(isSameBoardRunTarget(base, { kind: 'verification', runId: 12 })).toBe(false)
    expect(isSameBoardRunTarget(base, { kind: 'verification', runId: 13, traceId: 34 })).toBe(false)
    expect(isSameBoardRunTarget(null, null)).toBe(true)
    expect(isSameBoardRunTarget(null, base)).toBe(false)
  })
})

describe('hasUnusableBoardRunParams', () => {
  it('flags present-but-invalid params so the UI can explain the stale link', () => {
    expect(hasUnusableBoardRunParams({ run: 'verification:abc' })).toBe(true)
    expect(hasUnusableBoardRunParams({ run: 'exploration:7', trace: '3' })).toBe(true)
    expect(hasUnusableBoardRunParams({ trace: '3' })).toBe(true)
  })

  it('does not flag a clean board or a valid link', () => {
    expect(hasUnusableBoardRunParams({})).toBe(false)
    expect(hasUnusableBoardRunParams({ locale: 'en' })).toBe(false)
    expect(hasUnusableBoardRunParams({ run: 'verification:12', trace: '34' })).toBe(false)
  })
})
