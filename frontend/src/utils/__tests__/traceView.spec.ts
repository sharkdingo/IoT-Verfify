import { describe, it, expect } from 'vitest'
import { canOpenTracePlayback, deriveTraceContext } from '../traceView'

describe('canOpenTracePlayback', () => {
  it('allows playback when no conflicting panel is open', () => {
    const r = canOpenTracePlayback({ simulationVisible: false, recommendationPanelVisible: false })
    expect(r.allowed).toBe(true)
    expect(r.reason).toBe('')
  })

  it('blocks playback while the simulation timeline is visible', () => {
    const r = canOpenTracePlayback({ simulationVisible: true, recommendationPanelVisible: false })
    expect(r.allowed).toBe(false)
    expect(r.reason).toMatch(/simulation timeline/i)
  })

  it('blocks playback while the recommendations panel is visible', () => {
    const r = canOpenTracePlayback({ simulationVisible: false, recommendationPanelVisible: true })
    expect(r.allowed).toBe(false)
    expect(r.reason).toMatch(/recommendations/i)
  })

  it('prefers the simulation message when both are open', () => {
    const r = canOpenTracePlayback({ simulationVisible: true, recommendationPanelVisible: true })
    expect(r.allowed).toBe(false)
    expect(r.reason).toMatch(/simulation timeline/i)
  })
})

describe('deriveTraceContext', () => {
  const form = { isAttack: false, intensity: 3 }

  it('uses the trace own context when isAttack is set', () => {
    const ctx = deriveTraceContext({ isAttack: true, intensity: 12 }, form)
    expect(ctx).toEqual({ isAttack: true, intensity: 12 })
  })

  it('reflects a non-attack trace even when the live form has attack on', () => {
    const ctx = deriveTraceContext({ isAttack: false, intensity: 0 }, { isAttack: true, intensity: 40 })
    expect(ctx).toEqual({ isAttack: false, intensity: 0 })
  })

  it('falls back to the live form for legacy traces (isAttack undefined)', () => {
    const ctx = deriveTraceContext({ isAttack: undefined, intensity: undefined }, { isAttack: true, intensity: 9 })
    expect(ctx).toEqual({ isAttack: true, intensity: 9 })
  })

  it('falls back to the live form when trace is null', () => {
    const ctx = deriveTraceContext(null, form)
    expect(ctx).toEqual({ isAttack: false, intensity: 3 })
  })

  it('defaults intensity to 0 when an attack trace omits it', () => {
    const ctx = deriveTraceContext({ isAttack: true, intensity: undefined }, form)
    expect(ctx).toEqual({ isAttack: true, intensity: 0 })
  })
})
