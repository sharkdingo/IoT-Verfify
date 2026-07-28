import { describe, expect, it, vi } from 'vitest'

import { createBoardSemanticCommit, type BoardSemanticCommitPorts } from './semanticCommit'

const ports = (): BoardSemanticCommitPorts & { calls: string[] } => {
  const calls: string[] = []
  return {
    calls,
    setRules: vi.fn(() => { calls.push('setRules') }),
    setSpecs: vi.fn(() => { calls.push('setSpecs') }),
    syncRuleDerivedEdges: vi.fn(() => { calls.push('syncRuleDerivedEdges') }),
    markVerificationResultStale: vi.fn(() => { calls.push('markVerificationResultStale') }),
    syncUndoAvailability: vi.fn(() => { calls.push('syncUndoAvailability') }),
    clearDanglingFocus: vi.fn(() => { calls.push('clearDanglingFocus') })
  }
}

describe('board semantic commit', () => {
  it('rebuilds rule-derived edges whenever rules change', () => {
    const p = ports()
    createBoardSemanticCommit(p)({ rules: [] })

    // The historical bug: a mutation replaced rules but left the canvas edges describing the
    // previous rule set until some unrelated refresh happened to run.
    expect(p.syncRuleDerivedEdges).toHaveBeenCalledOnce()
  })

  it('does not rebuild edges for a specification-only mutation', () => {
    const p = ports()
    createBoardSemanticCommit(p)({ specs: [] })

    expect(p.setSpecs).toHaveBeenCalledOnce()
    expect(p.syncRuleDerivedEdges).not.toHaveBeenCalled()
  })

  it('replaces collections before anything derived from them is computed', () => {
    const p = ports()
    createBoardSemanticCommit(p)({ rules: [], specs: [], availability: { canUndo: true } })

    // Any derived value computed before the collections land would be stale.
    expect(p.calls.indexOf('setRules')).toBeLessThan(p.calls.indexOf('syncRuleDerivedEdges'))
    expect(p.calls.indexOf('setSpecs')).toBeLessThan(p.calls.indexOf('clearDanglingFocus'))
  })

  it('always marks a displayed verdict stale, because the model changed', () => {
    const p = ports()
    createBoardSemanticCommit(p)({ specs: [] })

    expect(p.markVerificationResultStale).toHaveBeenCalledOnce()
  })

  it('mirrors reported undo availability but never invents it', () => {
    const reversible = ports()
    createBoardSemanticCommit(reversible)({ rules: [], availability: { canUndo: true } })
    expect(reversible.syncUndoAvailability).toHaveBeenCalledWith({ canUndo: true })

    // A mutation that is not reversible omits availability; calling through with nothing would
    // let a stale local guess overwrite real server history.
    const plain = ports()
    createBoardSemanticCommit(plain)({ rules: [] })
    expect(plain.syncUndoAvailability).not.toHaveBeenCalled()
  })

  it('hands the applied scene to the focus port, which owns the dangling check', () => {
    const p = ports()
    const scene = { rules: [{ id: '2' } as any] }
    createBoardSemanticCommit(p)(scene)

    // The commit does not decide what is dangling; it guarantees the port is called with the
    // authoritative post-mutation scene, so no caller has to remember this follow-up.
    expect(p.clearDanglingFocus).toHaveBeenCalledWith(scene)
  })
})
