import { describe, expect, it } from 'vitest'
import { hasModeledStateMachine, resolveEffectiveNodeState } from '@/utils/canvas/nodeState'

const manifest = {
  Name: 'Light',
  Modes: ['SwitchState'],
  InitState: 'off',
  WorkingStates: [
    { Name: 'off', Trust: 'trusted', Privacy: 'public' },
    { Name: 'on', Trust: 'trusted', Privacy: 'public' }
  ]
}

describe('nodeState', () => {
  it('requires both modes and legal working states', () => {
    expect(hasModeledStateMachine(manifest)).toBe(true)
    expect(hasModeledStateMachine({ ...manifest, WorkingStates: [] })).toBe(false)
    expect(hasModeledStateMachine({ ...manifest, Modes: [] })).toBe(false)
  })

  it('keeps legal states and replaces stale persisted states with the legal initial state', () => {
    expect(resolveEffectiveNodeState('on', manifest, 'Unknown')).toBe('on')
    expect(resolveEffectiveNodeState('removed-by-template-upgrade', manifest, 'Unknown')).toBe('off')
  })

  it('falls back to the first legal state when a malformed initial state is no longer legal', () => {
    expect(resolveEffectiveNodeState('', { ...manifest, InitState: 'retired' }, 'Unknown')).toBe('off')
  })

  it('preserves the persistence fallback for stateless templates', () => {
    expect(resolveEffectiveNodeState('Working', { ...manifest, Modes: [], WorkingStates: [] }, 'Unknown'))
      .toBe('Working')
  })
})
