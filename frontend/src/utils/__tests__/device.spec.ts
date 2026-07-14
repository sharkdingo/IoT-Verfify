import { describe, expect, it } from 'vitest'
import { getDeviceIconUrl, resolveImpactEnvironmentDefinition, validateManifest } from '../device'
import type { DeviceManifest } from '@/types/device'

describe('device icon resolution', () => {
  const decodeDataSvg = (uri: string) =>
    decodeURIComponent(uri.slice(uri.indexOf(',') + 1))

  it('uses bundled assets for default templates without manifest icons', () => {
    const icon = getDeviceIconUrl('Window Shade', 'closed')
    const svg = decodeDataSvg(icon)

    expect(icon).toMatch(/^data:image\/svg\+xml/)
    expect(svg).toContain("viewBox='0 0 40 40'")
    expect(svg).toContain("M10 16H30")
  })

  it('generates a stable fallback icon for custom templates without assets', () => {
    const icon = getDeviceIconUrl('Custom Privacy Beacon', 'Working')
    const svg = decodeDataSvg(icon)

    expect(icon).toMatch(/^data:image\/svg\+xml/)
    expect(svg).toContain('viewBox="0 0 72 72"')
    expect(svg).toContain('>CP<')
  })

  it('prefers safe manifest icons and ignores unsafe URLs', () => {
    const safeManifest = {
      Icon: 'data:image/svg+xml,%3Csvg%20xmlns=%22http://www.w3.org/2000/svg%22/%3E'
    } as DeviceManifest
    const unsafeManifest = {
      Icon: 'javascript:alert(1)'
    } as DeviceManifest

    expect(getDeviceIconUrl('Any Device', 'Working', safeManifest)).toBe(safeManifest.Icon)
    expect(getDeviceIconUrl('Any Device', 'Working', unsafeManifest)).toMatch(/^data:image\/svg\+xml/)
  })
})

describe('device environment-domain semantics', () => {
  it('resolves an impact-only domain without adding a readable InternalVariable', () => {
    const manifest: DeviceManifest = {
      Name: 'Light',
      InternalVariables: [],
      EnvironmentDomains: [{
        Name: 'illuminance',
        LowerBound: 0,
        UpperBound: 100,
        Trust: 'untrusted',
        Privacy: 'public'
      }],
      ImpactedVariables: ['illuminance']
    }

    expect(manifest.InternalVariables).toEqual([])
    expect(resolveImpactEnvironmentDefinition(manifest, 'illuminance')).toMatchObject({
      Name: 'illuminance',
      LowerBound: 0,
      UpperBound: 100,
      IsInside: false,
      FalsifiableWhenCompromised: false
    })
    expect(validateManifest(manifest)).toEqual({ valid: true })
  })

  it('rejects an impacted value whose domain exists only outside its own manifest', () => {
    expect(validateManifest({
      Name: 'Incomplete Light',
      InternalVariables: [],
      ImpactedVariables: ['illuminance']
    })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('needs a domain in this manifest')
    })
  })

  it('rejects unused impact-domain metadata', () => {
    expect(validateManifest({
      Name: 'Incomplete Light',
      EnvironmentDomains: [{
        Name: 'illuminance',
        LowerBound: 0,
        UpperBound: 100,
        Trust: 'untrusted',
        Privacy: 'public'
      }],
      ImpactedVariables: []
    })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('is not listed in ImpactedVariables')
    })
  })

  it('rejects incomplete multi-mode working-state tuples', () => {
    expect(validateManifest({
      Name: 'Washer',
      Modes: ['Program', 'MachineState'],
      InitState: 'regular;idle',
      WorkingStates: [
        { Name: 'regular;idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'running', Trust: 'trusted', Privacy: 'public' }
      ]
    })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('one semicolon-separated value for each mode')
    })
  })

  it('rejects a wildcard or undefined initial state', () => {
    const base = {
      Name: 'Dual Mode Device',
      Modes: ['Power', 'Profile'],
      WorkingStates: [
        { Name: 'on;normal', Trust: 'trusted', Privacy: 'public' },
        { Name: 'off;normal', Trust: 'trusted', Privacy: 'public' }
      ]
    }
    expect(validateManifest({ ...base, InitState: 'on;_' })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('is not defined in WorkingStates')
    })
    expect(validateManifest({ ...base, InitState: 'on;eco' })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('is not defined in WorkingStates')
    })
    expect(validateManifest({ ...base, InitState: 'On;normal' })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('is not defined in WorkingStates')
    })
  })

  it('rejects conflicting labels for a reused mode-state component', () => {
    expect(validateManifest({
      Name: 'Home Profile',
      Modes: ['Occupancy', 'MachineState'],
      InitState: 'home;idle',
      WorkingStates: [
        { Name: 'home;idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'away;idle', Trust: 'untrusted', Privacy: 'public' }
      ]
    })).toMatchObject({
      valid: false,
      msg: expect.stringContaining('conflicting Trust/Privacy labels')
    })
  })

  it('rejects missing security labels instead of defaulting to trusted or public', () => {
    expect(validateManifest({
      Name: 'State Sensor',
      Modes: ['Detection'],
      InitState: 'clear',
      WorkingStates: [{ Name: 'clear' }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must define Trust') })

    expect(validateManifest({
      Name: 'Local Sensor',
      InternalVariables: [{
        Name: 'reading',
        IsInside: true,
        FalsifiableWhenCompromised: true,
        LowerBound: 0,
        UpperBound: 100
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must define Trust') })

    expect(validateManifest({
      Name: 'Ambiguous Sensor',
      InternalVariables: [{
        Name: 'reading',
        FalsifiableWhenCompromised: true,
        Trust: 'trusted',
        Privacy: 'public',
        LowerBound: 0,
        UpperBound: 100
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must explicitly define IsInside') })

    expect(validateManifest({
      Name: 'Implicit Boolean Sensor',
      InternalVariables: [{
        Name: 'detected',
        IsInside: true,
        FalsifiableWhenCompromised: true,
        Trust: 'trusted',
        Privacy: 'public'
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must explicitly define Values') })

    expect(validateManifest({
      Name: 'Camera',
      Contents: [{ Name: 'photo' }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must define Privacy') })
  })

  it('rejects a raw WorkingState invariant that the model cannot preserve', () => {
    expect(validateManifest({
      Name: 'Lamp',
      Modes: ['Power'],
      InitState: 'off',
      WorkingStates: [{
        Name: 'off',
        Trust: 'trusted',
        Privacy: 'public',
        Invariant: 'level < 50'
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('unsupported Invariant') })
  })

  it('rejects transition signals that cannot be referenced by rules or specifications', () => {
    expect(validateManifest({
      Name: 'Motion Sensor',
      InternalVariables: [{
        Name: 'motion',
        IsInside: true,
        FalsifiableWhenCompromised: true,
        Trust: 'untrusted',
        Privacy: 'public',
        Values: ['clear', 'detected']
      }],
      Transitions: [{
        Name: 'motion detected',
        Signal: true,
        Trigger: { Attribute: 'motion', Relation: '=', Value: 'detected' },
        Assignments: [{ Attribute: 'motion', Value: 'clear' }]
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('unsupported Signal') })
  })

  it('requires API trigger observability to be an explicit template choice', () => {
    expect(validateManifest({
      Name: 'Lamp',
      Modes: ['Power'],
      InitState: 'off',
      WorkingStates: [
        { Name: 'off', Trust: 'trusted', Privacy: 'public' },
        { Name: 'on', Trust: 'trusted', Privacy: 'public' }
      ],
      APIs: [{ Name: 'turn_on', StartState: 'off', EndState: 'on' }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must explicitly define boolean Signal') })
  })

  it('requires an explicit API state precondition instead of assuming any state', () => {
    expect(validateManifest({
      Name: 'Lamp',
      Modes: ['Power'],
      InitState: 'off',
      WorkingStates: [
        { Name: 'off', Trust: 'trusted', Privacy: 'public' },
        { Name: 'on', Trust: 'trusted', Privacy: 'public' }
      ],
      APIs: [{ Name: 'turn_on', EndState: 'on', Signal: true }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('must explicitly define StartState') })
  })

  it('rejects an ambiguous content-input capability instead of treating it as enabled', () => {
    expect(validateManifest({
      Name: 'Messenger',
      Modes: ['Status'],
      InitState: 'idle',
      WorkingStates: [
        { Name: 'idle', Trust: 'trusted', Privacy: 'private' },
        { Name: 'sending', Trust: 'trusted', Privacy: 'private' }
      ],
      APIs: [{
        Name: 'send',
        StartState: 'idle',
        EndState: 'sending',
        Signal: true,
        AcceptsContent: 'yes'
      }]
    })).toMatchObject({ valid: false, msg: expect.stringContaining('AcceptsContent must be boolean') })
  })
})
