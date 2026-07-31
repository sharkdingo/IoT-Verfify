import { describe, expect, it } from 'vitest'
import { i18n } from '@/assets/i18n'
import {
  canonicalNaturalChangeRate,
  getDeviceIconUrl,
  MANIFEST_VALIDATION_MESSAGE_KEYS,
  naturalChangeCandidateValues,
  naturalChangeDeltas,
  parseNaturalChangeRate,
  resolveImpactEnvironmentDefinition,
  validateManifest
} from '../device'
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
    const remoteManifest = {
      Icon: 'https://tracker.example/device.png'
    } as DeviceManifest

    expect(getDeviceIconUrl('Any Device', 'Working', safeManifest)).toBe(safeManifest.Icon)
    expect(getDeviceIconUrl('Any Device', 'Working', unsafeManifest)).toMatch(/^data:image\/svg\+xml/)
    expect(getDeviceIconUrl('Any Device', 'Working', remoteManifest)).toMatch(/^data:image\/svg\+xml/)
  })
})

describe('device environment-domain semantics', () => {
  it('exposes structured validation reasons that resolve in every supported locale', () => {
    for (const key of Object.values(MANIFEST_VALIDATION_MESSAGE_KEYS)) {
      expect(i18n.global.te(key, 'zh-CN'), `missing zh-CN translation for ${key}`).toBe(true)
      expect(i18n.global.te(key, 'en'), `missing en translation for ${key}`).toBe(true)
    }

    expect(validateManifest({ Name: 'Lamp', Modes: 'Power' })).toMatchObject({
      valid: false,
      code: 'fieldMustBeArray',
      params: { field: 'Modes' },
      msg: expect.stringContaining('must be an array')
    })
  })

  it('resolves an impact-only domain without adding a readable InternalVariable', () => {
    const manifest: DeviceManifest = {
      Name: 'Light',
      InternalVariables: [],
      EnvironmentDomains: [{
        Name: 'illuminance',
        LowerBound: 0,
        UpperBound: 100,
        NaturalChangeRate: '[-1, 1]',
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

  it('requires an explicit natural rate only for shared numeric variables', () => {
    const shared = {
      Name: 'Temperature Sensor',
      InternalVariables: [{
        Name: 'temperature',
        IsInside: false,
        FalsifiableWhenCompromised: true,
        Trust: 'untrusted',
        Privacy: 'public',
        LowerBound: 0,
        UpperBound: 100
      }]
    }
    expect(validateManifest(shared)).toMatchObject({
      valid: false,
      code: 'sharedNumericNaturalChangeRateRequired'
    })

    expect(validateManifest({
      ...shared,
      InternalVariables: [{ ...shared.InternalVariables[0], IsInside: true }]
    })).toEqual({ valid: true })
  })

  it('matches backend numeric-domain and natural-rate admission before upload', () => {
    const numericVariable = {
      Name: 'temperature',
      IsInside: false,
      FalsifiableWhenCompromised: true,
      Trust: 'untrusted',
      Privacy: 'public',
      LowerBound: 0,
      UpperBound: 100,
      NaturalChangeRate: '[-1, 1]'
    }

    expect(validateManifest({
      Name: 'Descending domain',
      InternalVariables: [{ ...numericVariable, LowerBound: 101 }]
    })).toMatchObject({ valid: false, code: 'numericBoundsOrderInvalid' })

    expect(validateManifest({
      Name: 'Out-of-range integer domain',
      InternalVariables: [{ ...numericVariable, UpperBound: 2147483648 }]
    })).toMatchObject({ valid: false, code: 'numericBoundsInvalid' })

    expect(validateManifest({
      Name: 'Descending rate',
      InternalVariables: [{ ...numericVariable, NaturalChangeRate: '[2, 1]' }]
    })).toMatchObject({ valid: false, code: 'naturalChangeRateInvalid' })

    expect(validateManifest({
      Name: 'Whitespace outside rate',
      InternalVariables: [{ ...numericVariable, NaturalChangeRate: ' [-1, 1]' }]
    })).toMatchObject({ valid: false, code: 'naturalChangeRateInvalid' })

    expect(validateManifest({
      Name: 'Descending impact domain',
      EnvironmentDomains: [{
        Name: 'temperature',
        Trust: 'untrusted',
        Privacy: 'public',
        LowerBound: 100,
        UpperBound: 0,
        NaturalChangeRate: '[-1, 1]'
      }],
      ImpactedVariables: ['temperature']
    })).toMatchObject({ valid: false, code: 'numericBoundsOrderInvalid' })

    expect(validateManifest({
      Name: 'Discrete weather',
      InternalVariables: [{
        Name: 'weather',
        IsInside: false,
        FalsifiableWhenCompromised: true,
        Trust: 'untrusted',
        Privacy: 'public',
        Values: ['dry', 'wet'],
        NaturalChangeRate: '1'
      }]
    })).toMatchObject({ valid: false, code: 'naturalChangeRateNumericOnly' })
  })

  it('parses a rate declaration and shows the whole interval it admits', () => {
    expect(parseNaturalChangeRate('1')).toEqual({ lower: 0, upper: 1 })
    expect(parseNaturalChangeRate('[2, 3]')).toEqual({ lower: 2, upper: 3 })
    expect(parseNaturalChangeRate('[3, 2]')).toBeNull()
    expect(parseNaturalChangeRate('2147483648')).toBeNull()
    expect(canonicalNaturalChangeRate(null)).toBe('0..0')
    expect(canonicalNaturalChangeRate('')).toBe('')
  })

  // The declaration constrains the per-step change, so the UI must not describe an
  // under-approximation the generator no longer produces. A step with no drift is always allowed,
  // which is why 0 appears even for an interval that excludes it.
  it('lists every per-step change the declared interval admits, including a stutter', () => {
    expect(naturalChangeDeltas('[-1, 1]')).toEqual([-1, 0, 1])
    expect(naturalChangeDeltas('[-3, 3]')).toEqual([-3, -2, -1, 0, 1, 2, 3])
    expect(naturalChangeDeltas('[2, 4]')).toEqual([0, 2, 3, 4])
    expect(naturalChangeDeltas('0')).toEqual([0])
    expect(naturalChangeCandidateValues('[-1, 1]')).toBe('-1, 0, +1')
    expect(naturalChangeCandidateValues('[2, 4]')).toBe('0, +2, +3, +4')
  })

  it('rejects a rate interval too wide to model exhaustively', () => {
    const manifest = (rate: string) => ({
      Name: 'Wide Drift Sensor',
      InternalVariables: [{
        Name: 'temperature',
        IsInside: false,
        LowerBound: -1000,
        UpperBound: 1000,
        NaturalChangeRate: rate,
        Trust: 'trusted',
        Privacy: 'public',
        FalsifiableWhenCompromised: false
      }]
    })
    expect(validateManifest(manifest('[-500, 500]')).code).toBe('naturalChangeRateSpanTooWide')
    expect(validateManifest(manifest('[-1, 1]')).code).not.toBe('naturalChangeRateSpanTooWide')
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
        NaturalChangeRate: '[-1, 1]',
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
