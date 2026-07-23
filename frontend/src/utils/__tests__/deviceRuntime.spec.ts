import { describe, expect, it } from 'vitest'
import type { DeviceTemplate } from '@/types/device'
import {
  buildDeviceRuntimeConfig,
  createDeviceRuntimeDraft,
  deviceRuntimeConfigsEqual,
  findTemplateStatePrivacy,
  findTemplateStateTrust,
  getTemplateVariableDefaultValue,
  materializeDeviceRuntimeConfig,
  resetDeviceRuntimeDraft,
  templateVariableUsesNumericBounds,
  validateDeviceRuntimeConfig
} from '../deviceRuntime'

const t = (key: string, params?: Record<string, unknown>) =>
  params ? `${key}:${JSON.stringify(params)}` : key

const thermostatTemplate: DeviceTemplate = {
  id: 1,
  name: 'Thermostat',
  manifest: {
    Name: 'Thermostat',
    Description: 'HVAC controller',
    Modes: ['ThermostatMode'],
    InitState: 'auto',
    InternalVariables: [
      {
        Name: 'temperature',
        IsInside: false,
        FalsifiableWhenCompromised: true,
        LowerBound: 0,
        UpperBound: 50,
        Trust: 'trusted',
        Privacy: 'private'
      },
      {
        Name: 'presence',
        IsInside: true,
        FalsifiableWhenCompromised: true,
        Values: ['home', 'away'],
        Trust: 'trusted',
        Privacy: 'public'
      }
    ],
    ImpactedVariables: [],
    WorkingStates: [
      { Name: 'auto', Description: '', Trust: 'trusted', Privacy: 'public', Dynamics: [] },
      { Name: 'cool', Description: '', Trust: 'untrusted', Privacy: 'private', Dynamics: [] }
    ],
    APIs: [],
    Contents: []
  }
}

const statelessSensorTemplate: DeviceTemplate = {
  id: 2,
  name: 'Smoke Sensor',
  manifest: {
    Name: 'Smoke Sensor',
    Description: 'Stateless smoke sensor',
    Modes: [],
    InitState: '',
    InternalVariables: [
      {
        Name: 'smoke',
        IsInside: false,
        FalsifiableWhenCompromised: true,
        Values: ['clear', 'detected'],
        Trust: 'trusted',
        Privacy: 'public'
      }
    ],
    ImpactedVariables: [],
    WorkingStates: [],
    APIs: [],
    Contents: []
  }
}

describe('device runtime authority helpers', () => {
  it('keeps template labels as fallback instead of instance overrides', () => {
    const draft = createDeviceRuntimeDraft()

    resetDeviceRuntimeDraft(draft, thermostatTemplate)

    expect(draft.state).toBe('auto')
    expect(draft.currentStateTrust).toBe('')
    expect(draft.currentStatePrivacy).toBe('')
    expect(draft.variableTrusts.temperature).toBe('')
    expect(draft.privacies.temperature).toBe('')
    expect(findTemplateStateTrust(thermostatTemplate, 'auto')).toBe('trusted')
    expect(findTemplateStatePrivacy(thermostatTemplate, 'auto')).toBe('public')
    expect(draft.variables.temperature).toBe('0')
    expect(draft.variables.presence).toBe('home')
    expect(getTemplateVariableDefaultValue(thermostatTemplate.manifest.InternalVariables![1])).toBe('home')
  })

  it('builds one canonical runtime config for manual and drag-created devices', () => {
    const draft = createDeviceRuntimeDraft()
    resetDeviceRuntimeDraft(draft, thermostatTemplate)
    draft.state = 'cool'
    draft.currentStateTrust = 'untrusted'
    draft.currentStatePrivacy = 'private'
    draft.variables.temperature = '27'
    draft.variableTrusts.temperature = 'untrusted'
    draft.privacies.temperature = 'private'
    draft.variables.presence = 'home'

    expect(buildDeviceRuntimeConfig(thermostatTemplate, draft)).toEqual({
      state: 'cool',
      currentStateTrust: 'untrusted',
      currentStatePrivacy: 'private',
      variables: [
        { name: 'temperature', value: '27', trust: 'untrusted' },
        { name: 'presence', value: 'home' }
      ],
      privacies: [
        { name: 'temperature', privacy: 'private' }
      ]
    })
  })

  it('materializes omitted local runtime while preserving supplied overrides', () => {
    expect(materializeDeviceRuntimeConfig(thermostatTemplate, {
      state: 'cool',
      variables: [{ name: 'presence', value: 'away', trust: 'untrusted' }]
    }, { variableScope: 'local' })).toEqual({
      state: 'cool',
      variables: [{ name: 'presence', value: 'away', trust: 'untrusted' }]
    })
  })

  it('uses the same effective local defaults when runtime is omitted or explicitly empty', () => {
    const expected = {
      state: 'auto',
      variables: [{ name: 'presence', value: 'home' }]
    }

    expect(materializeDeviceRuntimeConfig(thermostatTemplate, undefined, { variableScope: 'local' })).toEqual(expected)
    expect(materializeDeviceRuntimeConfig(thermostatTemplate, {
      variables: [],
      privacies: []
    }, { variableScope: 'local' })).toEqual(expected)
  })

  it('compares runtime snapshots by effective values rather than nullable transport fields', () => {
    expect(deviceRuntimeConfigsEqual(thermostatTemplate, {
      state: 'auto',
      currentStateTrust: null,
      variables: [{ name: 'presence', value: 'home', trust: null }],
      privacies: []
    }, {
      state: 'auto',
      variables: [{ name: 'presence', value: 'home' }]
    }, { variableScope: 'local', includeEmptyCollections: true })).toBe(true)

    expect(deviceRuntimeConfigsEqual(thermostatTemplate, {
      state: 'auto',
      variables: [{ name: 'presence', value: 'home' }]
    }, {
      state: 'auto',
      variables: [{ name: 'presence', value: 'away' }]
    }, { variableScope: 'local', includeEmptyCollections: true })).toBe(false)
  })

  it('can preserve empty runtime collections when editing an existing device', () => {
    const draft = createDeviceRuntimeDraft()
    resetDeviceRuntimeDraft(draft, thermostatTemplate)
    draft.variables.temperature = ''
    draft.variables.presence = ''

    expect(buildDeviceRuntimeConfig(thermostatTemplate, draft, { includeEmptyCollections: true })).toEqual({
      state: 'auto',
      variables: [],
      privacies: []
    })
  })

  it('keeps scenario-level environment variables out of device instance runtime forms', () => {
    const draft = createDeviceRuntimeDraft()
    resetDeviceRuntimeDraft(draft, thermostatTemplate)
    draft.variables.temperature = '27'
    draft.variableTrusts.temperature = 'untrusted'
    draft.privacies.temperature = 'public'
    draft.variables.presence = 'home'

    expect(buildDeviceRuntimeConfig(thermostatTemplate, draft, { variableScope: 'local' })).toEqual({
      state: 'auto',
      variables: [
        { name: 'presence', value: 'home' }
      ]
    })

    const validation = validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [{ name: 'temperature', value: '27', trust: 'trusted' }]
    }, t, { variableScope: 'local' })
    expect(validation).toContain('app.deviceImportEnvironmentVariableNotDeviceRuntime')
  })

  it('rejects runtime overrides that the backend model boundary would reject', () => {
    const invalidEnum = validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [{ name: 'presence', value: 'office', trust: 'trusted' }]
    }, t)
    const invalidRange = validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [{ name: 'temperature', value: '99', trust: 'trusted' }]
    }, t)
    const invalidTrust = validateDeviceRuntimeConfig(thermostatTemplate, {
      currentStateTrust: 'maybe'
    }, t)
    const invalidPrivacy = validateDeviceRuntimeConfig(thermostatTemplate, {
      currentStatePrivacy: 'secret'
    }, t)

    expect(invalidEnum).toContain('app.deviceImportInvalidVariableValue')
    expect(invalidRange).toContain('app.deviceImportInvalidVariableValue')
    expect(invalidTrust).toContain('app.deviceImportInvalidTrust')
    expect(invalidPrivacy).toContain('app.deviceImportInvalidPrivacy')
  })

  it('does not treat API null numeric bounds as a numeric range for enum variables', () => {
    expect(templateVariableUsesNumericBounds({
      Name: 'location',
      IsInside: true,
      FalsifiableWhenCompromised: true,
      Trust: 'trusted',
      Privacy: 'public',
      Values: ['home', 'away'],
      LowerBound: null as any,
      UpperBound: null as any
    })).toBe(false)

    expect(validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [{ name: 'presence', value: 'home', trust: 'trusted' }]
    }, t)).toBe('')
  })

  it('rejects state trust overrides for no-mode templates', () => {
    const result = validateDeviceRuntimeConfig(statelessSensorTemplate, {
      currentStateTrust: 'trusted'
    }, t)

    expect(result).toBe('app.deviceImportStateTrustWithoutModes')
  })

  it('rejects state privacy overrides for no-mode templates', () => {
    const result = validateDeviceRuntimeConfig(statelessSensorTemplate, {
      currentStatePrivacy: 'private'
    }, t)

    expect(result).toBe('app.deviceImportStatePrivacyWithoutModes')
  })

  it('rejects non-placeholder state overrides for no-mode templates', () => {
    const result = validateDeviceRuntimeConfig(statelessSensorTemplate, {
      state: 'clear'
    }, t)

    expect(result).toBe('app.deviceImportStateWithoutModes')
    expect(validateDeviceRuntimeConfig(statelessSensorTemplate, { state: 'Working' }, t)).toBe('')
  })

  it('rejects duplicate runtime overrides before save', () => {
    const duplicateVariable = validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [
        { name: 'presence', value: 'home', trust: 'trusted' },
        { name: 'presence', value: 'away', trust: 'trusted' }
      ]
    }, t)
    const duplicatePrivacy = validateDeviceRuntimeConfig(thermostatTemplate, {
      privacies: [
        { name: 'temperature', privacy: 'private' },
        { name: 'temperature', privacy: 'public' }
      ]
    }, t)

    expect(duplicateVariable).toContain('app.deviceImportDuplicateVariable')
    expect(duplicatePrivacy).toContain('app.deviceImportDuplicatePrivacy')
  })

  it('rejects mode names in variable runtime overrides', () => {
    const result = validateDeviceRuntimeConfig(thermostatTemplate, {
      variables: [{ name: 'ThermostatMode', value: 'cool', trust: 'trusted' }]
    }, t)

    expect(result).toContain('app.deviceImportInvalidVariable')
  })

  it('uses working-state trust when a state changes', () => {
    expect(findTemplateStateTrust(thermostatTemplate, 'cool')).toBe('untrusted')
    expect(findTemplateStateTrust(thermostatTemplate, 'missing')).toBe('')
    expect(findTemplateStatePrivacy(thermostatTemplate, 'cool')).toBe('private')
    expect(findTemplateStatePrivacy(thermostatTemplate, 'missing')).toBe('')
  })

  it('preserves explicit invalid labels so validation rejects them', () => {
    const draft = createDeviceRuntimeDraft()
    resetDeviceRuntimeDraft(draft, thermostatTemplate)
    draft.currentStateTrust = 'maybe'
    draft.variableTrusts.presence = 'unknown'

    const config = buildDeviceRuntimeConfig(thermostatTemplate, draft)

    expect(config?.currentStateTrust).toBe('maybe')
    expect(config?.variables?.find(variable => variable.name === 'presence')?.trust).toBe('unknown')
    expect(validateDeviceRuntimeConfig(thermostatTemplate, config, t)).toContain('app.deviceImportInvalidTrust')
  })
})
