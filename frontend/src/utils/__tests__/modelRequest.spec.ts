import { describe, expect, it } from 'vitest'
import {
  buildModelRunSignature,
  buildSimulationRequestPayload,
  buildVerificationRequestPayload,
  normalizeNuSmvDeviceName,
  normalizeNuSmvValue
} from '../modelRequest'

describe('modelRequest', () => {
  const nodes = [
    { id: 'node-1', label: '1Lamp', templateName: 'Switch', state: 'off' }
  ] as any[]

  const deviceTemplates = [
    {
      manifest: {
        Name: 'Switch',
        Modes: ['SwitchState'],
        WorkingStates: [
          { Name: 'off' },
          { Name: 'on' }
        ],
        InternalVariables: [
          { Name: 'power', LowerBound: 0, UpperBound: 100, Privacy: 'public' }
        ]
      }
    }
  ] as any[]

  const rules = [
    {
      id: '41',
      name: 'Turn on lamp',
      sources: [
        { fromId: 'node-1', fromApi: 'state', itemType: 'state', relation: '=', value: '"1"' }
      ],
      toId: 'node-1',
      toApi: 'turnOn'
    }
  ] as any[]

  const specifications = [
    {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Always',
      devices: [
        { deviceId: 'node-1', deviceLabel: 'node-1', selectedApis: ['turnOn'] }
      ],
      aConditions: [
        {
          id: 'cond-1',
          side: 'a',
          deviceId: 'node-1',
          deviceLabel: 'node-1',
          targetType: 'state',
          key: 'state',
          relation: '=',
          value: '"1"'
        }
      ],
      ifConditions: [],
      thenConditions: []
    }
  ] as any[]

  it('normalizes NuSMV identifiers and numeric values consistently', () => {
    expect(normalizeNuSmvDeviceName('1Lamp')).toBe('_1lamp')
    expect(normalizeNuSmvDeviceName('Lamp')).toBe('lamp')
    expect(normalizeNuSmvDeviceName('node-1')).toBe('node_1')
    expect(normalizeNuSmvDeviceName('FROZENVAR')).toBe('_frozenvar')
    expect(normalizeNuSmvDeviceName('CTLSPEC')).toBe('_ctlspec')
    expect(normalizeNuSmvValue('"42"')).toBe('42')
    expect(normalizeNuSmvValue("'42'")).toBe('42')
    expect(normalizeNuSmvValue('"on"')).toBe('"on"')
  })

  it('builds identical devices and rules for verification and simulation', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      specifications,
      isAttack: true,
      attackBudget: 2,
      enablePrivacy: true
    })

    const simulation = buildSimulationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      steps: 8,
      isAttack: true,
      attackBudget: 2,
      enablePrivacy: true
    })

    expect(simulation.devices).toEqual(verification.devices)
    expect(simulation.rules).toEqual(verification.rules)
    expect(verification.devices).toEqual([
      {
        varName: 'node_1',
        deviceLabel: '1Lamp',
        templateName: 'Switch',
        state: 'off'
      }
    ])
    expect(verification.rules[0].conditions[0]).toMatchObject({
      deviceName: 'node_1',
      targetType: 'state',
      value: '1'
    })
    expect(verification.rules[0].command.deviceName).toBe('node_1')
    expect(verification.rules[0].id).toBe(41)
    expect(simulation.rules[0].id).toBe(41)
  })

  it('keeps temporary UI rule ids out of the model boundary', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [{ ...rules[0], id: 'rule_1712345678' }] as any[],
      specifications,
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].id).toBeUndefined()
  })

  it('zeros attackBudget when attack mode is disabled', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      specifications,
      isAttack: false,
      attackBudget: 9,
      enablePrivacy: false
    })

    const simulation = buildSimulationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      steps: 8,
      isAttack: false,
      attackBudget: 9,
      enablePrivacy: false
    })

    expect(verification.attackBudget).toBe(0)
    expect(simulation.attackBudget).toBe(0)
  })

  it('preserves explicit state trust overrides for mode templates', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        {
          id: 'node-1',
          label: '1Lamp',
          templateName: 'Switch',
          state: 'off',
          currentStateTrust: 'untrusted',
          currentStatePrivacy: 'private'
        }
      ] as any[],
      deviceTemplates,
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'node_1',
      templateName: 'Switch',
      state: 'off',
      currentStateTrust: 'untrusted',
      currentStatePrivacy: 'private'
    })
  })

  it('does not reserve variable_ as a hidden template prefix', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        { id: 'variable-sensor-1', label: 'Variable Sensor', templateName: 'variable_sensor' }
      ] as any[],
      deviceTemplates: [
        {
          name: 'variable_sensor',
          manifest: {
            Name: 'variable_sensor',
            Modes: [],
            WorkingStates: [],
            InternalVariables: [
              { Name: 'reading', IsInside: true, LowerBound: 0, UpperBound: 100 }
            ]
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.devices).toEqual([
      {
        varName: 'variable_sensor_1',
        deviceLabel: 'Variable Sensor',
        templateName: 'variable_sensor'
      }
    ])
  })

  it('does not send state fields for templates without modes', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        { id: 'smoke-1', label: 'Smoke', templateName: 'Smoke Sensor', state: 'Working' }
      ] as any[],
      deviceTemplates: [
        {
          manifest: {
            Name: 'Smoke Sensor',
            Modes: [],
            InternalVariables: [
              { Name: 'smoke', IsInside: true, Values: ['clear', 'detected'], Privacy: 'public' }
            ]
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'smoke_1',
      templateName: 'Smoke Sensor'
    })
    expect(verification.devices[0].state).toBeUndefined()
    expect(verification.devices[0].currentStateTrust).toBeUndefined()
    expect(verification.devices[0].currentStatePrivacy).toBeUndefined()
    expect(verification.devices[0].variables).toBeUndefined()
    expect(verification.devices[0].privacies).toBeUndefined()
  })

  it('does not send state fields for templates with modes but no working states', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        { id: 'draft-1', label: 'Draft', templateName: 'Draft Template', state: 'on', currentStateTrust: 'trusted' }
      ] as any[],
      deviceTemplates: [
        {
          manifest: {
            Name: 'Draft Template',
            Modes: ['MachineState'],
            WorkingStates: []
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'draft_1',
      templateName: 'Draft Template'
    })
    expect(verification.devices[0].state).toBeUndefined()
    expect(verification.devices[0].currentStateTrust).toBeUndefined()
  })

  it('matches device templates by repository name or manifest name', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        {
          id: 'shade-1',
          label: 'Shade',
          templateName: 'Window Shade Display',
          state: 'closed',
          currentStateTrust: 'trusted'
        }
      ] as any[],
      deviceTemplates: [
        {
          name: 'Window Shade Display',
          manifest: {
            Name: 'Window Shade',
            Modes: ['OpenableState'],
            WorkingStates: [{ Name: 'closed' }, { Name: 'open' }]
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'shade_1',
      templateName: 'Window Shade Display',
      state: 'closed',
      currentStateTrust: 'trusted'
    })
  })

  it('sends only explicit device instance runtime overrides', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        {
          id: 'sensor-1',
          label: 'Sensor',
          templateName: 'Smoke Sensor',
          variables: [{ name: 'smoke', value: 'detected', trust: 'untrusted' }],
          privacies: [{ name: 'smoke', privacy: 'private' }]
        }
      ] as any[],
      deviceTemplates: [
        {
          manifest: {
            Name: 'Smoke Sensor',
            Modes: [],
            InternalVariables: [
              { Name: 'smoke', IsInside: true, Values: ['clear', 'detected'], Privacy: 'public' }
            ]
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'sensor_1',
      templateName: 'Smoke Sensor',
      variables: [{ name: 'smoke', value: 'detected', trust: 'untrusted' }],
      privacies: [{ name: 'smoke', privacy: 'private' }]
    })
  })

  it('keeps scenario environment variables out of device instance requests', () => {
    const verification = buildVerificationRequestPayload({
      nodes: [
        {
          id: 'temperature-sensor-1',
          label: 'Temperature Sensor',
          templateName: 'Temperature Sensor',
          variables: [{ name: 'temperature', value: '31', trust: 'trusted' }],
          privacies: [{ name: 'temperature', privacy: 'public' }]
        }
      ] as any[],
      deviceTemplates: [
        {
          manifest: {
            Name: 'Temperature Sensor',
            Modes: [],
            WorkingStates: [],
            InternalVariables: [
              { Name: 'temperature', IsInside: false, LowerBound: 0, UpperBound: 50, Privacy: 'public' }
            ]
          }
        }
      ] as any[],
      rules: [],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.devices[0]).toMatchObject({
      varName: 'temperature_sensor_1',
      templateName: 'Temperature Sensor'
    })
    expect(verification.devices[0].variables).toBeUndefined()
    expect(verification.devices[0].privacies).toBeUndefined()
  })

  it('sends the environment pool as a top-level model request field', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      specifications: [],
      environmentVariables: [
        { name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' },
        { name: 'presence', value: '"home"', trust: 'untrusted', privacy: 'private' }
      ],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    const simulation = buildSimulationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      environmentVariables: [
        { name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' }
      ],
      steps: 5,
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: true
    })

    expect(verification.environmentVariables).toEqual([
      { name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' },
      { name: 'presence', value: '"home"', trust: 'untrusted', privacy: 'private' }
    ])
    expect(simulation.environmentVariables).toEqual([
      { name: 'temperature', value: '28', trust: 'trusted', privacy: 'public' }
    ])
  })

  it('rejects a nameless environment entry instead of silently omitting model input', () => {
    expect(() => buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      specifications: [],
      environmentVariables: [
        { name: '   ', value: '28', trust: 'trusted', privacy: 'public' }
      ],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })).toThrow('Environment variable 1 requires a name')
  })

  it('preserves content-device rule commands in model requests', () => {
    const contentRule = {
      ...rules[0],
      contentDevice: 'node-1',
      content: 'photo'
    }

    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [contentRule],
      specifications,
      isAttack: true,
      attackBudget: 2,
      enablePrivacy: true
    })

    expect(verification.rules[0].command).toMatchObject({
      deviceName: 'node_1',
      action: 'turnOn',
      contentDevice: 'node_1',
      content: 'photo'
    })
  })

  it('normalizes specification condition and selected-device ids for model requests', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      specifications,
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.specs[0].aConditions[0]).toMatchObject({
      deviceId: 'node_1',
      deviceLabel: 'node-1',
      value: '1'
    })
    expect(verification.specs[0].devices?.[0]).toMatchObject({
      deviceId: 'node_1',
      deviceLabel: 'node-1',
      selectedApis: ['turnOn']
    })
  })

  it('normalizes rule and specification relation aliases at the model boundary', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: 'power', itemType: 'variable', relation: 'GTE', value: '10' }
          ]
        }
      ] as any[],
      specifications: [
        {
          ...specifications[0],
          aConditions: [
            {
              ...specifications[0].aConditions[0],
              key: 'power',
              targetType: 'variable',
              relation: 'NOT_IN',
              value: '1,2'
            }
          ]
        }
      ] as any[],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].conditions[0].relation).toBe('>=')
    expect(verification.specs[0].aConditions[0].relation).toBe('not in')
  })

  it('preserves falsy zero condition values in rules and specifications', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: 'brightness', itemType: 'variable', relation: '=', value: 0 }
          ]
        }
      ] as any[],
      specifications: [
        {
          ...specifications[0],
          aConditions: [
            {
              ...specifications[0].aConditions[0],
              key: 'brightness',
              value: 0
            }
          ]
        }
      ] as any[],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].conditions[0].value).toBe('0')
    expect(verification.specs[0].aConditions[0].value).toBe('0')
  })

  it('rejects incomplete value-based rule conditions at the model boundary', () => {
    expect(() => buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: 'state', itemType: 'state', relation: '=', value: '   ' }
          ]
        }
      ] as any[],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })).toThrow('Rule state condition requires relation and value')
  })

  it('omits relation and value for API signal rule triggers', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: 'turnOn', itemType: 'api' }
          ]
        }
      ] as any[],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].conditions[0]).toMatchObject({
      deviceName: 'node_1',
      attribute: 'turnOn',
      targetType: 'api'
    })
    expect(verification.rules[0].conditions[0].relation).toBeUndefined()
    expect(verification.rules[0].conditions[0].value).toBeUndefined()
  })

  it('keeps mode and full-state rule triggers as backend-recognized attributes', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: 'Mode', itemType: 'mode', relation: '=', value: 'sleep' },
            { fromId: 'node-1', fromApi: 'state', itemType: 'state', relation: '=', value: 'sleep;idle' }
          ]
        }
      ] as any[],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].conditions).toEqual([
      { deviceName: 'node_1', attribute: 'Mode', targetType: 'mode', relation: '=', value: 'sleep' },
      { deviceName: 'node_1', attribute: 'state', targetType: 'state', relation: '=', value: 'sleep;idle' }
    ])
  })

  it('normalizes full-state rule attributes even when imported data omits fromApi', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [
        {
          ...rules[0],
          sources: [
            { fromId: 'node-1', fromApi: '', itemType: 'state', relation: '=', value: 'sleep;idle' }
          ]
        }
      ] as any[],
      specifications: [],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.rules[0].conditions[0]).toMatchObject({
      deviceName: 'node_1',
      attribute: 'state',
      targetType: 'state',
      relation: '=',
      value: 'sleep;idle'
    })
  })

  it('defaults API specification conditions to an explicit true signal check', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      specifications: [{
        id: 'spec-api',
        templateId: '1',
        templateLabel: 'A holds forever',
        devices: [],
        aConditions: [{
          id: 'c-api',
          side: 'a',
          deviceId: 'node-1',
          deviceLabel: 'Node 1',
          targetType: 'api',
          key: 'turnOn',
          relation: '=',
          value: ''
        }],
        ifConditions: [],
        thenConditions: []
      }],
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })

    expect(verification.specs[0].aConditions[0]).toMatchObject({
      deviceId: 'node_1',
      targetType: 'api',
      key: 'turnOn',
      relation: '=',
      value: 'TRUE'
    })
  })

  it('changes the local run signature when model input or a referenced template changes', () => {
    const request = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      specifications,
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })
    const baseline = buildModelRunSignature(request, deviceTemplates)

    expect(buildModelRunSignature({ ...request, enablePrivacy: true }, deviceTemplates)).not.toBe(baseline)
    expect(buildModelRunSignature(request, [{
      ...deviceTemplates[0],
      manifest: {
        ...deviceTemplates[0].manifest,
        WorkingStates: [...deviceTemplates[0].manifest.WorkingStates, { Name: 'fault' }]
      }
    }] as any[])).not.toBe(baseline)
  })

  it('ignores unused templates and object key order in the local run signature', () => {
    const request = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      specifications,
      isAttack: false,
      attackBudget: 0,
      enablePrivacy: false
    })
    const reorderedRequest = {
      enablePrivacy: request.enablePrivacy,
      specs: request.specs,
      rules: request.rules,
      environmentVariables: request.environmentVariables,
      devices: request.devices,
      attackBudget: request.attackBudget,
      isAttack: request.isAttack
    }
    const withUnusedTemplate = [
      ...deviceTemplates,
      { manifest: { Name: 'Unused Sensor', Modes: [], InternalVariables: [] } }
    ] as any[]

    expect(buildModelRunSignature(reorderedRequest, withUnusedTemplate)).toBe(
      buildModelRunSignature(request, deviceTemplates)
    )
  })
})
