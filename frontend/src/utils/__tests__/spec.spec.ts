import { describe, expect, it } from 'vitest'
import { buildSpecFormula, isSameSpecification } from '../spec'
import type { DeviceNode } from '@/types/node'
import type { DeviceTemplate } from '@/types/device'
import type { Specification } from '@/types/spec'

describe('spec formula preview', () => {
  const nodes: DeviceNode[] = [
    {
      id: 'ac-1',
      label: 'Living Room AC',
      templateName: 'Air Conditioner',
      position: { x: 0, y: 0 },
      state: 'on;cool',
      width: 160,
      height: 120
    },
    {
      id: 'sensor-1',
      label: 'Temperature Sensor',
      templateName: 'Temperature Sensor',
      position: { x: 0, y: 0 },
      state: 'working',
      width: 120,
      height: 100
    }
  ]

  const deviceTemplates: DeviceTemplate[] = [
    {
      name: 'Air Conditioner',
      manifest: {
        Name: 'Air Conditioner',
        Description: '',
        Modes: ['Power', 'Mode'],
        InitState: 'off;idle',
        ImpactedVariables: [],
        InternalVariables: [],
        WorkingStates: [
          { Name: 'off;idle', Dynamics: [], Description: '', Trust: 'trusted', Privacy: 'public' },
          { Name: 'on;cool', Dynamics: [], Description: '', Trust: 'trusted', Privacy: 'public' }
        ],
        APIs: []
      }
    },
    {
      name: 'Temperature Sensor',
      manifest: {
        Name: 'Temperature Sensor',
        Description: '',
        Modes: ['SensorState'],
        InitState: 'working',
        ImpactedVariables: ['temperature'],
        InternalVariables: [
          { Name: 'temperature', IsInside: false, FalsifiableWhenCompromised: true, LowerBound: 0, UpperBound: 50, Trust: 'trusted', Privacy: 'public' },
          { Name: 'humidity', IsInside: false, FalsifiableWhenCompromised: true, LowerBound: 0, UpperBound: 100, Trust: 'trusted', Privacy: 'public' }
        ],
        WorkingStates: [
          { Name: 'working', Dynamics: [], Description: '', Trust: 'trusted', Privacy: 'public' }
        ],
        APIs: []
      }
    }
  ]

  const context = { nodes, deviceTemplates }

  it('expands full-state conditions using the selected device template modes', () => {
    const formula = buildSpecFormula({
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [{
        id: 'c1',
        side: 'a',
        deviceId: 'ac-1',
        deviceLabel: 'Living Room AC',
        targetType: 'state',
        key: 'state',
        relation: '=',
        value: 'on;cool'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG("Living Room AC".state = "on;cool")')
  })

  it('previews external variables at the model boundary as environment variables', () => {
    const formula = buildSpecFormula({
      templateId: '5',
      templateLabel: 'Response',
      aConditions: [],
      ifConditions: [{
        id: 'if1',
        side: 'if',
        deviceId: 'sensor-1',
        deviceLabel: 'Temperature Sensor',
        targetType: 'variable',
        key: 'temperature',
        relation: '>',
        value: '28'
      }],
      thenConditions: [{
        id: 'then1',
        side: 'then',
        deviceId: 'ac-1',
        deviceLabel: 'Living Room AC',
        targetType: 'mode',
        key: 'Mode',
        relation: '=',
        value: 'cool'
      }]
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG((Environment."temperature" > 28) -> AF("Living Room AC"."Mode" = "cool"))')
  })

  it('uses explicitly shared variables as environment values in formula previews', () => {
    const explicitSharedTemplates: DeviceTemplate[] = deviceTemplates.map(template =>
      template.name === 'Temperature Sensor'
        ? {
            ...template,
            manifest: {
              ...template.manifest,
              InternalVariables: [
                { Name: 'temperature', IsInside: false, FalsifiableWhenCompromised: true, LowerBound: 0, UpperBound: 50, Trust: 'trusted', Privacy: 'public' }
              ]
            }
          }
        : template
    )

    const formula = buildSpecFormula({
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [{
        id: 'a1',
        side: 'a',
        deviceId: 'sensor-1',
        deviceLabel: 'Temperature Sensor',
        targetType: 'variable',
        key: 'temperature',
        relation: '>',
        value: '28'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, {
      nodes,
      deviceTemplates: explicitSharedTemplates
    })

    expect(formula).toBe('CTL AG(Environment."temperature" > 28)')
  })

  it('previews relation aliases with the canonical NuSMV operators', () => {
    const formula = buildSpecFormula({
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [{
        id: 'a1',
        side: 'a',
        deviceId: 'sensor-1',
        deviceLabel: 'Temperature Sensor',
        targetType: 'variable',
        key: 'temperature',
        relation: 'GTE',
        value: '28'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG(Environment."temperature" >= 28)')
  })

  it('previews template 7 safety specs with a concrete trust predicate', () => {
    const formula = buildSpecFormula({
      templateId: '7',
      templateLabel: 'Safety',
      aConditions: [{
        id: 'a1',
        side: 'a',
          deviceId: 'sensor-1',
          deviceLabel: 'Temperature Sensor',
          targetType: 'variable',
          key: 'temperature',
          relation: '>',
          value: '28'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG NOT (Environment."temperature" > 28 AND controlSource(Environment."temperature") = untrusted)')
  })

  it('previews every reliability label that contributes to a multi-mode safety state', () => {
    const formula = buildSpecFormula({
      templateId: '7',
      templateLabel: 'Untrusted-source safety',
      aConditions: [{
        id: 'a-multi-mode',
        side: 'a',
        deviceId: 'ac-1',
        deviceLabel: 'Living Room AC',
        targetType: 'state',
        key: 'state',
        relation: '=',
        value: 'on;cool'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG NOT ("Living Room AC".state = "on;cool" AND controlSource("Living Room AC".state) = untrusted)')
    expect(formula).not.toContain('ac_1')
  })

  it('taints a multi-condition safety event when any source is untrusted', () => {
    const formula = buildSpecFormula({
      templateId: '7',
      templateLabel: 'Untrusted-source safety',
      aConditions: [
        {
          id: 'hot',
          side: 'a',
          deviceId: 'sensor-1',
          deviceLabel: 'Temperature Sensor',
          targetType: 'variable',
          key: 'temperature',
          relation: '>',
          value: '28'
        },
        {
          id: 'humid',
          side: 'a',
          deviceId: 'sensor-1',
          deviceLabel: 'Temperature Sensor',
          targetType: 'variable',
          key: 'humidity',
          relation: '>',
          value: '70'
        }
      ],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG NOT (Environment."temperature" > 28 AND Environment."humidity" > 70 AND (controlSource(Environment."temperature") = untrusted OR controlSource(Environment."humidity") = untrusted))')
  })

  it('treats a_ as part of a real environment variable name in formula previews', () => {
    const prefixedTemplates: DeviceTemplate[] = deviceTemplates.map(template =>
      template.name === 'Temperature Sensor'
        ? {
            ...template,
            manifest: {
              ...template.manifest,
              InternalVariables: [
                { Name: 'a_temperature', IsInside: false, FalsifiableWhenCompromised: true, LowerBound: 0, UpperBound: 50, Trust: 'trusted', Privacy: 'public' }
              ]
            }
          }
        : template
    )

    const formula = buildSpecFormula({
      templateId: '7',
      templateLabel: 'Safety',
      aConditions: [{
        id: 'a1',
        side: 'a',
        deviceId: 'sensor-1',
        deviceLabel: 'Temperature Sensor',
        targetType: 'variable',
        key: 'a_temperature',
        relation: '>',
        value: '28'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, {
      nodes,
      deviceTemplates: prefixedTemplates
    })

    expect(formula).toBe('CTL AG NOT (Environment."a_temperature" > 28 AND controlSource(Environment."a_temperature") = untrusted)')
    expect(formula).not.toContain('a_a_temperature')
  })

  it('treats targetType as part of specification condition identity', () => {
    const base = {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Always',
      devices: [],
      formula: '',
      ifConditions: [],
      thenConditions: []
    } satisfies Omit<Specification, 'aConditions'>

    const trustSpec: Specification = {
      ...base,
      aConditions: [{
        id: 'a1',
        side: 'a',
        deviceId: 'sensor-1',
        deviceLabel: 'Temperature Sensor',
        targetType: 'trust',
        propertyScope: 'variable',
        key: 'temperature',
        relation: '=',
        value: 'trusted'
      }]
    }
    const privacySpec: Specification = {
      ...base,
      aConditions: [{
        ...trustSpec.aConditions[0],
        targetType: 'privacy',
        value: 'public'
      }]
    }

    expect(isSameSpecification(trustSpec, privacySpec)).toBe(false)
  })

  it('checks the label of the currently active mode state without exposing a generated state key', () => {
    const formula = buildSpecFormula({
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [{
        id: 'a-state-trust',
        side: 'a',
        deviceId: 'ac-1',
        deviceLabel: 'Living Room AC',
        targetType: 'trust',
        propertyScope: 'state',
        key: 'Power',
        relation: '=',
        value: 'trusted'
      }],
      ifConditions: [],
      thenConditions: []
    } satisfies Pick<Specification, 'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>, context)

    expect(formula).toBe('CTL AG(controlSource("Living Room AC".current "Power" state) = trusted)')
    expect(formula).not.toContain('trust_Power_')
  })

  it('treats condition order, display caches, and relation aliases as the same specification', () => {
    const first: Specification = {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Always',
      formula: 'display cache one',
      devices: [],
      aConditions: [
        {
          id: 'a1', side: 'a', deviceId: 'sensor-1', deviceLabel: 'Old label',
          targetType: 'variable', key: 'temperature', relation: 'GTE', value: '30'
        },
        {
          id: 'a2', side: 'a', deviceId: 'sensor-1', deviceLabel: 'Old label',
          targetType: 'mode', key: 'Mode', relation: 'in', value: 'away, home'
        }
      ],
      ifConditions: [],
      thenConditions: []
    }
    const second: Specification = {
      ...first,
      id: 'spec-2',
      formula: 'different preview cache',
      aConditions: [
        { ...first.aConditions[1], id: 'other-2', deviceLabel: 'New label', value: 'home|away' },
        { ...first.aConditions[0], id: 'other-1', deviceLabel: 'New label', relation: '>=' }
      ]
    }

    expect(isSameSpecification(first, second)).toBe(true)
  })
})
