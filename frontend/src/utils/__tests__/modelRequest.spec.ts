import { describe, expect, it } from 'vitest'
import {
  buildSimulationRequestPayload,
  buildVerificationRequestPayload,
  normalizeNuSmvDeviceName,
  normalizeNuSmvValue
} from '../modelRequest'

describe('modelRequest', () => {
  const nodes = [
    { id: 'node-1', label: '1Lamp', templateName: 'Switch', state: 'off' },
    { id: 'node-1_power', label: 'power', templateName: 'variable_power', state: '0' }
  ] as any[]

  const deviceTemplates = [
    {
      manifest: {
        Name: 'Switch',
        InternalVariables: [
          { Name: 'power', Default: '0', Privacy: 'public' }
        ]
      }
    }
  ] as any[]

  const rules = [
    {
      id: 'rule-1',
      name: 'Turn on lamp',
      sources: [
        { fromId: 'node-1', fromApi: 'state', relation: '=', value: '"1"' }
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

  const resolveNodeLabel = (ref?: string | null) =>
    nodes.find(node => node.id === ref || node.label === ref)?.label || ref || ''

  it('normalizes NuSMV identifiers and numeric values consistently', () => {
    expect(normalizeNuSmvDeviceName('1Lamp')).toBe('d_1Lamp')
    expect(normalizeNuSmvDeviceName('Lamp')).toBe('Lamp')
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
      resolveNodeLabel,
      isAttack: true,
      intensity: 2,
      enablePrivacy: true
    })

    const simulation = buildSimulationRequestPayload({
      nodes,
      deviceTemplates,
      rules,
      resolveNodeLabel,
      steps: 8,
      isAttack: true,
      intensity: 2,
      enablePrivacy: true
    })

    expect(simulation.devices).toEqual(verification.devices)
    expect(simulation.rules).toEqual(verification.rules)
    expect(verification.devices).toEqual([
      {
        varName: 'd_1Lamp',
        templateName: 'Switch',
        state: 'off',
        currentStateTrust: 'trusted',
        variables: [{ name: 'power', value: '0', trust: 'trusted' }],
        privacies: [{ name: 'power', privacy: 'public' }]
      }
    ])
    expect(verification.rules[0].conditions[0]).toMatchObject({
      deviceName: 'd_1Lamp',
      value: '1'
    })
    expect(verification.rules[0].command.deviceName).toBe('d_1Lamp')
  })

  it('resolves legacy spec condition node ids before NuSMV normalization', () => {
    const verification = buildVerificationRequestPayload({
      nodes,
      deviceTemplates,
      rules: [],
      specifications,
      resolveNodeLabel,
      isAttack: false,
      intensity: 0,
      enablePrivacy: false
    })

    expect(verification.specs[0].aConditions[0]).toMatchObject({
      deviceId: 'd_1Lamp',
      deviceLabel: 'd_1Lamp',
      value: '1'
    })
  })
})
