import { describe, expect, it } from 'vitest'
import { analyzeBoardAttackSurface, getAttackSelectionIssue, selectedAttackPoints } from '@/utils/attackSurface'
import type { DeviceTemplate } from '@/types/device'
import type { DeviceNode } from '@/types/node'
import type { RuleForm } from '@/types/rule'

const node = (id: string, templateName: string): DeviceNode => ({ id, templateName } as DeviceNode)
const template = (name: string, falsifiable: boolean): DeviceTemplate => ({
  name,
  manifest: {
    Name: name,
    InternalVariables: [{
      Name: 'reading',
      IsInside: true,
      FalsifiableWhenCompromised: falsifiable,
      Trust: 'trusted',
      Privacy: 'public',
      Values: ['normal', 'alert']
    }]
  }
})

describe('analyzeBoardAttackSurface', () => {
  it('excludes device instances whose compromise cannot change model behavior', () => {
    const devices = [node('sensor', 'Sensor'), node('light', 'Light'), node('display', 'Display')]
    const templates = new Map([
      ['Sensor', template('Sensor', true)],
      ['Light', template('Light', false)],
      ['Display', template('Display', false)]
    ])
    const rules: RuleForm[] = [{
      sources: [{ fromId: 'sensor', fromApi: 'reading', itemType: 'variable', relation: '=', value: 'alert' }],
      toId: 'light',
      toApi: 'turnOn'
    }]

    const surface = analyzeBoardAttackSurface(devices, rules, device => templates.get(device.templateName))

    expect([...surface.effectfulDeviceIds]).toEqual(['light', 'sensor'])
    expect(surface.devicePointCount).toBe(2)
    expect(surface.automationLinkPointCount).toBe(1)
    expect(surface.totalPointCount).toBe(3)
  })

  it('deduplicates a target that also has falsifiable readings', () => {
    const devices = [node('hub', 'Hub')]
    const rules: RuleForm[] = [{ sources: [], toId: 'hub', toApi: 'refresh' }]

    const surface = analyzeBoardAttackSurface(devices, rules, () => template('Hub', true))

    expect(surface.devicePointCount).toBe(1)
    expect(surface.totalPointCount).toBe(2)
  })

  it('keeps the canvas key but sends the normalized model device id', () => {
    const surface = analyzeBoardAttackSurface(
      [node('device-a1b2', 'Sensor')],
      [],
      () => template('Sensor', true)
    )

    expect(surface.points[0]).toMatchObject({
      key: 'DEVICE:device-a1b2',
      deviceId: 'device_a1b2'
    })
    expect(selectedAttackPoints(surface, ['DEVICE:device-a1b2'])).toEqual([
      { kind: 'DEVICE', deviceId: 'device_a1b2' }
    ])
  })
})

describe('getAttackSelectionIssue', () => {
  it('keeps disabled attack modeling independent from a stale budget', () => {
    expect(getAttackSelectionIssue(false, 9, 0)).toBeNull()
  })

  it('requires an effectful attack surface when attack modeling stays selected', () => {
    expect(getAttackSelectionIssue(true, 1, 0)).toBe('NO_MODELED_EFFECT')
  })

  it('requires the user to revise a budget after the current attack surface shrinks', () => {
    expect(getAttackSelectionIssue(true, 4, 3)).toBe('INVALID_BUDGET')
    expect(getAttackSelectionIssue(true, 3, 3)).toBeNull()
  })
})
