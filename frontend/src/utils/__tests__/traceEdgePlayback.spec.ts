import { describe, expect, it } from 'vitest'
import type { DeviceEdge } from '@/types/edge'
import {
  formatRuleApiSignalName,
  getTraceValueForEdge,
  isEdgeActiveInTrace,
  isEdgeCompromisedInTrace,
  isEdgeConditionSatisfied,
  shouldAnimateEdgeFlow
} from '../traceEdgePlayback'

const apiEdge = (overrides: Partial<DeviceEdge> = {}): DeviceEdge => ({
  id: 'edge-1',
  from: 'button-1',
  to: 'alarm-1',
  fromLabel: 'Button',
  toLabel: 'Alarm',
  fromPos: { x: 0, y: 0 },
  toPos: { x: 1, y: 1 },
  fromApi: 'press',
  toApi: 'siren',
  itemType: 'api',
  relation: '',
  value: '',
  ruleId: 'rule-1',
  ruleIndex: 0,
  sourceIndex: 0,
  ...overrides
})

describe('trace edge playback', () => {
  it('uses NuSMV API signal variables when highlighting rule edges', () => {
    const edge = apiEdge()
    const trace = {
      selectedStateIndex: 1,
      states: [
        {
          triggeredRules: [],
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'press_a', value: 'FALSE' }] }
          ]
        },
        {
          triggeredRules: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Press starts alarm' }],
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'press_a', value: 'TRUE' }] }
          ]
        }
      ]
    }

    expect(getTraceValueForEdge(edge, trace, 1)).toBe('TRUE')
    expect(isEdgeConditionSatisfied(edge, trace, 1)).toBe(true)
    expect(isEdgeActiveInTrace(edge, [edge], trace)).toBe(true)
  })

  it('does not treat an API signal as active when the trace signal is false', () => {
    const edge = apiEdge()
    const trace = {
      selectedStateIndex: 1,
      states: [
        {
          triggeredRules: [],
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'press_a', value: 'FALSE' }] }
          ]
        },
        {
          triggeredRules: [],
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'press_a', value: 'FALSE' }] }
          ]
        }
      ]
    }

    expect(isEdgeConditionSatisfied(edge, trace, 1)).toBe(false)
    expect(isEdgeActiveInTrace(edge, [edge], trace)).toBe(false)
  })

  it('does not infer a rule firing when the backend explicitly reports no triggered rules', () => {
    const edge = apiEdge({ itemType: 'state', fromApi: 'state', relation: '=', value: 'pressed' })
    const trace = {
      selectedStateIndex: 1,
      states: [
        { triggeredRules: [], devices: [{ deviceId: 'button_1', state: 'pressed', variables: [] }] },
        { triggeredRules: [], devices: [{ deviceId: 'button_1', state: 'pressed', variables: [] }] }
      ]
    }

    expect(isEdgeConditionSatisfied(edge, trace, 0)).toBe(true)
    expect(isEdgeActiveInTrace(edge, [edge], trace)).toBe(false)
  })

  it('matches historical playback by a unique stable rule id rather than current list position', () => {
    const edge = apiEdge({ ruleIndex: 99 })
    const trace = {
      selectedStateIndex: 1,
      states: [
        { triggeredRules: [], devices: [] },
        { triggeredRules: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Historical rule' }], devices: [] }
      ]
    }

    expect(isEdgeActiveInTrace(edge, [edge], trace)).toBe(true)
  })

  it('does not guess a current edge when historical rule ids are duplicated', () => {
    const first = apiEdge({ id: 'edge-1', ruleId: 'duplicate', ruleIndex: 0 })
    const second = apiEdge({ id: 'edge-2', ruleId: 'duplicate', ruleIndex: 1 })
    const trace = {
      selectedStateIndex: 1,
      states: [
        { triggeredRules: [], devices: [] },
        { triggeredRules: [{ ruleIndex: 1, ruleId: 'duplicate', ruleLabel: 'Second rule' }], devices: [] }
      ]
    }

    expect(isEdgeActiveInTrace(first, [first, second], trace)).toBe(false)
    expect(isEdgeActiveInTrace(second, [first, second], trace)).toBe(false)
  })

  it('does not bind an id-less historical rule to the current board by list position', () => {
    const edge = apiEdge()
    const trace = {
      selectedStateIndex: 0,
      states: [{ triggeredRules: [{ ruleIndex: 0, ruleId: null, ruleLabel: 'No id' }], devices: [] }]
    }

    expect(isEdgeActiveInTrace(edge, [edge], trace)).toBe(false)
  })

  it('animates only a delivered rule and stops a compromised link', () => {
    const edge = apiEdge({ ruleIndex: 99 })
    const other = apiEdge({ id: 'edge-2', ruleId: 'rule-2' })
    const trace = {
      selectedStateIndex: 0,
      states: [{
        triggeredRules: [
          { ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Blocked historical rule' },
          { ruleIndex: 1, ruleId: 'rule-2', ruleLabel: 'Delivered rule' }
        ],
        compromisedAutomationLinks: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Historical rule' }],
        devices: []
      }]
    }

    expect(isEdgeCompromisedInTrace(edge, [edge, other], trace)).toBe(true)
    expect(isEdgeCompromisedInTrace(other, [edge, other], trace)).toBe(false)
    expect(shouldAnimateEdgeFlow(edge, [edge, other], trace)).toBe(false)
    expect(shouldAnimateEdgeFlow(other, [edge, other], trace)).toBe(true)
  })

  it('does not imply command delivery outside playback or for an idle rule', () => {
    const edge = apiEdge()

    expect(shouldAnimateEdgeFlow(edge, [edge], null)).toBe(false)
    expect(shouldAnimateEdgeFlow(edge, [edge], {
      selectedStateIndex: 0,
      states: [{ triggeredRules: [], compromisedAutomationLinks: [], devices: [] }]
    })).toBe(false)
  })

  it('reads environment-pool variables for variable rule edges', () => {
    const edge = apiEdge({
      itemType: 'variable',
      fromApi: 'temperature',
      relation: '>',
      value: '28'
    })
    const trace = {
      selectedStateIndex: 0,
      states: [
        {
          devices: [{ deviceId: 'button_1', variables: [] }],
          envVariables: [{ name: 'temperature', value: '31' }]
        }
      ]
    }

    expect(getTraceValueForEdge(edge, trace, 0)).toBe('31')
    expect(isEdgeConditionSatisfied(edge, trace, 0)).toBe(true)
  })

  it('treats a_ as part of literal environment variable names during trace playback', () => {
    const edge = apiEdge({
      itemType: 'variable',
      fromApi: 'a_temperature',
      relation: '>',
      value: '28'
    })

    expect(getTraceValueForEdge(edge, {
      selectedStateIndex: 0,
      states: [
        {
          devices: [{ deviceId: 'button_1', variables: [] }],
          envVariables: [{ name: 'a_temperature', value: '31' }]
        }
      ]
    }, 0)).toBe('31')

    expect(getTraceValueForEdge(edge, {
      selectedStateIndex: 0,
      states: [
        {
          devices: [{ deviceId: 'button_1', variables: [] }],
          envVariables: [{ name: 'temperature', value: '31' }]
        }
      ]
    }, 0)).toBeNull()
  })

  it('does not let variable edges match API signal names implicitly', () => {
    const edge = apiEdge({
      itemType: 'variable',
      fromApi: 'press',
      relation: '=',
      value: 'TRUE'
    })
    const trace = {
      selectedStateIndex: 0,
      states: [
        {
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'press_a', value: 'TRUE' }] }
          ]
        }
      ]
    }

    expect(getTraceValueForEdge(edge, trace, 0)).toBeNull()
    expect(isEdgeConditionSatisfied(edge, trace, 0)).toBe(false)
  })

  it('keeps API signal naming aligned with the SMV generator', () => {
    expect(formatRuleApiSignalName('turn on')).toBe('turn_on_a')
    expect(getTraceValueForEdge(apiEdge({ fromApi: 'turn on' }), {
      selectedStateIndex: 0,
      states: [
        {
          devices: [
            { deviceId: 'button_1', variables: [{ name: 'turn_on_a', value: 'TRUE' }] }
          ]
        }
      ]
    }, 0)).toBe('TRUE')
  })
})
