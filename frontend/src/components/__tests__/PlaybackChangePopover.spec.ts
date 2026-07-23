// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import PlaybackChangePopover from '../PlaybackChangePopover.vue'
import { i18n as appI18n } from '@/assets/i18n'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        state: 'State',
        mode: 'Mode',
        variableValue: 'Value',
        trusted: 'trusted',
        untrusted: 'untrusted',
        private: 'private data',
        public: 'public data',
        trust: 'trust',
        privacy: 'privacy',
        unknown: 'Unknown',
        fuzzFirstViolation: 'First violation',
        traceVisualization: {
          simulationStepChanges: 'Device Changes in This Step',
          counterexampleStepChanges: 'Counterexample Changes in This Step',
          fuzzingStepChanges: 'Candidate Changes in This Step',
          fuzzInputsInThisStep: 'Exploration inputs in this state',
          fuzzDeviceStateInput: 'Device-state input',
          fuzzDeviceInput: 'Device-variable input',
          fuzzEnvironmentInput: 'Environment-value input',
          fuzzEnvironmentRateInput: 'Environment-rate input',
          fuzzRandomInitialSource: 'Random initial state',
          fuzzSeedEventSource: 'Seed-generated input',
          fuzzModelChoiceSource: 'Model choice',
          noFuzzInputInThisStep: 'No exploration input was injected',
          fuzzObservedModelChanges: 'Observable model or natural changes',
          playbackInitialStateSummary: 'Initial path state; there is no previous state to compare.',
          playbackChangesSummaryWithRules: '{devices} device(s) and {environment} environment value(s) changed; {rules} user automation(s) ran in this step.',
          playbackChangesSummaryWithoutRules: '{devices} device(s) and {environment} environment value(s) changed; no user automation ran in this step.',
          playbackInitialStateNoPrevious: 'Initial state has no previous state',
          playbackNoObservableChanges: 'No observable values changed',
          environmentChanges: 'Environment changes',
          automationInThisStep: 'Automations run in this step',
          playbackAnimatedEdges: '{count} matching edge(s) animate',
          playbackTriggeredRuleWithoutCurrentEdge: 'No current matching edge',
          playbackCompromisedEdgesStatic: '{count} compromised edge(s) remain still',
          dismissChanges: 'Hide changes',
          moveChangesPanel: 'Drag to move the change panel',
          securityLabels: 'Trust / privacy labels',
          compromiseStatus: 'Compromise status',
          compromised: 'Compromised',
          notCompromised: 'Not compromised',
          changeCountSuffix: 'change(s)',
          stateLabel: 'State'
        }
      }
    }
  }
})

describe('PlaybackChangePopover', () => {
  it('shows independent, user-facing before/after facts and can be dismissed', async () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'simulation',
        stateNumber: 4,
        totalStates: 8,
        position: { x: 0, y: 0 },
        environmentChanges: [{ name: 'illuminance', previousValue: '20', currentValue: '21' }],
        triggeredRules: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Motion starts recording' }],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 1,
        compromisedEdgeCount: 0,
        changes: [{
          deviceId: 'internal_camera_1',
          deviceLabel: 'Hall camera',
          details: [
            { kind: 'state', previousValue: 'idle', currentValue: 'recording' },
            { kind: 'variable', name: 'motion', previousValue: 'FALSE', currentValue: 'TRUE' },
            { kind: 'security', name: 'video', previousValue: 'privacy=public', currentValue: 'privacy=private' }
          ]
        }]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Device Changes in This Step')
    expect(wrapper.text()).toContain('Hall camera')
    expect(wrapper.text()).toContain('idle')
    expect(wrapper.text()).toContain('recording')
    expect(wrapper.text()).toContain('illuminance')
    expect(wrapper.text()).toContain('Motion starts recording')
    expect(wrapper.text()).not.toContain('internal_camera_1')

    await wrapper.get('[data-testid="playback-change-dismiss"]').trigger('click')
    expect(wrapper.emitted('dismiss')).toHaveLength(1)
  })

  it('emits a bounded position while dragging the header', async () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'simulation',
        stateNumber: 2,
        totalStates: 3,
        position: { x: 0, y: 0 },
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0,
        changes: [{
          deviceId: 'sensor_1',
          deviceLabel: 'Sensor',
          details: [{ kind: 'state', previousValue: 'idle', currentValue: 'active' }]
        }]
      },
      global: { plugins: [i18n] }
    })

    const handle = wrapper.get('[data-testid="playback-change-drag-handle"]')
    await handle.trigger('mousedown', { button: 0, clientX: 100, clientY: 100 })
    window.dispatchEvent(new MouseEvent('mousemove', { clientX: 140, clientY: 135 }))
    window.dispatchEvent(new MouseEvent('mouseup', { clientX: 140, clientY: 135 }))

    expect(wrapper.emitted('move')).toBeTruthy()
    expect(wrapper.emitted('move')?.at(-1)?.[0]).toEqual(expect.objectContaining({ x: 40, y: 35 }))
  })

  it('stays informative when a playback state has no observable delta', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'simulation',
        stateNumber: 3,
        totalStates: 5,
        position: { x: 0, y: 0 },
        changes: [],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="playback-change-empty"]').text()).toContain('No observable values changed')
    expect(wrapper.text()).toContain('no user automation ran in this step')
    expect(wrapper.find('[data-testid="playback-change-automation"]').exists()).toBe(false)
  })

  it('does not show an empty automation card for device and environment evolution', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'counterexample',
        stateNumber: 7,
        totalStates: 26,
        position: { x: 0, y: 0 },
        changes: [{
          deviceId: 'clock-1',
          deviceLabel: 'Living room clock',
          details: [{ kind: 'variable', name: 'time', previousValue: '4', currentValue: '5' }]
        }],
        environmentChanges: [
          { name: 'time', previousValue: '4', currentValue: '5' },
          { name: 'illuminance', previousValue: '5', currentValue: '4' }
        ],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('1 device(s) and 2 environment value(s) changed')
    expect(wrapper.text()).toContain('no user automation ran in this step')
    expect(wrapper.find('[data-testid="playback-change-automation"]').exists()).toBe(false)
  })

  it('separates fuzz inputs from rule and model changes and marks the first violation', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 2,
        totalStates: 4,
        firstViolationStateNumber: 2,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 1,
          kind: 'DEVICE_VARIABLE',
          targetId: 'sensor-1',
          targetLabel: 'Hall sensor',
          property: 'motion',
          value: 'active',
          source: 'MODEL_CHOICE'
        }],
        changes: [{
          deviceId: 'alarm-1',
          deviceLabel: 'Alarm',
          details: [{ kind: 'state', previousValue: 'off', currentValue: 'on' }]
        }],
        environmentChanges: [],
        triggeredRules: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Motion activates alarm' }],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 1,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()).toContain('Hall sensor.motion')
    expect(wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()).toContain('active')
    expect(wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()).toContain('Model choice')
    expect(wrapper.get('[data-testid="playback-change-automation"]').text()).toContain('Motion activates alarm')
    expect(wrapper.text()).toContain('Observable model or natural changes')
    expect(wrapper.get('[data-testid="fuzzing-first-violation-badge"]').text()).toContain('First violation')
  })

  it('distinguishes random initialization from a seed-generated input at the same state', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 1,
        totalStates: 2,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 0,
          kind: 'DEVICE_STATE',
          targetId: 'door-1',
          targetLabel: 'Front door',
          property: 'workingState',
          value: 'closed',
          source: 'RANDOM_INITIAL_STATE'
        }, {
          step: 0,
          kind: 'DEVICE_STATE',
          targetId: 'door-1',
          targetLabel: 'Front door',
          property: 'workingState',
          value: 'open',
          source: 'SEED_EVENT'
        }],
        changes: [],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    const evidence = wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()
    expect(evidence).toContain('Random initial state')
    expect(evidence).toContain('Seed-generated input')
    expect(evidence).toContain('Device-state input')
    expect(evidence).toContain('Front door.workingState')
  })

  it('presents an encoded environment rate as a user-facing numeric rate', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 2,
        totalStates: 3,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 1,
          kind: 'ENVIRONMENT_RATE',
          targetId: 'environment',
          property: 'temperature',
          value: 'rate:-1',
          source: 'SEED_EVENT'
        }],
        changes: [],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    const evidence = wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()
    expect(evidence).toContain('Environment-rate input')
    expect(evidence).toContain('-1')
    expect(evidence).not.toContain('rate:-1')
  })

  it('localizes canonical model evidence in Chinese and leaves custom tokens unchanged', () => {
    appI18n.global.locale.value = 'zh-CN'
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 2,
        totalStates: 3,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 1,
          kind: 'DEVICE_STATE',
          targetId: 'door-1',
          targetLabel: '前门',
          property: 'workingState',
          value: 'locked',
          source: 'SEED_EVENT'
        }],
        changes: [{
          deviceId: 'door-1',
          deviceLabel: '前门',
          details: [
            { kind: 'state', previousValue: 'off', currentValue: 'locked' },
            { kind: 'variable', name: 'temperature', previousValue: '20', currentValue: '21' },
            { kind: 'variable', name: 'customMetric', previousValue: 'eco', currentValue: 'ecoBoost' }
          ]
        }],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0,
        bundledDeviceIds: ['door-1']
      },
      global: { plugins: [appI18n] }
    })

    const text = wrapper.text()
    expect(text).toContain('工作状态')
    expect(text).toContain('关闭')
    expect(text).toContain('已锁定')
    expect(text).toContain('温度')
    expect(text).toContain('customMetric')
    expect(text).toContain('ecoBoost')
  })

  it('keeps custom tokens raw when they collide with bundled identifiers', () => {
    appI18n.global.locale.value = 'zh-CN'
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 2,
        totalStates: 2,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 1,
          kind: 'DEVICE_VARIABLE',
          targetId: 'custom-1',
          targetLabel: '自定义设备',
          property: 'workingState',
          value: 'off',
          source: 'MODEL_CHOICE'
        }],
        changes: [{
          deviceId: 'custom-1',
          deviceLabel: '自定义设备',
          details: [
            { kind: 'state', previousValue: 'off', currentValue: 'active' },
            { kind: 'variable', name: 'workingState', previousValue: 'off', currentValue: 'active' }
          ]
        }],
        environmentChanges: [{ name: 'weather', previousValue: 'off', currentValue: 'active' }],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [appI18n] }
    })

    const text = wrapper.text()
    expect(text).toContain('workingState')
    expect(text).toContain('weather')
    expect(text).toContain('off')
    expect(text).toContain('active')
    expect(text).not.toContain('工作状态')
  })
})
