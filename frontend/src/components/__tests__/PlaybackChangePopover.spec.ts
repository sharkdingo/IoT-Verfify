// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it } from 'vitest'
import PlaybackChangePopover from '../PlaybackChangePopover.vue'

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
        traceVisualization: {
          simulationStepChanges: 'Device Changes in This Step',
          counterexampleStepChanges: 'Counterexample Changes in This Step',
          playbackChangesSummary: '{devices} device(s), {environment} environment value(s), {rules} rule(s)',
          playbackInitialStateNoPrevious: 'Initial state has no previous state',
          playbackNoObservableChanges: 'No observable values changed',
          environmentChanges: 'Environment changes',
          automationInThisStep: 'Automation in this step',
          playbackAnimatedEdges: '{count} matching edge(s) animate',
          playbackTriggeredRuleWithoutCurrentEdge: 'No current matching edge',
          playbackInitialEdgesStatic: 'Initial edges remain still',
          playbackEdgesStaticNoRule: 'No rule produced this state; edges remain still',
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
        triggeredRules: [{ ruleId: 'rule-1', ruleLabel: 'Motion starts recording' }],
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
    expect(wrapper.get('[data-testid="playback-change-automation"]').text()).toContain('edges remain still')
  })
})
