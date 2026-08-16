// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, describe, expect, it } from 'vitest'
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
        traceViolationHere: 'Violation',
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

const createPointerEvent = (
  type: string,
  init: { pointerId: number; clientX: number; clientY: number; buttons?: number }
) => {
  const event = new Event(type, { bubbles: true, cancelable: true })
  Object.defineProperties(event, {
    pointerId: { value: init.pointerId },
    pointerType: { value: 'touch' },
    isPrimary: { value: true },
    button: { value: 0 },
    buttons: { value: init.buttons ?? 0 },
    clientX: { value: init.clientX },
    clientY: { value: init.clientY }
  })
  return event
}

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
    expect(wrapper.get('[data-testid="playback-change-dismiss"]').classes()).toContain('h-11')
    expect(wrapper.get('[data-testid="playback-change-dismiss"]').classes()).toContain('w-11')

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

  it('starts a fresh drag after a viewport change interrupts the previous gesture', async () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'simulation',
        stateNumber: 2,
        totalStates: 4,
        position: { x: 0, y: 0 },
        changes: [{
          deviceId: 'sensor_1',
          deviceLabel: 'Sensor',
          details: [{ kind: 'state', previousValue: 'idle', currentValue: 'active' }]
        }],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    const handle = wrapper.get('[data-testid="playback-change-drag-handle"]')
    await handle.trigger('mousedown', { button: 0, clientX: 100, clientY: 100 })
    window.dispatchEvent(new Event('resize'))

    await handle.trigger('mousedown', { button: 0, clientX: 200, clientY: 200 })
    window.dispatchEvent(new MouseEvent('mousemove', { clientX: 225, clientY: 230 }))
    window.dispatchEvent(new MouseEvent('mouseup', { clientX: 225, clientY: 230 }))

    expect(wrapper.emitted('move')?.at(-1)?.[0]).toEqual({ x: 25, y: 30 })
  })

  it('keeps pointer dragging usable when capture is unavailable', () => {
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'simulation',
        stateNumber: 2,
        totalStates: 4,
        position: { x: 0, y: 0 },
        changes: [{
          deviceId: 'sensor_1',
          deviceLabel: 'Sensor',
          details: [{ kind: 'state', previousValue: 'idle', currentValue: 'active' }]
        }],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    const handle = wrapper.get('[data-testid="playback-change-drag-handle"]')
    handle.element.dispatchEvent(createPointerEvent('pointerdown', {
      pointerId: 7,
      clientX: 100,
      clientY: 100,
      buttons: 1
    }))
    window.dispatchEvent(createPointerEvent('pointerup', {
      pointerId: 7,
      clientX: 100,
      clientY: 100
    }))

    handle.element.dispatchEvent(createPointerEvent('pointerdown', {
      pointerId: 8,
      clientX: 200,
      clientY: 200,
      buttons: 1
    }))
    window.dispatchEvent(createPointerEvent('pointermove', {
      pointerId: 8,
      clientX: 225,
      clientY: 230,
      buttons: 1
    }))
    window.dispatchEvent(createPointerEvent('pointerup', {
      pointerId: 8,
      clientX: 225,
      clientY: 230
    }))

    expect(wrapper.emitted('move')?.at(-1)?.[0]).toEqual({ x: 25, y: 30 })
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
        violationStateNumber: 2,
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
    expect(wrapper.get('[data-testid="playback-violation-badge"]').text()).toContain('First violation')
  })

  it('marks the violating state of a verification counterexample, not only an exploration finding', () => {
    // The badge was gated on `kind === 'fuzzing'`, so a safety counterexample's violating state carried no
    // marker here while the rail marker directly beneath it said "Violation" on that same state — the one
    // panel explaining what happens at this state was the only surface silent about the fault.
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'counterexample',
        stateNumber: 3,
        totalStates: 3,
        violationStateNumber: 3,
        position: { x: 0, y: 0 },
        changes: [{
          deviceId: 'lock-1',
          deviceLabel: 'Front lock',
          details: [{ kind: 'state', previousValue: 'locked', currentValue: 'unlocked' }]
        }],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [i18n] }
    })

    // "Violation", matching the rail marker's wording rather than exploration's "First violation" — a
    // counterexample has exactly one violating state, so "first" would imply others exist.
    expect(wrapper.get('[data-testid="playback-violation-badge"]').text()).toContain('Violation')
    expect(wrapper.get('[data-testid="playback-violation-badge"]').text()).not.toContain('First')
  })

  it('marks no state when the fault is a cycle rather than a single state', () => {
    // A liveness counterexample gets `undefined`, because the repetition is the violation and the loop
    // sentence carries that. A badge naming one state of the cycle would be a different, wrong claim.
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'counterexample',
        stateNumber: 3,
        totalStates: 3,
        violationStateNumber: undefined,
        isLivenessViolation: true,
        loopRange: { start: 2, end: 3 },
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

    expect(wrapper.find('[data-testid="playback-violation-badge"]').exists()).toBe(false)
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

  it('keeps a custom device-state property raw when its name collides with a bundled token', () => {
    appI18n.global.locale.value = 'zh-CN'
    const wrapper = mount(PlaybackChangePopover, {
      props: {
        kind: 'fuzzing',
        stateNumber: 1,
        totalStates: 1,
        position: { x: 0, y: 0 },
        inputEvents: [{
          step: 0,
          kind: 'DEVICE_STATE',
          targetId: 'custom-1',
          targetLabel: '自定义设备',
          property: 'workingState',
          value: 'active',
          source: 'MODEL_CHOICE'
        }],
        changes: [],
        environmentChanges: [],
        triggeredRules: [],
        compromisedAutomationLinks: [],
        animatedEdgeCount: 0,
        compromisedEdgeCount: 0
      },
      global: { plugins: [appI18n] }
    })

    const text = wrapper.get('[data-testid="playback-change-fuzz-inputs"]').text()
    expect(text).toContain('自定义设备.workingState')
    expect(text).not.toContain('自定义设备.工作状态')
  })

  /*
   * The loop sentence had no rendering coverage at all: the only guard was a source-read asserting the
   * loop-back block is ordered before the generic empty state. That check cannot see what the block
   * *says*, which is how the liveness wording came to be "State 3 loops back to state 2" — mechanically
   * true, but the same kind of statement as the safety wording, silent on the one fact the liveness
   * branch exists to convey. Mounted with the real `appI18n` so the assertions read the shipped strings.
   */
  describe('the sentence on the state that closes the cycle', () => {
    // `appI18n` is a module singleton and the cases above switch it to zh-CN without restoring it, so each
    // case here sets the locale it asserts against and this hook hands the module back in a known state.
    afterEach(() => {
      appI18n.global.locale.value = 'en'
    })

    const loopProps = (overrides: Record<string, unknown>) => ({
      kind: 'counterexample' as const,
      stateNumber: 3,
      totalStates: 3,
      position: { x: 0, y: 0 },
      changes: [],
      environmentChanges: [],
      triggeredRules: [],
      compromisedAutomationLinks: [],
      animatedEdgeCount: 0,
      compromisedEdgeCount: 0,
      isLoopBackState: true,
      ...overrides
    })

    it('says the cycle itself is the violation for a liveness property', () => {
      appI18n.global.locale.value = 'en'
      const wrapper = mount(PlaybackChangePopover, {
        props: loopProps({ isLivenessViolation: true, loopRange: { start: 2, end: 3 } }),
        global: { plugins: [appI18n] }
      })

      const text = wrapper.get('[data-testid="playback-change-loop-back"]').text()
      expect(text).toContain('2')
      expect(text).toContain('3')
      // The claim, not just the arithmetic: a reader must learn why an unmoving final step is the fault.
      expect(text).toMatch(/never reached/i)
      expect(text).toMatch(/violation/i)
      // And it must not fall through to the generic empty state, which is what it replaces.
      expect(wrapper.find('[data-testid="playback-change-empty"]').exists()).toBe(false)
    })

    it('claims nothing about liveness for a safety counterexample that ends on a cycle', () => {
      // NuSMV reports a loop for these too — measured on both a CTL `AX` and an LTL `G(p)` refutation —
      // and there the fault is a single state, so "the required state is never reached" would be false.
      appI18n.global.locale.value = 'en'
      const wrapper = mount(PlaybackChangePopover, {
        props: loopProps({
          isLivenessViolation: false,
          loopRange: { start: 2, end: 3 },
          violationStateNumber: 3
        }),
        global: { plugins: [appI18n] }
      })

      const text = wrapper.get('[data-testid="playback-change-loop-back"]').text()
      expect(text).not.toMatch(/never reached/i)
      expect(text).toContain('2')
    })

    it('falls back to the range-free sentence when no loop range is resolved', () => {
      // Both flags can be absent independently, so the popover must not render a half-built sentence
      // with a literal `{start}` in it.
      appI18n.global.locale.value = 'en'
      const wrapper = mount(PlaybackChangePopover, {
        props: loopProps({ isLivenessViolation: true, loopRange: null }),
        global: { plugins: [appI18n] }
      })

      const text = wrapper.get('[data-testid="playback-change-loop-back"]').text()
      expect(text.length).toBeGreaterThan(0)
      expect(text).not.toContain('{')
    })
  })
})
