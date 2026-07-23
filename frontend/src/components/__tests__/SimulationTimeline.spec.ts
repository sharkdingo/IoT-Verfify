// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import SimulationTimeline from '../SimulationTimeline.vue'
import type { SimulationState } from '@/types/simulation'

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        close: 'Close',
        unknown: 'Unknown',
        state: 'State',
        mode: 'Mode',
        ruleNumber: 'Rule {number}',
        runDetails: 'Run details',
        viewSimulationRunDetails: 'View run details',
        runScopeAndSnapshot: 'Run Scope and Submission Snapshot',
        simulationStoppedBeforeRequestedSteps: 'Only {actual} of {requested} transitions were returned',
        modelSemanticsUnavailable: 'Model semantics unavailable',
        environmentEvolutionIncluded: 'Shared environment evolution and local stutter semantics',
        labelPropagationScopeSummary: 'Labels propagate only on automation commands',
        attackExactSelectionShort: '{count} explicit points',
        attackExhaustiveSelectionShort: 'Exhaustive up to {count} points',
        attackExactSelectionDetail: 'Explicit points ({count}): {points}',
        attackExhaustiveSelectionDetail: 'Exhaustive up to {count} of {total} points',
        attackDevicePoint: 'device {id}',
        attackAutomationLinkPoint: 'rule link #{id}',
        modelRunSnapshotTitle: 'Frozen Submission Snapshot',
        modelRunSnapshotSummary: 'Captured {time}: {devices} devices, {rules} rules, {specs} specs, {variables} variables, {templates} templates',
        runBoardInputUnchanged: 'Current input matches',
        runBoardInputChanged: 'Current input changed',
        runBoardComparisonUnavailable: 'Comparison unavailable',
        runBoardNotCompared: 'Current board not compared',
        runBoardInputUnchangedShort: 'Current input matches',
        runBoardInputChangedShort: 'Current input changed',
        runBoardComparisonUnavailableShort: 'Comparison unavailable',
        runBoardNotComparedShort: 'Current board not compared',
        traceVisualization: {
          stateSequence: 'State sequence',
          modelTracePlayback: 'Model Trace Playback',
          modelTraceNotPrediction: 'Model execution, not a physical prediction',
          simulationAttackContext: 'Attack budget {count} of {total} ({devices} devices + {links} links)',
          simulationNoAttackContext: 'No attack behavior modeled',
          privacyPropagationNotModeled: 'Privacy propagation not modeled',
          playbackSnapshotReadOnly: 'Saved read-only run snapshot',
          modelIncompletePlayback: 'Incomplete model: {rules} rules omitted',
          initialModelState: 'Initial model state',
          rulesAppliedToReachState: 'Rules that produced this state',
          noRulesApplied: 'No automation rule drove this step',
          historicalRuleNotOnCurrentBoard: 'Historical rule is no longer on this board',
          devicesInCurrentState: 'Devices in this state',
          historicalDeviceNotOnCurrentBoard: 'Historical device is no longer on this board',
          runtimeCompromisedPoints: 'Current compromised points',
          compromisedAutomationLinks: 'Compromised automation links in this branch',
          compromisedAutomationLinkHint: 'Command does not reach the target',
          attackScenario: 'Attack scenario',
          attackBudget: 'budget',
          privacyPropagationEnabled: 'Privacy propagation modeled',
          state: 'State {index}',
          compromisedPointCount: 'Current Compromised Points',
          attackedBang: 'Attacked',
          attacked: 'Attacked',
          includesUntrustedSource: 'Includes untrusted source',
          includesPrivateData: 'Includes private-data label',
          untrustedLabelDetails: 'Untrusted source labels: {labels}',
          privateLabelDetails: 'Private-data labels: {labels}',
          stop: 'Stop',
          pause: 'Pause',
          play: 'Play',
          jumpToState: 'Jump to state',
          previousState: 'Previous state',
          nextState: 'Next state',
          stateLabel: 'State',
          stateDetails: 'State details',
          transitionNumber: 'State after transition {index}',
          environmentVariables: 'Environment variables',
          changed: 'Changed',
          deviceBecameCompromised: 'Device became compromised',
          deviceNoLongerCompromised: 'Device is no longer compromised'
        }
      }
    }
  }
})

const states = (prefix: string): SimulationState[] => [
  {
    stateIndex: 1,
    triggeredRules: [],
    compromisedAutomationLinks: [],
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', state: 'idle', variables: [] }]
  },
  {
    stateIndex: 2,
    triggeredRules: [{ ruleId: 'rule-1', ruleLabel: `${prefix} activation` }],
    compromisedAutomationLinks: [],
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', state: 'active', variables: [] }]
  },
  {
    stateIndex: 3,
    triggeredRules: [],
    compromisedAutomationLinks: [],
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', state: 'done', variables: [] }]
  }
]

describe('SimulationTimeline', () => {
  beforeEach(() => {
    Element.prototype.scrollIntoView = vi.fn()
  })

  afterEach(() => {
    vi.useRealTimers()
  })

  it('resets playback focus to the first state whenever it opens', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: states('first')
      },
      global: {
        plugins: [i18n]
      }
    })

    await wrapper.get('[data-testid="simulation-timeline-state-2"]').trigger('click')
    expect(wrapper.get('[data-testid="simulation-timeline"]').attributes('data-selected-state-index')).toBe('2')

    await wrapper.setProps({ visible: false })
    await wrapper.setProps({ states: states('second'), visible: true })

    expect(wrapper.get('[data-testid="simulation-timeline"]').attributes('data-selected-state-index')).toBe('0')
    const highlightEvents = wrapper.emitted('highlight-state') || []
    expect(highlightEvents.at(-1)?.[0]).toMatchObject({ selectedStateIndex: 0 })
  })

  it('resets to the first state when a same-length run replaces the visible run', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: { visible: true, states: states('first') },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-testid="simulation-timeline-state-2"]').trigger('click')
    await wrapper.setProps({ states: states('replacement') })

    expect(wrapper.get('[data-testid="simulation-timeline"]').attributes('data-selected-state-index')).toBe('0')
    expect((wrapper.emitted('highlight-state') || []).at(-1)?.[0]).toMatchObject({
      selectedStateIndex: 0,
      states: expect.arrayContaining([
        expect.objectContaining({ devices: expect.arrayContaining([
          expect.objectContaining({ deviceId: 'replacement_sensor' })
        ]) })
      ])
    })
  })

  it('returns the control to Play as soon as the final state is displayed', async () => {
    vi.useFakeTimers()
    const wrapper = mount(SimulationTimeline, {
      props: { visible: true, states: states('playback') },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-testid="simulation-timeline-play"]').trigger('click')
    await vi.advanceTimersByTimeAsync(3_000)

    expect(wrapper.get('[data-testid="simulation-timeline"]').attributes('data-selected-state-index')).toBe('2')
    expect(wrapper.get('[data-testid="simulation-timeline-play"]').attributes('aria-label')).toBe('Play')
  })

  it('opens run details from the timeline header instead of a separate floating overlay', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: { visible: true, states: states('details') },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-testid="simulation-timeline-run-details"]').trigger('click')

    expect(wrapper.emitted('open-run-details')).toHaveLength(1)
  })

  it('keeps a shortened simulation horizon visible during playback', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: states('short'),
        actualSteps: 2,
        requestedSteps: 6
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="simulation-timeline-short-horizon-warning"]').text())
      .toContain('2 of 6')
  })

  it('shows compromised-point count only from runtime global variables', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: [
          {
            stateIndex: 1,
            triggeredRules: [],
            compromisedAutomationLinks: [],
            devices: [{ deviceId: 'sensor_1', deviceLabel: 'Sensor', templateName: 'Sensor', variables: [] }],
            envVariables: [{ name: 'attackBudget', value: '9' }],
            globalVariables: [{ name: 'compromisedPointCount', value: '4' }]
          }
        ]
      },
      global: {
        plugins: [i18n]
      }
    })

    expect(wrapper.text()).toContain('Current compromised points: 4')
    expect(wrapper.text()).not.toContain('Current compromised points: 9')
  })

  it('explains an attack budget with immutable counts from the run snapshot', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: states('snapshot'),
        isAttack: true,
        attackBudget: 2,
        enablePrivacy: false,
        modelSemantics: {
          attackPointUnit: 'BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK',
          attackSelectionPolicy: 'UP_TO_ATTACK_BUDGET_NONDETERMINISTIC',
          attackEffects: [
            'DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN',
            'COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED',
            'COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED'
          ],
          modeledDeviceAttackPointCount: 3,
          modeledFalsifiableReadingDeviceCount: 1,
          modeledAutomationLinkAttackPointCount: 2,
          modeledAttackPointCount: 5,
          trustPropagationPolicy: 'TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED',
          privacyPropagationPolicy: 'NOT_MODELED',
          labelPropagationScope: 'AUTOMATION_RULE_COMMANDS_ONLY',
          environmentEvolutionEffects: [
            'DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN',
            'DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN'
          ],
          localVariableFallbackPolicy: 'STUTTER_WHEN_NO_DECLARED_EVOLUTION'
        }
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Exhaustive up to 2 of 5 points')
    expect(wrapper.text()).toContain('Labels propagate only on automation commands')
    expect(wrapper.text()).not.toContain('Model semantics unavailable')
  })

  it('does not infer attack mechanisms when persisted model semantics are unavailable', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: states('legacy'),
        isAttack: true,
        attackBudget: 2,
        enablePrivacy: true
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Model semantics unavailable')
    expect(wrapper.text()).not.toContain('Attack budget 2 of')
    expect(wrapper.text()).not.toContain('Privacy propagation modeled')
    expect(wrapper.text()).toContain('Attack scenario')
  })

  it('does not treat an environment variable named attackBudget as attack count', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: [
          {
            stateIndex: 1,
            triggeredRules: [],
            compromisedAutomationLinks: [],
            devices: [{ deviceId: 'sensor_1', deviceLabel: 'Sensor', templateName: 'Sensor', variables: [] }],
            envVariables: [{ name: 'attackBudget', value: '9' }]
          }
        ]
      },
      global: {
        plugins: [i18n]
      }
    })

    expect(wrapper.text()).toContain('attackBudget')
    expect(wrapper.text()).not.toContain('Current compromised points: 9')
  })

  it('does not render an invalid historical compromised-point count as NaN', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: [{
          stateIndex: 1,
          triggeredRules: [],
          compromisedAutomationLinks: [],
          devices: [],
          globalVariables: [{ name: 'compromisedPointCount', value: 'unknown' }]
        }]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).not.toContain('NaN')
    expect(wrapper.text()).not.toContain('Current compromised points:')
  })

  it('shows model scope, completeness, and exact triggered-rule history', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: states('history'),
        modelComplete: false,
        disabledRuleCount: 2,
        modelSnapshot: {
          capturedAt: '2026-07-12T09:30:00',
          deviceCount: 3,
          ruleCount: 2,
          specificationCount: 0,
          environmentVariableCount: 1,
          deviceTemplateCount: 1,
          templatesFrozen: true
        },
        boardComparison: 'CHANGED',
        currentRuleIds: []
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('Model execution, not a physical prediction')
    expect(wrapper.get('[data-testid="simulation-timeline-incomplete-warning"]').text())
      .toContain('2 rules omitted')
    expect(wrapper.get('[data-testid="simulation-timeline-snapshot-notice"]').text())
      .toContain('3 devices, 2 rules, 0 specs, 1 variables, 1 templates')
    expect(wrapper.get('[data-testid="simulation-board-comparison"]').text())
      .toContain('Current input changed')

    await wrapper.get('[data-testid="simulation-timeline-state-1"]').trigger('click')
    const ruleSummary = wrapper.get('[data-testid="simulation-timeline-triggered-rules"]')
    expect(ruleSummary.text()).toContain('history activation')
    expect(ruleSummary.find('[title="Historical rule is no longer on this board"]').exists()).toBe(true)
  })

  it('keeps historical devices visible and marks state changes in the saved snapshot', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        currentDeviceIds: ['current_sensor'],
        states: [
          {
            stateIndex: 1,
            triggeredRules: [],
            compromisedAutomationLinks: [],
            devices: [
              { deviceId: 'current_sensor', deviceLabel: 'Current sensor', templateName: 'Sensor', state: 'idle', variables: [] },
              { deviceId: 'removed_lock', deviceLabel: 'Removed lock', templateName: 'Lock', state: 'locked', variables: [] }
            ]
          },
          {
            stateIndex: 2,
            triggeredRules: [],
            compromisedAutomationLinks: [],
            devices: [
              { deviceId: 'current_sensor', deviceLabel: 'Current sensor', templateName: 'Sensor', state: 'active', variables: [] },
              {
                deviceId: 'removed_lock',
                deviceLabel: 'Removed lock',
                templateName: 'Lock',
                state: 'unlocked',
                compromised: true,
                variables: []
              }
            ]
          }
        ]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="simulation-timeline-snapshot-notice"]').text())
      .toContain('Saved read-only run snapshot')

    await wrapper.get('[data-testid="simulation-timeline-state-1"]').trigger('click')
    const devices = wrapper.get('[data-testid="simulation-timeline-devices"]')
    expect(devices.text()).toContain('Current sensor')
    expect(devices.text()).toContain('active')
    expect(devices.text()).toContain('Removed lock')
    expect(devices.text()).toContain('unlocked')
    expect(devices.text()).toContain('idle -> active')
    expect(devices.text()).toContain('locked -> unlocked')
    expect(devices.text()).toContain('Attacked')
    expect(devices.find('[title="Historical device is no longer on this board"]').exists()).toBe(true)
  })

  it('shows trust and privacy facts from the selected historical state', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: [{
          stateIndex: 1,
          triggeredRules: [],
          compromisedAutomationLinks: [],
          devices: [{
            deviceId: 'camera_1',
            deviceLabel: 'Hall camera',
            templateName: 'Camera',
            mode: 'CameraMode',
            state: 'recording',
            variables: [{ name: 'motion', value: 'TRUE', trust: 'untrusted' }],
            trustPrivacy: [{ name: 'recording', propertyScope: 'state', mode: 'CameraMode', trust: true }],
            privacies: [{ name: 'video', propertyScope: 'content', privacy: 'private' }]
          }]
        }]
      },
      global: { plugins: [i18n] }
    })

    const devices = wrapper.get('[data-testid="simulation-timeline-devices"]')
    expect(devices.text()).toContain('Includes untrusted source')
    expect(devices.text()).toContain('Includes private-data label')
    expect(devices.find('[title="Untrusted source labels: motion"]').exists()).toBe(true)
    expect(devices.find('[title="Private-data labels: video"]').exists()).toBe(true)
  })

  it('formats bundled playback tokens at the display boundary without mutating saved states', () => {
    const savedStates: SimulationState[] = [{
      stateIndex: 1,
      triggeredRules: [],
      compromisedAutomationLinks: [],
      devices: [{
        deviceId: 'camera_1',
        deviceLabel: 'Hall camera',
        templateName: 'Camera',
        mode: 'MachineState',
        state: 'on',
        variables: [{ name: 'weather', value: 'sunny' }],
        trustPrivacy: [{ name: 'on', propertyScope: 'state', mode: 'MachineState', trust: false }],
        privacies: [{ name: 'photo', propertyScope: 'content', privacy: 'private' }]
      }],
      envVariables: [{ name: 'weather', value: 'sunny' }]
    }]
    const canonicalSnapshot = structuredClone(savedStates)
    const translations: Record<string, string> = {
      MachineState: '设备状态',
      on: '开启',
      weather: '天气',
      sunny: '晴朗',
      photo: '照片'
    }
    const formatToken = (_device: SimulationState['devices'][number], value: unknown) =>
      translations[String(value)] || String(value ?? '')
    const formatEnvironmentToken = (_name: string, value: unknown) =>
      translations[String(value)] || String(value ?? '')

    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        states: savedStates,
        currentDeviceIds: ['camera_1'],
        formatDeviceModelToken: formatToken,
        formatEnvironmentModelToken: formatEnvironmentToken
      },
      global: { plugins: [i18n] }
    })

    const devices = wrapper.get('[data-testid="simulation-timeline-devices"]')
    expect(devices.text()).toContain('开启')
    expect(devices.text()).toContain('设备状态')
    expect(devices.text()).toContain('天气=晴朗')
    expect(devices.find('[title="Untrusted source labels: 设备状态: 开启"]').exists()).toBe(true)
    expect(devices.find('[title="Private-data labels: 照片"]').exists()).toBe(true)
    expect(wrapper.get('[data-testid="simulation-timeline-env"]').text()).toContain('天气晴朗')
    expect(savedStates).toEqual(canonicalSnapshot)
  })

  it('names a compromised automation link without exposing its generated index', () => {
    const wrapper = mount(SimulationTimeline, {
      props: {
        visible: true,
        currentRuleIds: ['rule-1'],
        states: [{
          stateIndex: 1,
          triggeredRules: [],
          compromisedAutomationLinks: [{ ruleId: 'rule-1', ruleLabel: 'Hall motion turns on light' }],
          devices: []
        }]
      },
      global: { plugins: [i18n] }
    })

    const links = wrapper.get('[data-testid="simulation-timeline-compromised-links"]')
    expect(links.text()).toContain('Hall motion turns on light')
    expect(links.text()).not.toContain('iot_verify_automation_link_compromised_0')
  })
})
