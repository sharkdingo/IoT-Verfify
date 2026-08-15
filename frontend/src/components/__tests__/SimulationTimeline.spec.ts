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
        exit: 'Exit',
        exitTimeline: 'Exit playback and return to the canvas',
        unknown: 'Unknown',
        state: 'State',
        mode: 'Mode',
        ruleNumber: 'Rule {number}',
        runDetails: 'Run details',
        stepChanges: 'Step changes',
        showStepChanges: 'Show the step-changes panel again',
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
          provenance: {
            externalInput: 'external input',
            affectedBy: 'affected by {device}',
            affectedByMultiple: 'affected by {count} devices',
            naturalEvolution: 'natural evolution {rate}'
          },
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
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', modelTokenSource: 'UNKNOWN', state: 'idle', variables: [] }]
  },
  {
    stateIndex: 2,
    triggeredRules: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: `${prefix} activation` }],
    compromisedAutomationLinks: [],
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', modelTokenSource: 'UNKNOWN', state: 'active', variables: [] }]
  },
  {
    stateIndex: 3,
    triggeredRules: [],
    compromisedAutomationLinks: [],
    devices: [{ deviceId: `${prefix}_sensor`, deviceLabel: `${prefix} sensor`, templateName: 'Sensor', modelTokenSource: 'UNKNOWN', state: 'done', variables: [] }]
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
            devices: [{ deviceId: 'sensor_1', deviceLabel: 'Sensor', templateName: 'Sensor', modelTokenSource: 'UNKNOWN', variables: [] }],
            envVariables: [{ name: 'attackBudget', value: '9', modelTokenSource: 'UNKNOWN' }],
            globalVariables: [{ name: 'compromisedPointCount', value: '4', modelTokenSource: 'UNKNOWN' }]
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
            'UNWRITTEN_DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN',
    'DEVICE_WRITTEN_DISCRETE_VALUES_HOLD_WHEN_NO_DECLARED_EFFECT_APPLIES'
          ],
          localVariableFallbackPolicy: 'STUTTER_WHEN_NO_DECLARED_EVOLUTION'
        }
      },
      global: { plugins: [i18n] }
    })

    // Asserted on the help affordance's `text` prop, not on rendered output: these facts moved from a
    // standing disclosure into an `InfoTooltip`, and `ElTooltip` renders its content only once opened,
    // so `wrapper.text()` cannot see prose that is genuinely reachable.
    const helpText = wrapper.findComponent({ name: 'InfoTooltip' }).props('text') as string
    expect(helpText).toContain('Exhaustive up to 2 of 5 points')
    expect(helpText).toContain('Labels propagate only on automation commands')
    expect(helpText).not.toContain('Model semantics unavailable')
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
            devices: [{ deviceId: 'sensor_1', deviceLabel: 'Sensor', templateName: 'Sensor', modelTokenSource: 'UNKNOWN', variables: [] }],
            envVariables: [{ name: 'attackBudget', value: '9', modelTokenSource: 'UNKNOWN' }]
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
          globalVariables: [{ name: 'compromisedPointCount', value: 'unknown', modelTokenSource: 'UNKNOWN' }]
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
    // The frozen-snapshot counts are deliberately NOT here any more: the run-details dialog owns
    // them, and repeating them on an overlay whose subject is the canvas behind it cost permanent
    // height for a fact a reader needs once. What must survive is the help affordance itself —
    // its accessible name, since `ElTooltip` renders the prose only once opened.
    expect(wrapper.get('[data-testid="simulation-timeline-snapshot-notice"]')
      .attributes('aria-label')).toContain('Run Scope')
    expect(wrapper.text(), 'the counts must not return to this surface')
      .not.toContain('3 devices, 2 rules, 0 specs')
    // This surface warns only when the board HAS drifted; the full four-way verdict (including
    // "unchanged") belongs to the run-details dialog, which carries `simulation-board-comparison`.
    // A timeline that also announced "unchanged" would spend permanent height saying nothing happened.
    expect(wrapper.get('[data-testid="simulation-board-drift-warning"]').text())
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
              { deviceId: 'current_sensor', deviceLabel: 'Current sensor', templateName: 'Sensor', modelTokenSource: 'UNKNOWN', state: 'idle', variables: [] },
              { deviceId: 'removed_lock', deviceLabel: 'Removed lock', templateName: 'Lock', modelTokenSource: 'UNKNOWN', state: 'locked', variables: [] }
            ]
          },
          {
            stateIndex: 2,
            triggeredRules: [],
            compromisedAutomationLinks: [],
            devices: [
              { deviceId: 'current_sensor', deviceLabel: 'Current sensor', templateName: 'Sensor', modelTokenSource: 'UNKNOWN', state: 'active', variables: [] },
              {
                deviceId: 'removed_lock',
                deviceLabel: 'Removed lock',
                templateName: 'Lock',
                modelTokenSource: 'UNKNOWN',
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

    // Same reason as above: the read-only sentence now lives in the tooltip's content, which
    // `ElTooltip` does not render until opened. Assert the prop, which is the real contract.
    expect(wrapper.findComponent({ name: 'InfoTooltip' }).props('text') as string)
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
            modelTokenSource: 'UNKNOWN',
            mode: 'CameraMode',
            state: 'recording',
            variables: [{ name: 'motion', value: 'TRUE', trust: 'untrusted', modelTokenSource: 'UNKNOWN' }],
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
        modelTokenSource: 'BUNDLED',
        mode: 'MachineState',
        state: 'on',
        variables: [{ name: 'weather', value: 'sunny', modelTokenSource: 'BUNDLED' }],
        trustPrivacy: [{ name: 'on', propertyScope: 'state', mode: 'MachineState', trust: false }],
        privacies: [{ name: 'photo', propertyScope: 'content', privacy: 'private' }]
      }],
      envVariables: [{ name: 'weather', value: 'sunny', modelTokenSource: 'BUNDLED' }]
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
          compromisedAutomationLinks: [{ ruleIndex: 0, ruleId: 'rule-1', ruleLabel: 'Hall motion turns on light' }],
          devices: []
        }]
      },
      global: { plugins: [i18n] }
    })

    const links = wrapper.get('[data-testid="simulation-timeline-compromised-links"]')
    expect(links.text()).toContain('Hall motion turns on light')
    expect(links.text()).not.toContain('iot_verify_automation_link_compromised_0')
  })

  describe('a changed shared value names the rule that permitted the change', () => {
    // A value that moved with no stated cause is the case a user cannot act on: they cannot tell
    // whether their own rule did it or the model allowed it. So every combination the backend can
    // report must produce a cause, not just the ones that were easy to render first.
    const provenanceStates = (name: string, from: string, to: string): SimulationState[] => [
      {
        stateIndex: 1,
        triggeredRules: [],
        compromisedAutomationLinks: [],
        devices: [],
        envVariables: [{ name, value: from, modelTokenSource: 'BUNDLED' }]
      },
      {
        stateIndex: 2,
        triggeredRules: [],
        compromisedAutomationLinks: [],
        devices: [],
        envVariables: [{ name, value: to, modelTokenSource: 'BUNDLED' }]
      }
    ]

    const titleForChangedValue = async (
      name: string,
      from: string,
      to: string,
      provenance: Record<string, unknown>
    ) => {
      const wrapper = mount(SimulationTimeline, {
        props: {
          visible: true,
          states: provenanceStates(name, from, to),
          modelSnapshot: {
            capturedAt: '2026-08-01T10:00:00',
            deviceCount: 1,
            ruleCount: 0,
            specificationCount: 0,
            environmentVariableCount: 1,
            deviceTemplateCount: 1,
            templatesFrozen: true,
            environmentProvenance: [provenance]
          } as never
        },
        global: { plugins: [i18n] }
      })
      // Index 1 is the second state -- the one that changed. Index 0 has no predecessor, so it
      // deliberately carries no cause annotation.
      await wrapper.get('[data-testid="simulation-timeline-state-1"]').trigger('click')
      return wrapper.get('[data-testid="simulation-timeline-env"]').html()
    }

    it('reports a device when exactly one device declares it writes the value', async () => {
      const html = await titleForChangedValue('illuminance', 'dim', 'bright', {
        name: 'illuminance',
        type: 'DISCRETE_ENUM',
        values: ['dim', 'bright'],
        authorship: 'DEVICE_CONTROLLED',
        semantics: 'EXACT',
        writers: [{ deviceVarName: 'light_1', templateName: 'Light', templateSource: 'BUNDLED' }],
        readers: [],
        evolutionSummary: 'Controlled by device light_1 (Light).'
      })
      expect(html).toContain('affected by light_1')
    })

    it('names the abstraction when nobody writes a discrete value', async () => {
      const html = await titleForChangedValue('weather', 'sunny', 'rainy', {
        name: 'weather',
        type: 'DISCRETE_ENUM',
        values: ['sunny', 'rainy'],
        authorship: 'EXOGENOUS',
        semantics: 'ABSTRACTION',
        writers: [],
        readers: [{ deviceVarName: 'weather_1' }],
        evolutionSummary: 'External input.'
      })
      // The user must be able to tell this apart from a change their scene caused.
      expect(html).toContain('external input')
    })

    it('cites the declared interval when nobody writes a numeric value', async () => {
      // This is the most common shared value in the product -- every bundled sensor declares one --
      // and it fell through every branch, so the trace showed a bare "20 -> 21" with no cause.
      const html = await titleForChangedValue('temperature', '20', '21', {
        name: 'temperature',
        type: 'NUMERIC',
        lowerBound: 0,
        upperBound: 100,
        naturalChangeRate: '[-1, 1]',
        authorship: 'EXOGENOUS',
        semantics: 'EXACT',
        writers: [],
        readers: [{ deviceVarName: 'temp_1' }],
        evolutionSummary: 'External input; natural evolution [-1, 1].'
      })
      expect(html).toContain('natural evolution [-1, 1]')
      // Exact semantics must not be presented as the disclosed over-approximation.
      expect(html).not.toContain('external input')
    })

    it('reports the writer count when several devices write the value', async () => {
      const html = await titleForChangedValue('airQuality', 'poor', 'good', {
        name: 'airQuality',
        type: 'DISCRETE_ENUM',
        values: ['poor', 'good'],
        authorship: 'COMPOSED',
        semantics: 'EXACT',
        writers: [
          { deviceVarName: 'purifier_1', templateName: 'Air Purifier', templateSource: 'BUNDLED' },
          { deviceVarName: 'fan_1', templateName: 'Range Hood', templateSource: 'BUNDLED' }
        ],
        readers: [],
        evolutionSummary: 'Affected by 2 devices: purifier_1, fan_1.'
      })
      expect(html).toContain('affected by 2 devices')
    })
  })

  /**
   * The counterexample rail has this guard in `views/board/actionDockHierarchy.spec.ts` ("shows what
   * caused the selected counterexample step without an extra click"). This rail had none, which is how a
   * change wrapping its whole step-values block in a collapsed `<details>` shipped: the only existing
   * assertion checked that the testid *exists*, and the E2E helper clicks the disclosure open before
   * reading it, so nothing noticed the answer had moved behind a click.
   *
   * Asserted against a mounted DOM rather than the source text, so it covers the rendered ancestry
   * instead of a regex over markup.
   */
  it('does not put the cause of the selected step behind a disclosure', async () => {
    const wrapper = mount(SimulationTimeline, {
      props: { visible: true, states: states('playback') },
      global: { plugins: [i18n] }
    })

    // Past the initial state: there is no rule that produced state 0, so the row renders from step 1 on.
    await wrapper.get('[data-testid="simulation-timeline-state-1"]').trigger('click')

    const cause = wrapper.get('[data-testid="simulation-timeline-triggered-rules"]')
    expect(
      cause.element.closest('details'),
      'the cause of the selected step must not sit inside a <details>'
    ).toBeNull()

    // The value tables keep their disclosure: they are genuinely tall, and the canvas nodes are the
    // richer authority for device values. Removing the disclosure entirely is not the fix.
    const values = wrapper.find('[data-testid="simulation-step-values"]')
    expect(values.exists(), 'the value tables should still be present').toBe(true)
    expect(values.element.tagName.toLowerCase(), 'and should still be a disclosure').toBe('details')
  })
})
