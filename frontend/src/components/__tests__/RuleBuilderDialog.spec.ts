// @vitest-environment jsdom
import { flushPromises, mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it, vi } from 'vitest'
import RuleBuilderDialog from '../RuleBuilderDialog.vue'
import type { DeviceNode } from '@/types/node'

vi.mock('@/api/board', () => ({
  default: {
    checkDuplicateRule: vi.fn().mockResolvedValue({ isDuplicate: false, requiresReview: false }),
    checkRuleSimilarity: vi.fn()
  }
}))

const i18n = createI18n({
  legacy: false,
  locale: 'en',
  messages: {
    en: {
      app: {
        api: 'API',
        actionEvent: 'Action Event',
        action: 'Action',
        variable: 'Variable',
        internalVariable: 'Internal variable',
        environmentVariable: 'Environment variable',
        modes: 'Modes',
        state: 'State',
        none: 'None',
        selectPlaceholder: 'Select',
        selectDevicePlaceholder: 'Select device',
        selectAction: 'Select action',
        type: 'Type',
        device: 'Device',
        condition: 'Condition',
        value: 'Value',
        relationEquals: 'equals',
        relationNotEquals: 'not equals',
        relationGreater: 'greater than',
        relationLess: 'less than',
        relationGreaterEqual: 'at least',
        relationLessEqual: 'at most',
        relationIn: 'in',
        relationNotIn: 'not in',
        ifTrigger: 'IF',
        sourceDevices: 'Trigger sources',
        ruleLogicHint: 'AND logic',
        thenAction: 'THEN',
        targetDevice: 'Target device',
        addSource: 'Add source',
        ruleName: 'Rule name',
        ruleNamePlaceholder: 'Name',
        createNewRule: 'Create rule',
        cancel: 'Cancel',
        createRule: 'Create',
        saving: 'Saving',
        checkingAiSimilarity: 'Checking',
        aiSimilarityCheck: 'Check similarity',
        rulePreview: 'Preview',
        anyValue: 'Any',
        and: 'AND',
        unknown: 'Unknown',
        triggers: 'triggers',
        ifThenDescription: 'IF {source} THEN {target} {action}',
        contentPayload: 'Content payload',
        contentPayloadHint: 'Optional',
        acceptsContentSensitivity: 'Accepts content sensitivity',
        noContentPayload: 'None',
        contentSourceDevice: 'Source',
        contentItem: 'Item',
        selectContentDeviceFirst: 'Select source',
        selectContent: 'Select content',
        contentItemWithSensitivity: '{name}',
        completeRequiredFields: 'Complete fields',
        completeRequiredFieldsBeforeDuplicateCheck: 'Complete fields',
        configureRuleSourceBeforeSubmit: 'Configure and add at least one IF condition.',
        addConfiguredRuleSourceBeforeSubmit: 'Add the configured IF condition to the rule before continuing.',
        selectRuleTargetBeforeSubmit: 'Select the THEN target device and action.',
        completeContentPayloadFields: 'Complete payload',
        close: 'Close',
        modelTokens: {
          lock: 'Lock device',
          mode: 'Operating mode',
          switchState: 'Switch status',
          photo: 'Photo item',
          content: 'Content item',
          on: 'Enabled',
          off: 'Disabled'
        }
      }
    }
  },
  missingWarn: false,
  fallbackWarn: false
})

const nodes: DeviceNode[] = [
  { id: 'source', label: 'Hall light', templateName: 'Light', position: { x: 0, y: 0 }, state: 'idle', width: 176, height: 128 },
  { id: 'target', label: 'Bedroom light', templateName: 'Light', position: { x: 220, y: 0 }, state: 'off', width: 176, height: 128 }
]

const template = {
  name: 'Light',
  manifest: {
    Name: 'Light',
    APIs: [
      { Name: 'turn_on', Signal: true, AcceptsContent: true },
      { Name: 'turn_off', Signal: false }
    ],
    InternalVariables: [],
    Modes: [],
    WorkingStates: [],
    Contents: [{ Name: 'photo', Privacy: 'private' }]
  }
}

const localizedTemplate = {
  name: 'Switch',
  defaultTemplate: true,
  manifest: {
    Name: 'Switch',
    APIs: [{ Name: 'lock', Signal: true, AcceptsContent: true }],
    InternalVariables: [{ Name: 'SwitchState', IsInside: true, Values: ['on', 'off'] }],
    Modes: ['Mode'],
    WorkingStates: [{ Name: 'off' }],
    Contents: [{ Name: 'photo', Privacy: 'private' as const }]
  }
}

const customCollisionTemplate = {
  ...localizedTemplate,
  name: 'CustomSwitch',
  defaultTemplate: false,
  manifest: {
    ...localizedTemplate.manifest,
    Name: 'CustomSwitch'
  }
}

const localizedNodes: DeviceNode[] = [
  { id: 'localized-source', label: 'Built-in source', templateName: 'Switch', position: { x: 0, y: 0 }, state: 'off', width: 176, height: 128 },
  { id: 'localized-target', label: 'Built-in target', templateName: 'Switch', position: { x: 220, y: 0 }, state: 'off', width: 176, height: 128 }
]

const customCollisionNodes: DeviceNode[] = [
  { id: 'custom-source', label: 'Custom source', templateName: 'CustomSwitch', position: { x: 0, y: 0 }, state: 'off', width: 176, height: 128 },
  { id: 'custom-target', label: 'Custom target', templateName: 'CustomSwitch', position: { x: 220, y: 0 }, state: 'off', width: 176, height: 128 }
]

describe('RuleBuilderDialog action semantics', () => {
  it('localizes bundled model tokens for display while submitting canonical rule values', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes: localizedNodes, deviceTemplates: [localizedTemplate] },
      global: { plugins: [i18n] }
    })

    await wrapper.get('#rule-source-device').setValue('localized-source')

    await wrapper.get('#rule-source-type').setValue('mode')
    const modeOption = wrapper.get('#rule-source-mode').get('option[value="Mode"]')
    expect(modeOption.text()).toBe('Operating mode')
    expect(modeOption.attributes('value')).toBe('Mode')
    await wrapper.get('#rule-source-mode').setValue('Mode')
    expect(wrapper.get('#rule-source-value').get('option[value="off"]').text()).toBe('Disabled')

    await wrapper.get('#rule-source-type').setValue('state')
    expect(wrapper.get('#rule-source-value').get('option[value="off"]').text()).toBe('Disabled')

    await wrapper.get('#rule-source-type').setValue('variable')
    const variableOption = wrapper.get('#rule-source-variable').get('option[value="SwitchState"]')
    expect(variableOption.text()).toBe('Switch status (Internal variable)')
    expect(variableOption.attributes('value')).toBe('SwitchState')
    await wrapper.get('#rule-source-variable').setValue('SwitchState')
    const valueOption = wrapper.get('#rule-source-value').get('option[value="on"]')
    expect(valueOption.text()).toBe('Enabled')
    expect(valueOption.attributes('value')).toBe('on')
    await wrapper.get('#rule-source-value').setValue('on')
    await wrapper.get('[data-testid="rule-add-source"]').trigger('click')

    await wrapper.get('#rule-target-device').setValue('localized-target')
    const actionOption = wrapper.get('#rule-target-action').get('option[value="lock"]')
    expect(actionOption.text()).toBe('Lock device')
    expect(actionOption.attributes('value')).toBe('lock')
    await wrapper.get('#rule-target-action').setValue('lock')
    await wrapper.get('[data-testid="rule-content-device"]').setValue('localized-source')
    const contentOption = wrapper.get('[data-testid="rule-content-name"] option[value="photo"]')
    expect(contentOption.text()).toBe('Photo item')
    expect(contentOption.attributes('value')).toBe('photo')
    await wrapper.get('[data-testid="rule-content-name"]').setValue('photo')
    expect(wrapper.text()).toContain('Built-in source.Photo item')
    await wrapper.get('[data-testid="rule-save"]').trigger('click')
    await flushPromises()

    const saveRequest = wrapper.emitted('save-rule')?.[0]?.[0] as any
    expect(saveRequest.rule.sources[0]).toMatchObject({
      fromApi: 'SwitchState',
      value: 'on'
    })
    expect(saveRequest.rule.toApi).toBe('lock')
    expect(saveRequest.rule.contentDevice).toBe('localized-source')
    expect(saveRequest.rule.content).toBe('photo')
    saveRequest.complete(true)
  })

  it('keeps colliding custom-template tokens unchanged in every rule selector', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes: customCollisionNodes, deviceTemplates: [customCollisionTemplate] },
      global: { plugins: [i18n] }
    })

    await wrapper.get('#rule-source-device').setValue('custom-source')
    await wrapper.get('#rule-source-type').setValue('mode')
    expect(wrapper.get('#rule-source-mode').get('option[value="Mode"]').text()).toBe('Mode')
    await wrapper.get('#rule-source-mode').setValue('Mode')
    expect(wrapper.get('#rule-source-value').get('option[value="off"]').text()).toBe('off')

    await wrapper.get('#rule-source-type').setValue('variable')
    expect(wrapper.get('#rule-source-variable').get('option[value="SwitchState"]').text())
      .toBe('SwitchState (Internal variable)')
    await wrapper.get('#rule-source-variable').setValue('SwitchState')
    expect(wrapper.get('#rule-source-value').get('option[value="on"]').text()).toBe('on')

    await wrapper.get('#rule-target-device').setValue('custom-target')
    expect(wrapper.get('#rule-target-action').get('option[value="lock"]').text()).toBe('lock')
    await wrapper.get('#rule-target-action').setValue('lock')
    await wrapper.get('[data-testid="rule-content-device"]').setValue('custom-source')
    const contentOption = wrapper.get('[data-testid="rule-content-name"] option[value="photo"]')
    expect(contentOption.text()).toBe('photo')
    expect(contentOption.attributes('value')).toBe('photo')
  })

  it('offers only observable action events as IF sources while keeping all actions available for THEN', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes, deviceTemplates: [template] },
      global: { plugins: [i18n] }
    })

    await wrapper.get('#rule-source-device').setValue('source')
    expect(wrapper.get('#rule-source-type').text()).toContain('Action Event')
    await wrapper.get('#rule-source-type').setValue('api')
    const eventValues = wrapper.get('#rule-source-api').findAll('option').map(option => option.attributes('value'))
    expect(eventValues).toContain('turn_on')
    expect(eventValues).not.toContain('turn_off')

    await wrapper.get('#rule-target-device').setValue('target')
    const actionValues = wrapper.get('#rule-target-action').findAll('option').map(option => option.attributes('value'))
    expect(actionValues).toContain('turn_on')
    expect(actionValues).toContain('turn_off')
  })

  it('offers content sensitivity only for an action that declares it can carry content', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes, deviceTemplates: [template] },
      global: { plugins: [i18n] }
    })

    await wrapper.get('#rule-target-device').setValue('target')
    await wrapper.get('#rule-target-action').setValue('turn_off')
    expect(wrapper.find('#rule-content-device').exists()).toBe(false)

    await wrapper.get('#rule-target-action').setValue('turn_on')
    expect(wrapper.find('#rule-content-device').exists()).toBe(true)
  })

  it('keeps rule actions disabled until the configured IF condition is explicitly added', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes, deviceTemplates: [template] },
      global: { plugins: [i18n] }
    })

    const saveButton = wrapper.get('[data-testid="rule-save"]')
    const similarityButton = wrapper.get('[data-testid="rule-check-duplicate"]')
    expect((saveButton.element as HTMLButtonElement).disabled).toBe(true)
    expect((similarityButton.element as HTMLButtonElement).disabled).toBe(true)
    expect(wrapper.get('[data-testid="rule-draft-readiness"]').text())
      .toBe('Configure and add at least one IF condition.')

    await wrapper.get('#rule-source-device').setValue('source')
    await wrapper.get('#rule-source-type').setValue('api')
    await wrapper.get('#rule-source-api').setValue('turn_on')
    await wrapper.get('#rule-target-device').setValue('target')
    await wrapper.get('#rule-target-action').setValue('turn_off')

    expect((saveButton.element as HTMLButtonElement).disabled).toBe(true)
    expect((similarityButton.element as HTMLButtonElement).disabled).toBe(true)
    expect(wrapper.get('[data-testid="rule-draft-readiness"]').text())
      .toBe('Add the configured IF condition to the rule before continuing.')

    await wrapper.get('[data-testid="rule-add-source"]').trigger('click')

    expect((saveButton.element as HTMLButtonElement).disabled).toBe(false)
    expect((similarityButton.element as HTMLButtonElement).disabled).toBe(false)
    expect(wrapper.find('[data-testid="rule-draft-readiness"]').exists()).toBe(false)
  })

  it('explains missing THEN and partial content payload fields before enabling rule actions', async () => {
    const wrapper = mount(RuleBuilderDialog, {
      props: { modelValue: true, nodes, deviceTemplates: [template] },
      global: { plugins: [i18n] }
    })

    await wrapper.get('#rule-source-device').setValue('source')
    await wrapper.get('#rule-source-type').setValue('api')
    await wrapper.get('#rule-source-api').setValue('turn_on')
    await wrapper.get('[data-testid="rule-add-source"]').trigger('click')

    const saveButton = wrapper.get('[data-testid="rule-save"]')
    expect((saveButton.element as HTMLButtonElement).disabled).toBe(true)
    expect(wrapper.get('[data-testid="rule-draft-readiness"]').text())
      .toBe('Select the THEN target device and action.')

    await wrapper.get('#rule-target-device').setValue('target')
    await wrapper.get('#rule-target-action').setValue('turn_on')
    await wrapper.get('[data-testid="rule-content-device"]').setValue('source')

    expect((saveButton.element as HTMLButtonElement).disabled).toBe(true)
    expect(wrapper.get('[data-testid="rule-draft-readiness"]').text()).toBe('Complete payload')

    await wrapper.get('[data-testid="rule-content-name"]').setValue('photo')

    expect((saveButton.element as HTMLButtonElement).disabled).toBe(false)
    expect(wrapper.find('[data-testid="rule-draft-readiness"]').exists()).toBe(false)
  })
})
