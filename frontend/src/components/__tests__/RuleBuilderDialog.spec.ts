// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { createI18n } from 'vue-i18n'
import { describe, expect, it, vi } from 'vitest'
import RuleBuilderDialog from '../RuleBuilderDialog.vue'
import type { DeviceNode } from '@/types/node'

vi.mock('@/api/board', () => ({
  default: {
    checkDuplicateRule: vi.fn(),
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
        completeContentPayloadFields: 'Complete payload',
        close: 'Close'
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

describe('RuleBuilderDialog action semantics', () => {
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
})
