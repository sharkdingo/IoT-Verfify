// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { beforeEach, describe, expect, it } from 'vitest'
import SystemInspector from '../SystemInspector.vue'
import { i18n } from '@/assets/i18n'
import type { DeviceNode } from '@/types/node'
import type { DeviceTemplate } from '@/types/device'
import type { RuleForm } from '@/types/rule'
import type { Specification } from '@/types/spec'

const devices: DeviceNode[] = [
  {
    id: 'sensor-1',
    label: 'Hall sensor',
    templateName: 'Sensor',
    position: { x: 0, y: 0 },
    state: 'Working',
    width: 176,
    height: 128
  },
  {
    id: 'light-1',
    label: 'Hall light',
    templateName: 'Light',
    position: { x: 200, y: 0 },
    state: 'off',
    width: 176,
    height: 128
  }
]

const rule = (id: string, name: string, action: string): RuleForm => ({
  id,
  name,
  sources: [{
    fromId: 'sensor-1',
    fromApi: 'motion',
    itemType: 'variable',
    relation: '=',
    value: 'detected'
  }],
  toId: 'light-1',
  toApi: action
})

describe('SystemInspector rule execution order', () => {
  beforeEach(() => {
    i18n.global.locale.value = 'en'
  })

  it('shows first-match semantics and emits an explicit complete-order move intent', async () => {
    const wrapper = mount(SystemInspector, {
      props: {
        activeSection: 'rules',
        devices,
        rules: [rule('1', 'Turn off first', 'off'), rule('2', 'Turn on second', 'on')]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-testid="rule-execution-order-hint"]').text())
      .toContain('first matching rule')
    expect(wrapper.text()).toContain('#1')
    expect(wrapper.text()).toContain('#2')
    expect(wrapper.get('[data-rule-id="1"]').attributes('tabindex')).toBe('-1')

    const moveEarlierButtons = wrapper.findAll('button[aria-label="Move earlier"]')
    expect(moveEarlierButtons).toHaveLength(2)
    expect(moveEarlierButtons[0].attributes('disabled')).toBeDefined()
    await moveEarlierButtons[1].trigger('click')

    expect(wrapper.emitted('move-rule')).toEqual([['2', 'up']])
  })

  it('lets keyboard users focus and select a device while revealing its action', async () => {
    const wrapper = mount(SystemInspector, {
      props: {
        activeSection: 'devices',
        devices,
        rules: []
      },
      global: { plugins: [i18n] }
    })

    const device = wrapper.get('[data-device-id="sensor-1"]')
    const openButton = device.get('button[aria-label="Hall sensor"]')
    expect(openButton.element.tagName).toBe('BUTTON')
    expect(openButton.attributes('type')).toBe('button')
    await openButton.trigger('click')
    expect(wrapper.emitted('device-click')).toEqual([['sensor-1']])

    const deleteButton = device.get('button[aria-label="Remove device"]')
    expect(deleteButton.classes()).toContain('group-focus-within:opacity-100')
  })

  it('implements roving tab focus and links each tab to its panel', async () => {
    const wrapper = mount(SystemInspector, {
      attachTo: document.body,
      props: { activeSection: 'devices', devices, rules: [] },
      global: { plugins: [i18n] }
    })

    const devicesTab = wrapper.get('[data-testid="inspector-tab-devices"]')
    const rulesTab = wrapper.get('[data-testid="inspector-tab-rules"]')
    expect(devicesTab.attributes('tabindex')).toBe('0')
    expect(rulesTab.attributes('tabindex')).toBe('-1')
    expect(devicesTab.attributes('aria-controls')).toBe('inspector-panel-devices')
    expect(wrapper.get('#inspector-panel-devices').attributes('aria-labelledby'))
      .toBe('inspector-tab-devices')

    ;(devicesTab.element as HTMLElement).focus()
    await devicesTab.trigger('keydown', { key: 'ArrowRight' })
    expect(document.activeElement).toBe(rulesTab.element)
    expect(wrapper.emitted('update:active-section')?.at(-1)).toEqual(['rules'])

    await wrapper.setProps({ activeSection: 'rules' })
    expect(wrapper.get('[data-testid="inspector-tab-rules"]').attributes('tabindex')).toBe('0')
    expect(wrapper.get('#inspector-panel-rules').attributes('role')).toBe('tabpanel')
    await wrapper.get('[data-testid="inspector-tab-rules"]').trigger('keydown', { key: 'ArrowLeft' })
    expect(document.activeElement).toBe(wrapper.get('[data-testid="inspector-tab-devices"]').element)
    expect(wrapper.emitted('update:active-section')?.at(-1)).toEqual(['devices'])

    await wrapper.setProps({ activeSection: 'devices' })
    await wrapper.get('[data-testid="inspector-tab-devices"]').trigger('keydown', { key: 'End' })
    expect(document.activeElement).toBe(wrapper.get('[data-testid="inspector-tab-specs"]').element)
    expect(wrapper.emitted('update:active-section')?.at(-1)).toEqual(['specs'])

    await wrapper.setProps({ activeSection: 'specs' })
    await wrapper.get('[data-testid="inspector-tab-specs"]').trigger('keydown', { key: 'Home' })
    expect(document.activeElement).toBe(wrapper.get('[data-testid="inspector-tab-devices"]').element)
    expect(wrapper.emitted('update:active-section')?.at(-1)).toEqual(['devices'])
    wrapper.unmount()
  })

  it('localizes bundled model tokens while preserving canonical edit values and custom states', async () => {
    i18n.global.locale.value = 'zh-CN'
    const bundledTemplate: DeviceTemplate = {
      name: 'Light',
      defaultTemplate: true,
      manifest: {
        Name: 'Light',
        Modes: ['SwitchState'],
        InitState: 'off',
        WorkingStates: [
          { Name: 'off', Trust: 'trusted', Privacy: 'public' },
          { Name: 'on', Trust: 'trusted', Privacy: 'public' }
        ],
        InternalVariables: [{
          Name: 'temperature',
          IsInside: false,
          FalsifiableWhenCompromised: false,
          Trust: 'trusted',
          Privacy: 'public',
          Values: ['off', 'on']
        }]
      }
    }
    const customTemplate: DeviceTemplate = {
      name: 'Custom device',
      defaultTemplate: false,
      manifest: {
        Name: 'Custom device',
        Modes: ['CustomMode'],
        InitState: 'ecoBoost',
        WorkingStates: [{ Name: 'ecoBoost', Trust: 'trusted', Privacy: 'public' }]
      }
    }
    const wrapper = mount(SystemInspector, {
      props: {
        activeSection: 'devices',
        deviceTemplates: [bundledTemplate, customTemplate],
        devices: [
          { ...devices[1], templateName: 'Light', state: 'off' },
          { ...devices[0], id: 'custom-1', label: 'Custom', templateName: 'Custom device', state: 'ecoBoost' }
        ],
        environmentVariables: [{ name: 'temperature', value: 'off' }]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.text()).toContain('关闭')
    expect(wrapper.text()).toContain('ecoBoost')
    expect(wrapper.text()).toContain('温度')
    await wrapper.get('[data-testid="toggle-environment-pool"]').trigger('click')
    await wrapper.get('article button').trigger('click')
    const valueSelect = wrapper.get('[data-testid="environment-value-temperature"]')
    expect(valueSelect.find('option[value="off"]').text()).toBe('关闭')
    await valueSelect.setValue('on')
    expect(wrapper.emitted('save-environment')?.at(-1)).toEqual([[
      { name: 'temperature', value: 'on' }
    ]])
  })

  it('localizes the synthetic lowercase state field in bundled rule summaries', () => {
    i18n.global.locale.value = 'zh-CN'
    const bundledTemplate: DeviceTemplate = {
      name: 'Light',
      defaultTemplate: true,
      manifest: {
        Name: 'Light',
        Modes: ['SwitchState'],
        InitState: 'off',
        WorkingStates: [
          { Name: 'off', Trust: 'trusted', Privacy: 'public' },
          { Name: 'on', Trust: 'trusted', Privacy: 'public' }
        ]
      }
    }
    const stateRule: RuleForm = {
      id: 'state-rule',
      name: 'State rule',
      sources: [{
        fromId: 'light-1',
        fromApi: 'state',
        itemType: 'state',
        relation: '=',
        value: 'off'
      }],
      toId: 'light-1',
      toApi: 'on'
    }
    const wrapper = mount(SystemInspector, {
      props: {
        activeSection: 'rules',
        deviceTemplates: [bundledTemplate],
        devices: [{ ...devices[1], templateName: 'Light', state: 'off' }],
        rules: [stateRule]
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-rule-id="state-rule"]').text()).toContain('状态 = 关闭')
    expect(stateRule.sources[0]).toMatchObject({ fromApi: 'state', value: 'off' })
  })

  it('preserves shared environment tokens when any provider is a custom template', async () => {
    i18n.global.locale.value = 'zh-CN'
    const environmentDefinition = {
      Name: 'temperature',
      IsInside: false,
      FalsifiableWhenCompromised: false,
      Trust: 'trusted',
      Privacy: 'public',
      Values: ['off', 'on']
    }
    const bundledTemplate: DeviceTemplate = {
      name: 'Light',
      defaultTemplate: true,
      manifest: {
        Name: 'Light',
        Modes: ['SwitchState'],
        InitState: 'off',
        WorkingStates: [{ Name: 'off', Trust: 'trusted', Privacy: 'public' }],
        InternalVariables: [environmentDefinition]
      }
    }
    const customTemplate: DeviceTemplate = {
      name: 'Custom provider',
      defaultTemplate: false,
      manifest: {
        Name: 'Custom provider',
        Modes: ['CustomMode'],
        InitState: 'off',
        WorkingStates: [{ Name: 'off', Trust: 'trusted', Privacy: 'public' }],
        InternalVariables: [environmentDefinition]
      }
    }
    const wrapper = mount(SystemInspector, {
      props: {
        activeSection: 'devices',
        deviceTemplates: [bundledTemplate, customTemplate],
        devices: [
          { ...devices[1], templateName: 'Light' },
          { ...devices[0], id: 'custom-provider', templateName: 'Custom provider' }
        ],
        environmentVariables: [{ name: 'temperature', value: 'off' }]
      },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-testid="toggle-environment-pool"]').trigger('click')
    expect(wrapper.get('[data-testid="environment-pool"]').text()).toContain('temperature')
    await wrapper.get('article button').trigger('click')
    const valueSelect = wrapper.get('[data-testid="environment-value-temperature"]')
    expect(valueSelect.find('option[value="off"]').text()).toBe('off')
    expect(valueSelect.find('option[value="on"]').text()).toBe('on')
  })

  it('does not add a dead tab stop to a specification card', () => {
    const specification: Specification = {
      id: 'spec-1',
      templateId: '1',
      templateLabel: 'Always',
      aConditions: [],
      ifConditions: [],
      thenConditions: []
    }
    const wrapper = mount(SystemInspector, {
      props: { activeSection: 'specs', devices, specifications: [specification] },
      global: { plugins: [i18n] }
    })

    expect(wrapper.get('[data-spec-id="spec-1"]').attributes('tabindex')).toBe('-1')
    expect(wrapper.get('[data-spec-id="spec-1"] button').attributes('aria-label')).toBeTruthy()
  })
})
