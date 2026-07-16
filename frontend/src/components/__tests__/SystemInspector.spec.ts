// @vitest-environment jsdom
import { mount } from '@vue/test-utils'
import { beforeEach, describe, expect, it } from 'vitest'
import SystemInspector from '../SystemInspector.vue'
import { i18n } from '@/assets/i18n'
import type { DeviceNode } from '@/types/node'
import type { RuleForm } from '@/types/rule'

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
})
