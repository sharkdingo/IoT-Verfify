import { mount } from '@vue/test-utils'
import { afterEach, describe, expect, it } from 'vitest'

import DeviceDialog from '@/components/DeviceDialog.vue'
import { i18n } from '@/assets/i18n'

describe('DeviceDialog template authority', () => {
  afterEach(() => {
    document.body.innerHTML = ''
  })

  it('does not present missing or stale device-type semantics as current details', async () => {
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: 'Thermostat',
        description: '',
        label: 'Hall thermostat',
        nodeId: 'node-1',
        manifest: null,
        nodes: [{
          id: 'node-1',
          templateName: 'Thermostat',
          label: 'Hall thermostat',
          position: { x: 0, y: 0 },
          state: 'heat',
          width: 176,
          height: 128
        }],
        deviceTemplates: [],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    expect(document.querySelector('[data-testid="device-template-details-unavailable"]')?.textContent)
      .toContain('Thermostat')
    expect(document.querySelector('[data-testid="device-dialog-states"]')).toBeNull()
    expect(document.body.textContent).not.toContain('heat')

    wrapper.unmount()
  })

  it('exposes device rename as a visible instance action', () => {
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: 'Light',
        description: '',
        label: 'Hall light',
        nodeId: 'light-1',
        manifest: null,
        nodes: [],
        deviceTemplates: [],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const renameButton = document.querySelector<HTMLButtonElement>('[data-testid="device-rename"]')
    expect(renameButton).not.toBeNull()
    renameButton?.click()
    expect(wrapper.emitted('rename')).toHaveLength(1)

    wrapper.unmount()
  })
})
