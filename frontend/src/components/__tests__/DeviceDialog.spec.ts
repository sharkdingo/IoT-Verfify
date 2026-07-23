import { mount } from '@vue/test-utils'
import { afterEach, describe, expect, it } from 'vitest'

import DeviceDialog from '@/components/DeviceDialog.vue'
import { i18n } from '@/assets/i18n'
import type { DeviceManifest, DeviceTemplate } from '@/types/device'

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
    expect(document.querySelector('.device-dialog-header')?.classList).toContain('px-4')
    expect(document.querySelector('.device-dialog-body')?.classList).toContain('px-4')
    expect(document.querySelector('.device-dialog-footer')?.classList).toContain('flex-col')
    expect(renameButton?.classList).toContain('w-full')
    renameButton?.click()
    expect(wrapper.emitted('rename')).toHaveLength(1)

    wrapper.unmount()
  })

  it('localizes bundled model tokens but preserves tokens from custom or unresolved templates', () => {
    i18n.global.locale.value = 'zh-CN'
    const manifest: DeviceManifest = {
      Name: 'Camera',
      Modes: ['SwitchState'],
      InitState: 'off',
      WorkingStates: [
        { Name: 'off', Trust: 'trusted', Privacy: 'public' },
        { Name: 'on', Trust: 'trusted', Privacy: 'public' }
      ],
      APIs: [{
        Name: 'take photo',
        StartState: 'on',
        EndState: 'on',
        Trigger: null,
        Signal: true
      }]
    }
    const node = {
      id: 'camera-1',
      templateName: 'Camera',
      label: 'Camera',
      position: { x: 0, y: 0 },
      state: 'retired-by-template-upgrade',
      width: 176,
      height: 128
    }
    const mountDialog = (deviceTemplates: DeviceTemplate[]) => mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: 'Camera',
        description: '',
        label: 'Camera',
        nodeId: 'camera-1',
        manifest,
        nodes: [node],
        deviceTemplates,
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const bundled = mountDialog([{ name: 'Camera', manifest, defaultTemplate: true }])
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('拍照')
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('开启')
    expect(document.querySelector('[data-testid="device-dialog-states"]')?.textContent).toContain('关闭')
    expect(document.body.textContent).toContain('开关状态')
    expect((document.querySelector('[data-testid="device-runtime-state"]') as HTMLSelectElement | null)?.value)
      .toBe('off')
    bundled.unmount()

    const custom = mountDialog([{ name: 'Camera', manifest, defaultTemplate: false }])
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('take photo')
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('on')
    expect(document.querySelector('[data-testid="device-dialog-states"]')?.textContent).toContain('off')
    expect(document.body.textContent).toContain('SwitchState')
    custom.unmount()

    const missingProvenance = mountDialog([{ name: 'Camera', manifest }])
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('take photo')
    expect(document.querySelector('[data-testid="device-dialog-states"]')?.textContent).toContain('off')
    expect(document.body.textContent).toContain('SwitchState')
    missingProvenance.unmount()

    const unresolved = mountDialog([])
    expect(document.querySelector('[data-testid="device-dialog-apis"]')?.textContent).toContain('take photo')
    unresolved.unmount()
  })

  it('preserves an edited runtime draft across board refreshes and reloads it after reopening', async () => {
    const manifest: DeviceManifest = {
      Name: 'Custom Controller',
      Modes: ['CustomMode'],
      InitState: 'idle',
      WorkingStates: [
        { Name: 'idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'active', Trust: 'trusted', Privacy: 'public' }
      ],
      InternalVariables: [{
        Name: 'threshold',
        IsInside: true,
        FalsifiableWhenCompromised: false,
        LowerBound: 0,
        UpperBound: 100,
        Trust: 'trusted',
        Privacy: 'public'
      }],
      APIs: []
    }
    const template: DeviceTemplate = {
      name: 'Custom Controller',
      manifest,
      defaultTemplate: false
    }
    const node = {
      id: 'controller-1',
      templateName: template.name,
      label: 'Controller',
      position: { x: 0, y: 0 },
      state: 'idle',
      width: 176,
      height: 128,
      variables: [{ name: 'threshold', value: '10' }]
    }
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: template.name,
        description: '',
        label: node.label,
        nodeId: node.id,
        manifest,
        nodes: [node],
        deviceTemplates: [template],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const input = () => document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-threshold"]'
    )
    expect(input()?.value).toBe('10')
    input()!.value = '25'
    input()!.dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()

    const refreshedNode = {
      ...node,
      variables: [{ name: 'threshold', value: '15' }]
    }
    await wrapper.setProps({ nodes: [refreshedNode] })
    expect(input()?.value).toBe('25')

    await wrapper.setProps({ visible: false })
    await wrapper.setProps({ visible: true })
    expect(input()?.value).toBe('15')

    const latestNode = {
      ...refreshedNode,
      variables: [{ name: 'threshold', value: '18' }]
    }
    await wrapper.setProps({ nodes: [latestNode] })
    expect(input()?.value).toBe('18')

    wrapper.unmount()
  })
})
