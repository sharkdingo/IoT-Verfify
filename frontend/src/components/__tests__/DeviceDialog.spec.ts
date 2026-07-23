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
    expect(renameButton?.classList).toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-delete"]')?.classList).toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-dialog-footer-close"]')?.classList)
      .toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-dialog-close"]')?.classList)
      .toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-dialog-close"]')?.classList)
      .toContain('min-w-11')
    renameButton?.click()
    expect(wrapper.emitted('rename')).toHaveLength(1)

    wrapper.unmount()
  })

  it('uses reachable dedicated icons for doors and garage doors', async () => {
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: 'Garage Door',
        description: '',
        label: 'Garage Door',
        nodeId: 'garage-1',
        manifest: null,
        nodes: [],
        deviceTemplates: [],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const headerIcon = () => document.querySelector(
      '.device-dialog-header .material-icons-round'
    )?.textContent?.trim()
    expect(headerIcon()).toBe('garage')

    await wrapper.setProps({ deviceName: 'Door', label: 'Front Door' })
    expect(headerIcon()).toBe('door_front_door')

    await wrapper.setProps({ deviceName: 'Door Sensor', label: 'Entry Sensor' })
    expect(headerIcon()).toBe('sensors')
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

  it('merges disjoint refreshes and requires an explicit choice for conflicting runtime edits', async () => {
    const manifest: DeviceManifest = {
      Name: 'Custom Controller',
      Modes: ['CustomMode'],
      InitState: 'idle',
      WorkingStates: [
        { Name: 'idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'active', Trust: 'trusted', Privacy: 'public' }
      ],
      InternalVariables: [
        {
          Name: 'threshold',
          IsInside: true,
          FalsifiableWhenCompromised: false,
          LowerBound: 0,
          UpperBound: 100,
          Trust: 'trusted',
          Privacy: 'public'
        },
        {
          Name: 'limit',
          IsInside: true,
          FalsifiableWhenCompromised: false,
          LowerBound: 0,
          UpperBound: 100,
          Trust: 'trusted',
          Privacy: 'public'
        }
      ],
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
      variables: [
        { name: 'threshold', value: '10' },
        { name: 'limit', value: '40' }
      ]
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
    const limitInput = () => document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-limit"]'
    )
    expect(input()?.value).toBe('10')
    input()!.value = '25'
    input()!.dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()

    await wrapper.setProps({ suspended: true })
    expect(document.querySelector('[data-testid="device-dialog"]')).toBeNull()
    await wrapper.setProps({ suspended: false })
    expect(input()?.value).toBe('25')

    const disjointRefresh = {
      ...node,
      variables: [
        { name: 'threshold', value: '10' },
        { name: 'limit', value: '50' }
      ]
    }
    await wrapper.setProps({ nodes: [disjointRefresh] })
    expect(input()?.value).toBe('25')
    expect(limitInput()?.value).toBe('50')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).toBeNull()

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')!.click()
    await wrapper.vm.$nextTick()
    expect(wrapper.emitted('save-runtime')?.[0]?.[1]).toMatchObject({
      variables: [
        { name: 'threshold', value: '25' },
        { name: 'limit', value: '50' }
      ]
    })

    const conflictingRefresh = {
      ...disjointRefresh,
      variables: [
        { name: 'threshold', value: '15' },
        { name: 'limit', value: '50' }
      ]
    }
    await wrapper.setProps({ nodes: [conflictingRefresh] })
    expect(input()?.value).toBe('25')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).not.toBeNull()
    expect(document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')?.disabled).toBe(true)
    expect(document.querySelector('[data-testid="device-runtime-save"]')?.classList).toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-runtime-adopt-latest"]')?.classList).toContain('min-h-11')
    expect(document.querySelector('[data-testid="device-runtime-keep-local"]')?.classList).toContain('min-h-11')

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-keep-local"]')!.click()
    await wrapper.vm.$nextTick()
    expect(input()?.value).toBe('25')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).toBeNull()
    expect(document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')?.disabled).toBe(false)

    await wrapper.setProps({ visible: false })
    await wrapper.setProps({ visible: true })
    expect(input()?.value).toBe('15')

    const latestNode = {
      ...conflictingRefresh,
      variables: [
        { name: 'threshold', value: '18' },
        { name: 'limit', value: '50' }
      ]
    }
    input()!.value = '30'
    input()!.dispatchEvent(new Event('input', { bubbles: true }))
    limitInput()!.value = '60'
    limitInput()!.dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()
    await wrapper.setProps({ nodes: [latestNode] })
    expect(input()?.value).toBe('30')
    expect(limitInput()?.value).toBe('60')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).not.toBeNull()

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-adopt-latest"]')!.click()
    await wrapper.vm.$nextTick()
    expect(input()?.value).toBe('18')
    expect(limitInput()?.value).toBe('60')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).toBeNull()

    wrapper.unmount()
  })

  it('does not overwrite an edit that returns to the old value while a save is in flight', async () => {
    const manifest: DeviceManifest = {
      Name: 'Custom Controller',
      Modes: [],
      WorkingStates: [],
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
      name: manifest.Name,
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
    let markSaving: (() => void) | null = null
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        runtimeSaving: false,
        deviceName: template.name,
        description: '',
        label: node.label,
        nodeId: node.id,
        manifest,
        nodes: [node],
        deviceTemplates: [template],
        specs: [],
        onSaveRuntime: () => markSaving?.()
      },
      global: { plugins: [i18n] }
    })
    markSaving = () => {
      void wrapper.setProps({ runtimeSaving: true })
    }
    const input = () => document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-threshold"]'
    )!
    const setInput = async (value: string) => {
      input().value = value
      input().dispatchEvent(new Event('input', { bubbles: true }))
      await wrapper.vm.$nextTick()
    }

    await setInput('25')
    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')!.click()
    await wrapper.vm.$nextTick()
    expect(wrapper.emitted('save-runtime')?.[0]?.[1]).toMatchObject({
      variables: [{ name: 'threshold', value: '25' }]
    })

    await setInput('10')
    await wrapper.setProps({
      nodes: [{ ...node, variables: [{ name: 'threshold', value: '25' }] }],
      runtimeSaving: false
    })

    expect(input().value).toBe('10')

    await wrapper.setProps({
      nodes: [{ ...node, variables: [{ name: 'threshold', value: '25' }] }]
    })
    expect(input().value).toBe('10')
    wrapper.unmount()
  })

  it('resets the runtime edit session when a same-id device changes template schema', async () => {
    const manifestWithVariable = (name: string): DeviceManifest => ({
      Name: `${name} Controller`,
      Modes: [],
      WorkingStates: [],
      InternalVariables: [{
        Name: name,
        IsInside: true,
        FalsifiableWhenCompromised: false,
        LowerBound: 0,
        UpperBound: 100,
        Trust: 'trusted',
        Privacy: 'public'
      }],
      APIs: []
    })
    const originalManifest = manifestWithVariable('alpha')
    const replacementManifest = manifestWithVariable('beta')
    const originalTemplate: DeviceTemplate = {
      name: originalManifest.Name,
      manifest: originalManifest,
      defaultTemplate: false
    }
    const replacementTemplate: DeviceTemplate = {
      name: replacementManifest.Name,
      manifest: replacementManifest,
      defaultTemplate: false
    }
    const originalNode = {
      id: 'controller-1',
      templateName: originalTemplate.name,
      label: 'Controller',
      position: { x: 0, y: 0 },
      state: 'Working',
      width: 176,
      height: 128,
      variables: [{ name: 'alpha', value: '10' }]
    }
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: originalTemplate.name,
        description: '',
        label: originalNode.label,
        nodeId: originalNode.id,
        manifest: originalManifest,
        nodes: [originalNode],
        deviceTemplates: [originalTemplate],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const originalInput = document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-alpha"]'
    )!
    originalInput.value = '25'
    originalInput.dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()

    await wrapper.setProps({
      deviceName: replacementTemplate.name,
      manifest: replacementManifest,
      deviceTemplates: [replacementTemplate],
      nodes: [{
        ...originalNode,
        templateName: replacementTemplate.name,
        variables: [{ name: 'beta', value: '7' }]
      }]
    })

    expect(document.querySelector('[data-testid="device-runtime-variable-alpha"]')).toBeNull()
    expect(document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-beta"]'
    )?.value).toBe('7')
    wrapper.unmount()
  })

  it('disables the delete action while its impact preview is loading', async () => {
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deleteLoading: true,
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

    const deleteButton = document.querySelector<HTMLButtonElement>('[data-testid="device-delete"]')!
    expect(deleteButton.disabled).toBe(true)
    expect(deleteButton.getAttribute('aria-busy')).toBe('true')
    expect(deleteButton.textContent).toContain(i18n.global.t('app.loading'))
    deleteButton.click()
    expect(wrapper.emitted('delete')).toBeUndefined()

    await wrapper.setProps({ deleteLoading: false })
    deleteButton.click()
    expect(wrapper.emitted('delete')).toHaveLength(1)
    wrapper.unmount()
  })
})
