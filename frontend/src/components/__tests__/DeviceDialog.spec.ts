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

  it('keeps state, trust, and privacy together when a snapshot races a local edit', async () => {
    const manifest: DeviceManifest = {
      Name: 'Stateful Controller',
      Modes: ['OperatingMode'],
      InitState: 'idle',
      WorkingStates: [
        { Name: 'idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'active', Trust: 'untrusted', Privacy: 'private' }
      ],
      APIs: []
    }
    const template: DeviceTemplate = {
      name: manifest.Name,
      manifest,
      defaultTemplate: false
    }
    const node = {
      id: 'stateful-1',
      templateName: template.name,
      label: 'Stateful controller',
      position: { x: 0, y: 0 },
      state: 'idle',
      currentStateTrust: 'trusted',
      currentStatePrivacy: 'public',
      width: 176,
      height: 128
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

    const state = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state"]')!
    const trust = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state-trust"]')!
    const privacy = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state-privacy"]')!

    trust().value = 'untrusted'
    trust().dispatchEvent(new Event('change', { bubbles: true }))
    await wrapper.vm.$nextTick()

    await wrapper.setProps({
      nodes: [{
        ...node,
        state: 'active',
        currentStateTrust: 'untrusted',
        currentStatePrivacy: 'private'
      }]
    })

    expect(state().value).toBe('idle')
    expect(trust().value).toBe('untrusted')
    expect(privacy().value).toBe('public')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).not.toBeNull()
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')?.textContent)
      .toContain(i18n.global.t('app.deviceRuntimeConflict', { count: 1 }))
    const adoptLatest = document.querySelector<HTMLButtonElement>(
      '[data-testid="device-runtime-adopt-latest"]'
    )!
    expect(adoptLatest.classList).toContain('device-runtime-adopt-latest')

    adoptLatest.click()
    await wrapper.vm.$nextTick()
    expect(state().value).toBe('active')
    expect(trust().value).toBe('untrusted')
    expect(privacy().value).toBe('private')
    expect(document.querySelector('[data-testid="device-runtime-conflict"]')).toBeNull()
    wrapper.unmount()
  })

  it('rebases the complete state context atomically when the device schema changes', async () => {
    const originalManifest: DeviceManifest = {
      Name: 'Schema Controller',
      Modes: ['OperatingMode'],
      InitState: 'idle',
      WorkingStates: [
        { Name: 'idle', Trust: 'trusted', Privacy: 'public' },
        { Name: 'active', Trust: 'untrusted', Privacy: 'private' }
      ],
      APIs: []
    }
    const revisedManifest: DeviceManifest = {
      ...originalManifest,
      WorkingStates: [
        ...originalManifest.WorkingStates!,
        { Name: 'standby', Trust: 'trusted', Privacy: 'private' }
      ]
    }
    const originalTemplate: DeviceTemplate = {
      name: originalManifest.Name,
      manifest: originalManifest,
      defaultTemplate: false
    }
    const revisedTemplate: DeviceTemplate = {
      ...originalTemplate,
      manifest: revisedManifest
    }
    const node = {
      id: 'schema-stateful-1',
      templateName: originalTemplate.name,
      label: 'Schema controller',
      position: { x: 0, y: 0 },
      state: 'idle',
      currentStateTrust: 'trusted',
      currentStatePrivacy: 'public',
      width: 176,
      height: 128
    }
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: originalTemplate.name,
        description: '',
        label: node.label,
        nodeId: node.id,
        manifest: originalManifest,
        nodes: [node],
        deviceTemplates: [originalTemplate],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    const state = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state"]')!
    const trust = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state-trust"]')!
    const privacy = () => document.querySelector<HTMLSelectElement>('[data-testid="device-runtime-state-privacy"]')!
    privacy().value = 'private'
    privacy().dispatchEvent(new Event('change', { bubbles: true }))
    await wrapper.vm.$nextTick()

    await wrapper.setProps({
      manifest: revisedManifest,
      deviceTemplates: [revisedTemplate],
      nodes: [{
        ...node,
        state: 'active',
        currentStateTrust: 'untrusted',
        currentStatePrivacy: 'private'
      }]
    })

    expect(state().value).toBe('idle')
    expect(trust().value).toBe('trusted')
    expect(privacy().value).toBe('private')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).not.toBeNull()

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-adopt-latest"]')!.click()
    await wrapper.vm.$nextTick()
    expect(state().value).toBe('active')
    expect(trust().value).toBe('untrusted')
    expect(privacy().value).toBe('private')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).toBeNull()
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

  it('adopts a new runtime schema without prompting when the draft was not edited', async () => {
    const manifest = (upperBound: number): DeviceManifest => ({
      Name: 'Controller',
      Modes: [],
      WorkingStates: [],
      InternalVariables: [{
        Name: 'threshold',
        IsInside: true,
        FalsifiableWhenCompromised: false,
        LowerBound: 0,
        UpperBound: upperBound,
        Trust: 'trusted',
        Privacy: 'public'
      }],
      APIs: []
    })
    const originalManifest = manifest(100)
    const revisedManifest = manifest(50)
    const node = {
      id: 'controller-1',
      templateName: 'Controller',
      label: 'Controller',
      position: { x: 0, y: 0 },
      state: 'Working',
      width: 176,
      height: 128,
      variables: [{ name: 'threshold', value: '10' }]
    }
    const wrapper = mount(DeviceDialog, {
      attachTo: document.body,
      props: {
        visible: true,
        deviceName: 'Controller',
        description: '',
        label: node.label,
        nodeId: node.id,
        manifest: originalManifest,
        nodes: [node],
        deviceTemplates: [{
          name: 'Controller',
          manifest: originalManifest,
          defaultTemplate: false
        }],
        specs: []
      },
      global: { plugins: [i18n] }
    })

    await wrapper.setProps({
      manifest: revisedManifest,
      nodes: [{ ...node, variables: [{ name: 'threshold', value: '7' }] }],
      deviceTemplates: [{
        name: 'Controller',
        manifest: revisedManifest,
        defaultTemplate: false
      }]
    })

    expect(document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-threshold"]'
    )?.value).toBe('7')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).toBeNull()
    expect(document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')?.disabled)
      .toBe(false)
    wrapper.unmount()
  })

  it('preserves compatible edits and requires a choice when a same-id device schema changes', async () => {
    const variable = (name: string, upperBound = 100) => ({
      Name: name,
      IsInside: true,
      FalsifiableWhenCompromised: false,
      LowerBound: 0,
      UpperBound: upperBound,
      Trust: 'trusted',
      Privacy: 'public'
    })
    const originalManifest: DeviceManifest = {
      Name: 'Original Controller',
      Modes: [],
      WorkingStates: [],
      InternalVariables: [variable('shared'), variable('alpha')],
      APIs: []
    }
    const replacementManifest: DeviceManifest = {
      Name: 'Replacement Controller',
      Modes: [],
      WorkingStates: [],
      InternalVariables: [variable('shared', 30), variable('beta')],
      APIs: []
    }
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
      variables: [
        { name: 'shared', value: '10' },
        { name: 'alpha', value: '15' }
      ]
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

    const sharedInput = () => document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-shared"]'
    )!
    const originalInput = document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-alpha"]'
    )!
    sharedInput().value = '25'
    sharedInput().dispatchEvent(new Event('input', { bubbles: true }))
    originalInput.value = '35'
    originalInput.dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()

    await wrapper.setProps({
      deviceName: replacementTemplate.name,
      manifest: replacementManifest,
      deviceTemplates: [replacementTemplate],
      nodes: [{
        ...originalNode,
        templateName: replacementTemplate.name,
        variables: [
          { name: 'shared', value: '7' },
          { name: 'beta', value: '9' }
        ]
      }]
    })

    expect(document.querySelector('[data-testid="device-runtime-variable-alpha"]')).toBeNull()
    expect(sharedInput().value).toBe('25')
    expect(document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-beta"]'
    )?.value).toBe('9')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')?.textContent)
      .toContain(i18n.global.t('app.deviceRuntimeSchemaConflict'))
    expect(document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')?.disabled)
      .toBe(true)
    expect(document.querySelector('[data-testid="device-runtime-keep-local"]')?.textContent)
      .toContain(i18n.global.t('app.deviceRuntimeContinueCompatible'))

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-keep-local"]')!.click()
    await wrapper.vm.$nextTick()
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).toBeNull()
    expect(sharedInput().value).toBe('25')
    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-save"]')!.click()
    await wrapper.vm.$nextTick()
    expect(wrapper.emitted('save-runtime')?.[0]?.[1]).toMatchObject({
      variables: [
        { name: 'shared', value: '25' },
        { name: 'beta', value: '9' }
      ]
    })

    sharedInput().value = '20'
    sharedInput().dispatchEvent(new Event('input', { bubbles: true }))
    await wrapper.vm.$nextTick()
    const revisedManifest: DeviceManifest = {
      ...replacementManifest,
      InternalVariables: [variable('shared', 40), variable('beta')]
    }
    const revisedTemplate: DeviceTemplate = {
      ...replacementTemplate,
      manifest: revisedManifest
    }
    await wrapper.setProps({
      manifest: revisedManifest,
      deviceTemplates: [revisedTemplate],
      nodes: [{
        ...originalNode,
        templateName: revisedTemplate.name,
        variables: [
          { name: 'shared', value: '11' },
          { name: 'beta', value: '12' }
        ]
      }]
    })
    expect(sharedInput().value).toBe('20')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).not.toBeNull()

    document.querySelector<HTMLButtonElement>('[data-testid="device-runtime-adopt-latest"]')!.click()
    await wrapper.vm.$nextTick()
    expect(sharedInput().value).toBe('11')
    expect(document.querySelector<HTMLInputElement>(
      '[data-testid="device-runtime-variable-beta"]'
    )?.value).toBe('12')
    expect(document.querySelector('[data-testid="device-runtime-schema-conflict"]')).toBeNull()
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
