import { mount } from '@vue/test-utils'
import { describe, expect, it, vi } from 'vitest'

import CanvasBoard from '@/components/CanvasBoard.vue'
import { i18n } from '@/assets/i18n'

describe('CanvasBoard device context actions', () => {
  it('opens the custom device menu on mouse right-click', async () => {
    const node = {
      id: 'light-1',
      templateName: 'Light',
      label: 'Hall light',
      position: { x: 40, y: 50 },
      state: 'off',
      width: 176,
      height: 128
    }
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [node],
        edges: [],
        pan: { x: 0, y: 0 },
        zoom: 1,
        getNodeIcon: () => '',
        getNodeLabelStyle: () => ({})
      },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-node-id="light-1"]').trigger('contextmenu', {
      clientX: 240,
      clientY: 180
    })

    expect(wrapper.emitted('node-context')).toEqual([[node, { x: 240, y: 180 }]])
    wrapper.unmount()
  })

  it('keeps rule labels hidden until the edge is hovered or keyboard-focused', async () => {
    const source = {
      id: 'motion-1',
      templateName: 'Motion Detector',
      label: 'Hall motion',
      position: { x: 40, y: 50 },
      state: 'idle',
      width: 176,
      height: 128
    }
    const target = {
      id: 'camera-1',
      templateName: 'Camera',
      label: 'Hall camera',
      position: { x: 420, y: 220 },
      state: 'on',
      width: 176,
      height: 128
    }
    const edge = {
      id: 'rule-1-source-0',
      from: source.id,
      to: target.id,
      fromLabel: source.label,
      toLabel: target.label,
      fromPos: source.position,
      toPos: target.position,
      fromApi: 'motion',
      toApi: 'take photo',
      itemType: 'variable' as const,
      relation: '=',
      value: 'active',
      ruleId: 'rule-1'
    }
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [source, target],
        edges: [edge],
        pan: { x: 0, y: 0 },
        zoom: 1,
        focusedRuleId: 'rule-1',
        getNodeIcon: () => '',
        getNodeLabelStyle: () => ({})
      },
      global: { plugins: [i18n] }
    })

    expect(wrapper.find('.edge-label').exists()).toBe(false)

    const hitarea = wrapper.get('.edge-hitarea')
    await hitarea.trigger('pointerenter')
    expect(wrapper.find('.edge-label').exists()).toBe(true)

    await hitarea.trigger('pointerleave')
    expect(wrapper.find('.edge-label').exists()).toBe(false)

    await hitarea.trigger('focus')
    expect(wrapper.find('.edge-label').exists()).toBe(true)

    wrapper.unmount()
  })

  it('localizes each playback delta on the changed device while the triggered edge carries command flow', () => {
    const source = {
      id: 'motion-1',
      templateName: 'Motion Detector',
      label: 'Hall motion',
      position: { x: 40, y: 50 },
      state: 'idle',
      width: 176,
      height: 128
    }
    const target = {
      id: 'light-1',
      templateName: 'Light',
      label: 'Hall light',
      position: { x: 420, y: 220 },
      state: 'off',
      width: 176,
      height: 128
    }
    const edge = {
      id: 'rule-1-source-0',
      from: source.id,
      to: target.id,
      fromLabel: source.label,
      toLabel: target.label,
      fromPos: source.position,
      toPos: target.position,
      fromApi: 'motion',
      toApi: 'turn on',
      itemType: 'api' as const,
      ruleId: 'rule-1'
    }
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [source, target],
        edges: [edge],
        pan: { x: 0, y: 0 },
        zoom: 1,
        highlightedTrace: {
          selectedStateIndex: 1,
          states: [
            {
              stateIndex: 1,
              triggeredRules: [],
              compromisedAutomationLinks: [],
              devices: [
                { deviceId: 'motion_1', deviceLabel: source.label, state: 'idle', variables: [] },
                { deviceId: 'light_1', deviceLabel: target.label, state: 'off', variables: [{ name: 'brightness', value: '0' }] }
              ]
            },
            {
              stateIndex: 2,
              triggeredRules: [{ ruleId: 'rule-1', ruleLabel: 'Motion turns on light' }],
              compromisedAutomationLinks: [],
              devices: [
                { deviceId: 'motion_1', deviceLabel: source.label, state: 'active', variables: [] },
                { deviceId: 'light_1', deviceLabel: target.label, state: 'on', variables: [{ name: 'brightness', value: '100' }] }
              ]
            }
          ]
        },
        getNodeIcon: () => '',
        getNodeLabelStyle: () => ({})
      },
      global: { plugins: [i18n] }
    })

    const changedTarget = wrapper.get('[data-node-id="light-1"]')
    expect(changedTarget.classes()).toContain('trace-changed')
    expect(changedTarget.get('.device-runtime-chip--changed').text()).toContain('100')
    expect(changedTarget.find('[data-testid="trace-change-badge"]').exists()).toBe(false)
    expect(changedTarget.find('.device-runtime-chip__previous').exists()).toBe(false)
    expect(wrapper.findAll('.edge-line--active').length).toBeGreaterThan(0)
    expect(wrapper.find('.particle-line').exists()).toBe(true)

    wrapper.unmount()
  })

  it('restarts delivered-rule edge flow for each model transition', async () => {
    const source = {
      id: 'motion-1',
      templateName: 'Motion Detector',
      label: 'Hall motion',
      position: { x: 40, y: 50 },
      state: 'idle',
      width: 176,
      height: 128
    }
    const target = {
      id: 'light-1',
      templateName: 'Light',
      label: 'Hall light',
      position: { x: 420, y: 220 },
      state: 'off',
      width: 176,
      height: 128
    }
    const edge = {
      id: 'rule-1-source-0',
      from: source.id,
      to: target.id,
      fromLabel: source.label,
      toLabel: target.label,
      fromPos: source.position,
      toPos: target.position,
      fromApi: 'motion',
      toApi: 'turn on',
      itemType: 'variable' as const,
      relation: '=',
      value: 'active',
      ruleId: 'rule-1'
    }
    const states = [
      { triggeredRules: [], compromisedAutomationLinks: [], devices: [] },
      {
        triggeredRules: [{ ruleId: 'rule-1', ruleLabel: 'Motion turns on light' }],
        compromisedAutomationLinks: [],
        devices: []
      },
      {
        triggeredRules: [{ ruleId: 'rule-1', ruleLabel: 'Motion turns on light' }],
        compromisedAutomationLinks: [],
        devices: []
      }
    ]
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [source, target],
        edges: [edge],
        pan: { x: 0, y: 0 },
        zoom: 1,
        highlightedTrace: { states, selectedStateIndex: 1 },
        getNodeIcon: () => '',
        getNodeLabelStyle: () => ({})
      },
      global: { plugins: [i18n] }
    })

    const firstFlow = wrapper.get('.particle-line').element
    expect(firstFlow.getAttribute('data-playback-state')).toBe('1')
    expect(wrapper.html()).toContain('repeatCount="1"')
    expect(wrapper.html()).not.toContain('repeatCount="indefinite"')

    await wrapper.setProps({ highlightedTrace: { states, selectedStateIndex: 2 } })
    await wrapper.vm.$nextTick()

    const secondFlow = wrapper.get('.particle-line').element
    expect(secondFlow.getAttribute('data-playback-state')).toBe('2')
    expect(secondFlow).not.toBe(firstFlow)
    wrapper.unmount()
  })

  it('replays every semantic device change and renders the new visual state immediately', async () => {
    vi.useFakeTimers()
    const node = {
      id: 'camera-1',
      templateName: 'Camera',
      label: 'Hall camera',
      position: { x: 80, y: 80 },
      state: 'off',
      width: 176,
      height: 128
    }
    const states = [
      {
        devices: [{
          deviceId: 'camera_1',
          deviceLabel: node.label,
          state: 'off',
          variables: [],
          trustPrivacy: [{ name: 'off', propertyScope: 'state' as const, trust: true }]
        }]
      },
      {
        devices: [{
          deviceId: 'camera_1',
          deviceLabel: node.label,
          state: 'off',
          variables: [],
          trustPrivacy: [{ name: 'off', propertyScope: 'state' as const, trust: false }]
        }]
      },
      {
        devices: [{
          deviceId: 'camera_1',
          deviceLabel: node.label,
          state: 'on',
          variables: [],
          trustPrivacy: [{ name: 'on', propertyScope: 'state' as const, trust: false }]
        }]
      }
    ]
    const getNodeIcon = vi.fn((_node: typeof node, state?: string) => `/${state}.svg`)
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [node],
        edges: [],
        pan: { x: 0, y: 0 },
        zoom: 1,
        highlightedTrace: { states, selectedStateIndex: 0 },
        getNodeIcon,
        getNodeLabelStyle: () => ({})
      },
      global: { plugins: [i18n] }
    })

    try {
      await wrapper.setProps({ highlightedTrace: { states, selectedStateIndex: 1 } })
      await Promise.resolve()
      await wrapper.vm.$nextTick()
      await wrapper.vm.$nextTick()
      const changedNode = wrapper.get('[data-node-id="camera-1"]')
      expect(changedNode.classes()).toContain('trace-changed')
      expect(changedNode.classes()).toContain('trace-change-pulse')

      await wrapper.setProps({ highlightedTrace: { states, selectedStateIndex: 2 } })
      await Promise.resolve()
      await wrapper.vm.$nextTick()
      await wrapper.vm.$nextTick()
      expect(changedNode.classes()).toContain('trace-change-pulse')
      expect(changedNode.get('.device-state-value').text()).toBe('on')
      expect(changedNode.get('.device-img').attributes('src')).toBe('/on.svg')

      await wrapper.setProps({ highlightedTrace: null })
      await wrapper.vm.$nextTick()
      expect(changedNode.classes()).not.toContain('trace-change-pulse')
    } finally {
      wrapper.unmount()
      vi.useRealTimers()
    }
  })
})
