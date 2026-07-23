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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working'
      },
      global: { plugins: [i18n] }
    })

    await wrapper.get('[data-node-id="light-1"]').trigger('contextmenu', {
      clientX: 240,
      clientY: 180
    })

    expect(wrapper.emitted('node-context')).toEqual([[node, { x: 240, y: 180 }]])
    expect(wrapper.get('.device-label').attributes('title')).toBe('Hall light')

    await wrapper.get('[data-node-id="light-1"]').trigger('keydown', {
      key: 'F10',
      shiftKey: true
    })
    expect(wrapper.emitted('node-context')).toHaveLength(2)
    const keyboardPayload = wrapper.emitted('node-context')?.[1]
    expect(keyboardPayload?.[0]).toStrictEqual(node)
    expect(keyboardPayload?.[1]).toEqual({ x: expect.any(Number), y: expect.any(Number) })
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
      fromApi: 'state',
      toApi: 'take photo',
      itemType: 'variable' as const,
      relation: 'in',
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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working',
        formatNodeModelToken: (_node, value) => ({
          state: '状态',
          active: '活动',
          'take photo': '拍照'
        }[String(value)] || String(value ?? ''))
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
    expect(wrapper.get('.edge-label').text()).toContain('Hall motion.状态 属于 活动')
    expect(wrapper.get('.edge-label').text()).toContain('Hall camera.拍照')
    expect(edge).toMatchObject({ fromApi: 'state', relation: 'in', value: 'active', toApi: 'take photo' })

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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working'
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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working'
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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working'
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

  it('localizes playback security labels without changing canonical trace facts', () => {
    const node = {
      id: 'camera-1',
      templateName: 'Camera',
      label: 'Hall camera',
      position: { x: 80, y: 80 },
      state: 'off',
      width: 176,
      height: 128
    }
    const highlightedTrace = {
      selectedStateIndex: 0,
      states: [{
        devices: [{
          deviceId: 'camera_1',
          deviceLabel: node.label,
          templateName: 'Camera',
          mode: 'MachineState',
          state: 'on',
          variables: [],
          trustPrivacy: [{ name: 'on', propertyScope: 'state' as const, mode: 'MachineState', trust: false }],
          privacies: [{ name: 'photo', propertyScope: 'content' as const, privacy: 'private' }]
        }]
      }]
    }
    const canonicalSnapshot = structuredClone(highlightedTrace)
    const labels: Record<string, string> = {
      MachineState: '设备状态',
      on: '开启',
      photo: '照片'
    }
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [node],
        edges: [],
        pan: { x: 0, y: 0 },
        zoom: 1,
        highlightedTrace,
        getNodeIcon: () => '',
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'Working',
        formatNodeModelToken: (_node, value) => labels[String(value)] || String(value ?? '')
      },
      global: { plugins: [i18n] }
    })

    const titles = wrapper.findAll('.device-node-trust').map(badge => badge.attributes('title'))
    expect(titles.some(title => title?.includes('设备状态: 开启'))).toBe(true)
    expect(titles.some(title => title?.includes('照片'))).toBe(true)
    expect(titles.join(' ')).not.toContain('MachineState: on')
    expect(highlightedTrace).toEqual(canonicalSnapshot)
    wrapper.unmount()
  })

  it('shows a localized stateless label instead of the persistence fallback state', () => {
    const node = {
      id: 'sensor-1',
      templateName: 'Temperature Sensor',
      label: 'Hall sensor',
      position: { x: 20, y: 30 },
      state: 'Working',
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
        hasNodeStateMachine: () => false,
        getNodeEffectiveState: () => 'Working'
      },
      global: { plugins: [i18n] }
    })

    const rendered = wrapper.get('[data-node-id="sensor-1"]')
    expect(rendered.get('.device-state').classes()).toContain('state-stateless')
    expect(rendered.get('.device-state-value').text()).toBe(i18n.global.t('app.noStateMachine'))
    expect(rendered.attributes('title')).not.toContain('Working')
    wrapper.unmount()
  })

  it('uses compact, condensed, and expanded tiers and supports keyboard resizing', async () => {
    const node = {
      id: 'light-1',
      templateName: 'Light',
      label: 'Hall light',
      position: { x: 20, y: 30 },
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
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'off'
      },
      global: { plugins: [i18n] }
    })
    const rendered = wrapper.get('[data-node-id="light-1"]')

    expect(rendered.classes()).toContain('device-node--expanded')
    expect(rendered.findAll('.resize-handle')).toHaveLength(4)
    await wrapper.setProps({ zoom: 0.7 })
    expect(rendered.classes()).toContain('device-node--condensed')
    expect(rendered.findAll('.resize-handle')).toHaveLength(4)
    await wrapper.setProps({ zoom: 0.5 })
    expect(rendered.classes()).toContain('device-node--compact')
    expect(rendered.findAll('.resize-handle')).toHaveLength(4)

    await rendered.trigger('keydown', { key: 'ArrowRight', ctrlKey: true })
    await rendered.trigger('keydown', { key: 'ArrowDown', ctrlKey: true, shiftKey: true })
    expect(node.width).toBe(186)
    expect(node.height).toBe(129)
    expect(wrapper.emitted('node-moved-or-resized')).toEqual([['light-1'], ['light-1']])
    wrapper.unmount()
  })

  it('hides overlapping pointer resize targets at minimum size and low zoom while keeping keyboard resize', async () => {
    const node = {
      id: 'small-light-1',
      templateName: 'Light',
      label: 'Small light',
      position: { x: 20, y: 30 },
      state: 'off',
      width: 80,
      height: 60
    }
    const wrapper = mount(CanvasBoard, {
      props: {
        nodes: [node],
        edges: [],
        pan: { x: 0, y: 0 },
        zoom: 0.4,
        getNodeIcon: () => '',
        hasNodeStateMachine: () => true,
        getNodeEffectiveState: currentNode => currentNode.state || 'off'
      },
      global: { plugins: [i18n] }
    })
    const rendered = wrapper.get('[data-node-id="small-light-1"]')

    expect(rendered.findAll('.resize-handle')).toHaveLength(0)
    await rendered.trigger('keydown', { key: 'ArrowRight', ctrlKey: true })
    expect(node.width).toBe(90)
    expect(wrapper.emitted('node-moved-or-resized')).toEqual([['small-light-1']])

    await wrapper.setProps({ zoom: 1 })
    expect(rendered.findAll('.resize-handle')).toHaveLength(4)
    wrapper.unmount()
  })
})
