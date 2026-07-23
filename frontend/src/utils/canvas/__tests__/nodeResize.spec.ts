import { describe, expect, it } from 'vitest'
import type { DeviceNode } from '../../../types/node'
import {
  beginNodeResize,
  cancelNodeResize,
  createNodeResizeState,
  NODE_HEIGHT_RANGE,
  NODE_WIDTH_RANGE,
  updateNodeResize
} from '../nodeResize'

const device = (): DeviceNode => ({
  id: 'device_1',
  templateName: 'Light',
  label: 'Hall light',
  position: { x: 100, y: 80 },
  state: 'off',
  width: 176,
  height: 128
})

const pointer = (clientX: number, clientY: number) => ({ clientX, clientY } as PointerEvent)

describe('node resize persistence domain', () => {
  it('keeps displayed dimensions integral at non-unit zoom', () => {
    const node = device()
    const state = createNodeResizeState()
    beginNodeResize(pointer(0, 0), node, 'br', state)

    expect(updateNodeResize(pointer(13, 17), state, 1.5)).toBe(true)
    expect(node.width).toBe(185)
    expect(node.height).toBe(139)
  })

  it('clamps dimensions to the same domain accepted by the API', () => {
    const node = device()
    const state = createNodeResizeState()
    beginNodeResize(pointer(0, 0), node, 'br', state)

    updateNodeResize(pointer(10_000, 10_000), state)
    expect(node.width).toBe(NODE_WIDTH_RANGE.max)
    expect(node.height).toBe(NODE_HEIGHT_RANGE.max)

    beginNodeResize(pointer(0, 0), node, 'br', state)
    updateNodeResize(pointer(-10_000, -10_000), state)
    expect(node.width).toBe(NODE_WIDTH_RANGE.min)
    expect(node.height).toBe(NODE_HEIGHT_RANGE.min)
  })

  it('preserves the opposite corner when a top-left resize is clamped', () => {
    const node = device()
    const right = node.position.x + node.width
    const bottom = node.position.y + node.height
    const state = createNodeResizeState()
    beginNodeResize(pointer(0, 0), node, 'tl', state)

    updateNodeResize(pointer(1_000, 1_000), state)
    expect(node.width).toBe(NODE_WIDTH_RANGE.min)
    expect(node.height).toBe(NODE_HEIGHT_RANGE.min)
    expect(node.position.x + node.width).toBe(right)
    expect(node.position.y + node.height).toBe(bottom)
  })

  it('restores size and position when an active pointer resize is cancelled', () => {
    const node = device()
    const original = {
      width: node.width,
      height: node.height,
      position: { ...node.position }
    }
    const state = createNodeResizeState()
    beginNodeResize(pointer(0, 0), node, 'tl', state)

    updateNodeResize(pointer(-50, -30), state)
    expect(node.width).not.toBe(original.width)

    expect(cancelNodeResize(state)).toBe(node)
    expect(node).toMatchObject(original)
    expect(state.node).toBeNull()
  })
})
