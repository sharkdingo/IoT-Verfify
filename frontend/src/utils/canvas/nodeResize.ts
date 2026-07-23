// src/utils/canvas/nodeResize.ts
import type { DeviceNode } from '../../types/node'
import { NODE_HEIGHT_RANGE, NODE_WIDTH_RANGE } from './nodeLayout'

export { NODE_HEIGHT_RANGE, NODE_WIDTH_RANGE } from './nodeLayout'

export interface NodeResizeState {
    node: DeviceNode | null
    start: { x: number; y: number }
    originSize: { w: number; h: number }
    originPos: { x: number; y: number }
    dir: 'tl' | 'tr' | 'bl' | 'br'
}

export const createNodeResizeState = (): NodeResizeState => ({
    node: null,
    start: { x: 0, y: 0 },
    originSize: { w: 0, h: 0 },
    originPos: { x: 0, y: 0 },
    dir: 'br'
})

export const beginNodeResize = (
    e: PointerEvent,
    node: DeviceNode,
    dir: 'tl' | 'tr' | 'bl' | 'br',
    resizeState: NodeResizeState
) => {
    resizeState.node = node
    resizeState.dir = dir
    resizeState.start = { x: e.clientX, y: e.clientY }
    resizeState.originSize = { w: node.width, h: node.height }
    resizeState.originPos = { x: node.position.x, y: node.position.y }
}

export const updateNodeResize = (
    e: PointerEvent,
    resizeState: NodeResizeState,
    zoom = 1
): boolean => {
    const node = resizeState.node
    if (!node) return false

    const scale = Number.isFinite(zoom) && zoom > 0 ? zoom : 1
    const dx = (e.clientX - resizeState.start.x) / scale
    const dy = (e.clientY - resizeState.start.y) / scale

    let newW = resizeState.originSize.w
    let newH = resizeState.originSize.h
    let newX = resizeState.originPos.x
    let newY = resizeState.originPos.y

    switch (resizeState.dir) {
        case 'br':
            newW = resizeState.originSize.w + dx
            newH = resizeState.originSize.h + dy
            break
        case 'bl':
            newW = resizeState.originSize.w - dx
            newH = resizeState.originSize.h + dy
            break
        case 'tr':
            newW = resizeState.originSize.w + dx
            newH = resizeState.originSize.h - dy
            break
        case 'tl':
            newW = resizeState.originSize.w - dx
            newH = resizeState.originSize.h - dy
    }

    newW = Math.round(Math.min(NODE_WIDTH_RANGE.max, Math.max(NODE_WIDTH_RANGE.min, newW)))
    newH = Math.round(Math.min(NODE_HEIGHT_RANGE.max, Math.max(NODE_HEIGHT_RANGE.min, newH)))
    if (resizeState.dir === 'bl' || resizeState.dir === 'tl') {
        newX = resizeState.originPos.x + (resizeState.originSize.w - newW)
    }
    if (resizeState.dir === 'tr' || resizeState.dir === 'tl') {
        newY = resizeState.originPos.y + (resizeState.originSize.h - newH)
    }

    node.width = newW
    node.height = newH
    node.position.x = newX
    node.position.y = newY

    return true
}

export const endNodeResize = (resizeState: NodeResizeState): DeviceNode | null => {
    const n = resizeState.node
    resizeState.node = null
    return n
}

export const cancelNodeResize = (resizeState: NodeResizeState): DeviceNode | null => {
    const node = resizeState.node
    if (!node) return null

    node.width = resizeState.originSize.w
    node.height = resizeState.originSize.h
    node.position.x = resizeState.originPos.x
    node.position.y = resizeState.originPos.y
    resizeState.node = null
    return node
}
