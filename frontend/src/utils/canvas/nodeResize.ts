// src/utils/canvas/nodeResize.ts
import type { DeviceNode } from '../../types/node'

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
    resizeState: NodeResizeState
): boolean => {
    const node = resizeState.node
    if (!node) return false

    const dx = e.clientX - resizeState.start.x
    const dy = e.clientY - resizeState.start.y

    const minW = 80
    const minH = 60

    let newW = resizeState.originSize.w
    let newH = resizeState.originSize.h
    let newX = resizeState.originPos.x
    let newY = resizeState.originPos.y

    switch (resizeState.dir) {
        case 'br':
            newW = Math.max(minW, resizeState.originSize.w + dx)
            newH = Math.max(minH, resizeState.originSize.h + dy)
            break
        case 'bl':
            newW = Math.max(minW, resizeState.originSize.w - dx)
            newH = Math.max(minH, resizeState.originSize.h + dy)
            newX = resizeState.originPos.x + (resizeState.originSize.w - newW)
            break
        case 'tr':
            newW = Math.max(minW, resizeState.originSize.w + dx)
            newH = Math.max(minH, resizeState.originSize.h - dy)
            newY = resizeState.originPos.y + (resizeState.originSize.h - newH)
            break
        case 'tl':
            newW = Math.max(minW, resizeState.originSize.w - dx)
            newH = Math.max(minH, resizeState.originSize.h - dy)
            newX = resizeState.originPos.x + (resizeState.originSize.w - newW)
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
