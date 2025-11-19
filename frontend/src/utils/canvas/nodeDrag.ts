// src/utils/canvas/nodeDrag.ts
import type { DeviceNode } from '@/types/node.ts'

export interface NodeDragState {
    node: DeviceNode | null
    start: { x: number; y: number }
    origin: { x: number; y: number }
}

export const createNodeDragState = (): NodeDragState => ({
    node: null,
    start: { x: 0, y: 0 },
    origin: { x: 0, y: 0 }
})

export const beginNodeDrag = (e: PointerEvent, node: DeviceNode, dragState: NodeDragState) => {
    dragState.node = node
    dragState.start = { x: e.clientX, y: e.clientY }
    dragState.origin = { x: node.position.x, y: node.position.y }
}

export const updateNodeDrag = (
    e: PointerEvent,
    dragState: NodeDragState
): boolean => {
    if (!dragState.node) return false

    const dx = e.clientX - dragState.start.x
    const dy = e.clientY - dragState.start.y

    dragState.node.position.x = dragState.origin.x + dx
    dragState.node.position.y = dragState.origin.y + dy

    return true
}

export const endNodeDrag = (dragState: NodeDragState): DeviceNode | null => {
    const node = dragState.node
    dragState.node = null
    return node
}
