// src/utils/canvas/nodeDrag.ts
import type { DeviceNode } from '@/types/node.ts'

export interface NodeDragState {
    node: DeviceNode | null
    start: { x: number; y: number }
    origin: { x: number; y: number }
    // Temporary position during drag to avoid triggering Vue reactivity on every pointermove
    tempPosition: { x: number; y: number } | null
}

export const createNodeDragState = (): NodeDragState => ({
    node: null,
    start: { x: 0, y: 0 },
    origin: { x: 0, y: 0 },
    tempPosition: null
})

export const beginNodeDrag = (e: PointerEvent, node: DeviceNode, dragState: NodeDragState) => {
    dragState.node = node
    dragState.start = { x: e.clientX, y: e.clientY }
    dragState.origin = { x: node.position.x, y: node.position.y }
    // Initialize temp position (non-reactive)
    dragState.tempPosition = { x: node.position.x, y: node.position.y }
}

export const updateNodeDrag = (
    e: PointerEvent,
    dragState: NodeDragState,
    zoom = 1
): boolean => {
    if (!dragState.node || !dragState.tempPosition) return false

    const scale = Number.isFinite(zoom) && zoom > 0 ? zoom : 1
    const dx = (e.clientX - dragState.start.x) / scale
    const dy = (e.clientY - dragState.start.y) / scale

    // Update temporary position instead of reactive node.position
    // This prevents triggering Vue reactivity on every pointermove event
    dragState.tempPosition.x = dragState.origin.x + dx
    dragState.tempPosition.y = dragState.origin.y + dy

    return true
}

/**
 * Get the current drag position (temporary during drag, committed position after drag ends).
 * Used for rendering the dragging node at its visual position.
 */
export const getNodeDragPosition = (node: DeviceNode, dragState: NodeDragState): { x: number; y: number } => {
    if (dragState.node === node && dragState.tempPosition) {
        return dragState.tempPosition
    }
    return node.position
}

export const endNodeDrag = (dragState: NodeDragState): DeviceNode | null => {
    const node = dragState.node
    if (node && dragState.tempPosition) {
        // Commit the temporary position to the reactive node.position (single update)
        node.position.x = dragState.tempPosition.x
        node.position.y = dragState.tempPosition.y
    }
    dragState.node = null
    dragState.tempPosition = null
    return node
}

export const cancelNodeDrag = (dragState: NodeDragState): DeviceNode | null => {
    const node = dragState.node
    if (!node) return null

    // No need to reset position - temp position is discarded
    dragState.node = null
    dragState.tempPosition = null
    return node
}
