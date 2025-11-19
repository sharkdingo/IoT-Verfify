// src/utils/canvas/pan.ts
import type { CanvasPan } from '../../types/canvas'

export interface PanState {
    isPanning: boolean
    start: { x: number; y: number }
    origin: { x: number; y: number }
}

export const createPanState = (): PanState => ({
    isPanning: false,
    start: { x: 0, y: 0 },
    origin: { x: 0, y: 0 }
})

export const onCanvasPointerDownPan = (
    e: PointerEvent,
    panState: PanState,
    currentPan: CanvasPan
) => {
    panState.isPanning = true
    panState.start = { x: e.clientX, y: e.clientY }
    panState.origin = { ...currentPan }
}

export const onCanvasPointerMovePan = (
    e: PointerEvent,
    panState: PanState,
    zoom: number
): CanvasPan | null => {
    if (!panState.isPanning) return null
    const dx = e.clientX - panState.start.x
    const dy = e.clientY - panState.start.y

    return {
        x: panState.origin.x + dx / zoom,
        y: panState.origin.y + dy / zoom
    }
}

export const onCanvasPointerUpPan = (panState: PanState) => {
    panState.isPanning = false
}
