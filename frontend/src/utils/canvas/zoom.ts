// src/utils/canvas/zoom.ts
export interface ZoomConfig {
    MIN_ZOOM: number
    MAX_ZOOM: number
    STEP: number
}

export const defaultZoomConfig: ZoomConfig = {
    MIN_ZOOM: 0.4,
    MAX_ZOOM: 2,
    STEP: 0.1
}

export const applyWheelZoom = (
    e: WheelEvent,
    currentZoom: number,
    cfg: ZoomConfig = defaultZoomConfig
): number | null => {
    if (!e.ctrlKey) return null
    e.preventDefault()

    if (e.deltaY > 0) {
        return Math.max(cfg.MIN_ZOOM, currentZoom - cfg.STEP)
    } else {
        return Math.min(cfg.MAX_ZOOM, currentZoom + cfg.STEP)
    }
}

export const applyKeyZoom = (
    e: KeyboardEvent,
    currentZoom: number,
    cfg: ZoomConfig = defaultZoomConfig
): number | null => {
    if (!e.ctrlKey) return null
    if (!['=', '+', '-', '0'].includes(e.key)) return null
    e.preventDefault()

    if (e.key === '=' || e.key === '+') {
        return Math.min(cfg.MAX_ZOOM, currentZoom + cfg.STEP)
    }
    if (e.key === '-') {
        return Math.max(cfg.MIN_ZOOM, currentZoom - cfg.STEP)
    }
    if (e.key === '0') {
        return 1
    }
    return null
}
