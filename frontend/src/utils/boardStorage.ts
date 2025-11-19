// src/utils/boardStorage.ts
import type { DeviceNode, DeviceEdge, PanelPositions, PanelActive } from '../types/board'
import type { DeviceTemplate } from '../types/device'
import { Specification } from "../types/spec";

export const STORAGE_KEYS = {
    DEVICES: 'iot_devices',
    NODES: 'iot_nodes',
    EDGES: 'iot_edges',
    SPECS: 'iot_specs',
    PANELS: 'iot_panels',
    PANEL_ACTIVE: 'iot_panel_active'
}

// 通用 load/save
export function loadFromSession<T>(key: string): T | null {
    const raw = sessionStorage.getItem(key)
    return raw ? (JSON.parse(raw) as T) : null
}

export function saveToSession<T>(key: string, value: T) {
    sessionStorage.setItem(key, JSON.stringify(value))
}

//---------------------------------------//
export function loadDeviceTemplates(): DeviceTemplate[] {
    return loadFromSession<DeviceTemplate[]>(STORAGE_KEYS.DEVICES) ?? []
}

export function loadNodes(): DeviceNode[] {
    return loadFromSession<DeviceNode[]>(STORAGE_KEYS.NODES) ?? []
}

export function loadEdges(): DeviceEdge[] {
    return loadFromSession<DeviceEdge[]>(STORAGE_KEYS.EDGES) ?? []
}

export function loadSpecs(): Specification[] {
    return loadFromSession<Specification[]>(STORAGE_KEYS.SPECS) ?? []
}

export function loadPanels(): PanelPositions | null {
    return loadFromSession<PanelPositions>(STORAGE_KEYS.PANELS)
}

export function loadPanelActive(): PanelActive | null {
    return loadFromSession<PanelActive>(STORAGE_KEYS.PANEL_ACTIVE)
}

export function saveDeviceTemplates(devices: DeviceTemplate[]) {
    saveToSession(STORAGE_KEYS.DEVICES, devices)
}

export function saveNodes(nodes: DeviceNode[]) {
    saveToSession(STORAGE_KEYS.NODES, nodes)
}

export function saveEdges(edges: DeviceEdge[]) {
    saveToSession(STORAGE_KEYS.EDGES, edges)
}

export function saveSpecs(specs: Specification[]) {
    saveToSession(STORAGE_KEYS.SPECS, specs)
}

export function savePanels(panels: PanelPositions) {
    saveToSession(STORAGE_KEYS.PANELS, panels)
}

export function savePanelActive(active: PanelActive) {
    saveToSession(STORAGE_KEYS.PANEL_ACTIVE, active)
}