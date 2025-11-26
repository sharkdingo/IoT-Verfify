// src/utils/boardStorage.ts
import type { DeviceTemplate } from '@/types/device'

export const STORAGE_KEYS = {
    DEVICES: 'iot_devices',
}

export function loadDeviceTemplates(): DeviceTemplate[] {
    const raw = sessionStorage.getItem(STORAGE_KEYS.DEVICES)
    return raw ? JSON.parse(raw) : []
}

export function saveDeviceTemplates(devices: DeviceTemplate[]) {
    sessionStorage.setItem(STORAGE_KEYS.DEVICES, JSON.stringify(devices))
}
