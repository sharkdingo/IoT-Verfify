// src/utils/canvas/nodeCreate.ts
import type { DeviceNode } from '@/types/node.ts'

export const deviceLabelKey = (value: unknown): string =>
    String(value ?? '').trim().toLowerCase()

export function reserveUniqueDeviceLabel(base: string, reservedKeys: Set<string>): string {
    const normalizedBase = String(base ?? '').trim()
    if (!normalizedBase) return ''

    let index = 0
    let candidate = normalizedBase
    while (reservedKeys.has(deviceLabelKey(candidate))) {
        index += 1
        candidate = `${normalizedBase}_${index}`
    }
    reservedKeys.add(deviceLabelKey(candidate))
    return candidate
}

/**
 * Generate a unique user-facing label. Device identity is deliberately separate:
 * renaming a device must not rewrite rule/spec references or its model identity.
 */
export function getUniqueLabel(base: string, nodes: DeviceNode[]): string {
    const existingLabels = new Set(nodes.map(node => deviceLabelKey(node.label)).filter(Boolean))
    return reserveUniqueDeviceLabel(base, existingLabels)
}

/**
 * Generate an opaque, portable board reference for a new device instance.
 * The `device_` namespace cannot be confused with user-facing labels or the
 * model's generated environment/rule/attack/fix identifiers.
 */
export function createDeviceInstanceId(nodes: Pick<DeviceNode, 'id'>[]): string {
    const existingIds = new Set(nodes.map(node => node.id))
    let candidate = ''
    do {
        const uuid = globalThis.crypto?.randomUUID?.()
            ?? `${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 14)}`
        candidate = `device_${uuid}`
    } while (existingIds.has(candidate))
    return candidate
}
