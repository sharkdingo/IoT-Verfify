// src/utils/canvas/nodeCreate.ts
import type { DeviceNode } from '@/types/node.ts'

/**
 * 根据基础名称和已有节点，生成唯一 label。
 * AC_Cooler -> AC_Cooler_1 -> AC_Cooler_2 ...
 */
export function getUniqueLabel(base: string, nodes: DeviceNode[]): string {
    const existing = nodes.map(n => n.label)
    if (!existing.includes(base)) return base

    let idx = 1
    while (true) {
        const candidate = `${base}_${idx}`
        if (!existing.includes(candidate)) return candidate
        idx++
    }
}
