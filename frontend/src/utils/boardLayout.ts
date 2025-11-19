// src/utils/boardLayout.ts
import type { DeviceNode, DeviceEdge } from '../types/board'
import type { DeviceTemplate } from '../types/device'
import { getLinkPoints } from './rule'

/**
 * 根据基础名称和已有节点，生成唯一 label
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

/**
 * 根据 nodeId 重新计算与该节点相连的边的端点坐标
 */
export function updateEdgesForNode(
    nodeId: string,
    nodes: DeviceNode[],
    edges: DeviceEdge[]
) {
    const fromNode = nodes.find(n => n.id === nodeId)
    if (!fromNode) return

    edges.forEach(edge => {
        if (edge.from !== nodeId && edge.to !== nodeId) return

        const from = nodes.find(n => n.id === edge.from)
        const to = nodes.find(n => n.id === edge.to)
        if (!from || !to) return

        const { fromPoint, toPoint } = getLinkPoints(from, to)
        edge.fromPos = fromPoint
        edge.toPos = toPoint
    })
}

/**
 * 通过节点 id 找到对应模板
 */
export function getTemplateByNodeId(
    nodeId: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): DeviceTemplate | undefined {
    const n = nodes.find(n => n.id === nodeId)
    if (!n) return
    return templates.find(t => t.name === n.templateName)
}
