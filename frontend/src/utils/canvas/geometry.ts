// src/utils/canvas/geometry.ts
import type { DeviceNode } from '@/types/node.ts'
import type { DeviceEdge } from '@/types/edge.ts'
import { getLinkPoints, getSelfLoopPath } from '../rule'

/**
 * 当某个节点移动/缩放后，重新计算与之连接的所有边的端点位置。
 */
export const updateEdgesForNode = (
    nodeId: string,
    nodes: DeviceNode[],
    edges: DeviceEdge[]
) => {
    const moved = nodes.find(n => n.id === nodeId)
    if (!moved) return

    edges.forEach(edge => {
        if (edge.from !== nodeId && edge.to !== nodeId) return

        const fromNode = nodes.find(n => n.id === edge.from)
        const toNode = nodes.find(n => n.id === edge.to)
        if (!fromNode || !toNode) return

        // 特殊：自环
        if (fromNode.id === toNode.id) {
            //const d = getSelfLoopPath(fromNode)
            edge.fromPos = { x: fromNode.position.x, y: fromNode.position.y }
            edge.toPos = { x: fromNode.position.x, y: fromNode.position.y }
            return
        }

        const { fromPoint, toPoint } = getLinkPoints(fromNode, toNode)
        edge.fromPos = fromPoint
        edge.toPos = toPoint
    })
}

/**
 * 自环 path d 的封装
 */
export const getSelfLoopD = (edge: DeviceEdge, nodes: DeviceNode[]) => {
    const n = nodes.find(n => n.id === edge.from)
    return n ? getSelfLoopPath(n) : ''
}
