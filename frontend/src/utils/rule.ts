// src/utils/rule.ts
import type { DeviceEdge } from '../types/edge'
import type { DeviceNode } from '../types/node'

/**
 * 节点重命名时：更新所有相关规则（边）上的 fromLabel / toLabel
 * @returns 是否发生了修改
 */
export const updateRulesForNodeRename = (
    rules: DeviceEdge[],
    nodeId: string,
    newLabel: string
): boolean => {
    let changed = false

    rules.forEach(edge => {
        if (edge.from === nodeId && edge.fromLabel !== newLabel) {
            edge.fromLabel = newLabel
            changed = true
        }
        if (edge.to === nodeId && edge.toLabel !== newLabel) {
            edge.toLabel = newLabel
            changed = true
        }
    })

    return changed
}

/**
 * 获取节点中心点坐标
 */
export const getNodeCenter = (node: DeviceNode) => {
    const w = node.width || 110
    const h = node.height || 90
    return {
        x: node.position.x + w / 2,
        y: node.position.y + h / 2,
    }
}

/**
 * 计算两个节点之间连线的端点（切点）
 * 使得连线看起来是从节点边缘出发，而不是从中心出发
 */
export const getLinkPoints = (fromNode: DeviceNode, toNode: DeviceNode) => {
    const fromCenter = getNodeCenter(fromNode)
    const toCenter = getNodeCenter(toNode)

    const fw = fromNode.width || 110
    const fh = fromNode.height || 90
    const fx1 = fromNode.position.x
    const fy1 = fromNode.position.y
    const fx2 = fx1 + fw
    const fy2 = fy1 + fh

    const tw = toNode.width || 110
    const th = toNode.height || 90
    const tx1 = toNode.position.x
    const ty1 = toNode.position.y
    const tx2 = tx1 + tw
    const ty2 = ty1 + th

    const dx = toCenter.x - fromCenter.x
    const dy = toCenter.y - fromCenter.y
    const EPS = 1e-6

    // 1) 计算起始点 (Intersection with From Node)
    let tFrom = 1
    if (Math.abs(dx) > EPS) {
        // Left edge
        const tL = (fx1 - fromCenter.x) / dx
        const yL = fromCenter.y + tL * dy
        if (tL > 0 && yL >= fy1 && yL <= fy2) tFrom = Math.min(tFrom, tL)

        // Right edge
        const tR = (fx2 - fromCenter.x) / dx
        const yR = fromCenter.y + tR * dy
        if (tR > 0 && yR >= fy1 && yR <= fy2) tFrom = Math.min(tFrom, tR)
    }
    if (Math.abs(dy) > EPS) {
        // Top edge
        const tT = (fy1 - fromCenter.y) / dy
        const xT = fromCenter.x + tT * dx
        if (tT > 0 && xT >= fx1 && xT <= fx2) tFrom = Math.min(tFrom, tT)

        // Bottom edge
        const tB = (fy2 - fromCenter.y) / dy
        const xB = fromCenter.x + tB * dx
        if (tB > 0 && xB >= fx1 && xB <= fx2) tFrom = Math.min(tFrom, tB)
    }
    const fromPoint = {
        x: fromCenter.x + dx * tFrom,
        y: fromCenter.y + dy * tFrom,
    }

    // 2) 计算终点 (Intersection with To Node)
    // 反向向量
    const bdx = fromCenter.x - toCenter.x
    const bdy = fromCenter.y - toCenter.y
    let tTo = 1
    if (Math.abs(bdx) > EPS) {
        const tL = (tx1 - toCenter.x) / bdx
        const yL = toCenter.y + tL * bdy
        if (tL > 0 && yL >= ty1 && yL <= ty2) tTo = Math.min(tTo, tL)

        const tR = (tx2 - toCenter.x) / bdx
        const yR = toCenter.y + tR * bdy
        if (tR > 0 && yR >= ty1 && yR <= ty2) tTo = Math.min(tTo, tR)
    }
    if (Math.abs(bdy) > EPS) {
        const tT = (ty1 - toCenter.y) / bdy
        const xT = toCenter.x + tT * bdx
        if (tT > 0 && xT >= tx1 && xT <= tx2) tTo = Math.min(tTo, tT)

        const tB = (ty2 - toCenter.y) / bdy
        const xB = toCenter.x + tB * bdx
        if (tB > 0 && xB >= tx1 && xB <= tx2) tTo = Math.min(tTo, tB)
    }
    const toPoint = {
        x: toCenter.x + bdx * tTo,
        y: toCenter.y + bdy * tTo,
    }

    return { fromPoint, toPoint }
}

/**
 * 自环连线（from === to）：
 * 在节点右侧画一条“半椭圆”样式的 path
 */
export const getSelfLoopPath = (node: DeviceNode): string => {
    const w = node.width || 110
    const h = node.height || 90

    const right = node.position.x + w
    const top = node.position.y

    const startY = top + h * 0.25
    const endY   = top + h * 0.75
    const offsetX = Math.min(w, h) * 0.8
    const ctrlOffsetY = h * 0.2

    const startX = right
    const endX   = right

    const c1x = right + offsetX
    const c1y = startY - ctrlOffsetY

    const c2x = right + offsetX
    const c2y = endY + ctrlOffsetY

    return `M ${startX} ${startY} C ${c1x} ${c1y} ${c2x} ${c2y} ${endX} ${endY}`
}