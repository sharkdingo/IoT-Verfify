// src/utils/rule.ts
import type {DeviceEdge, DeviceNode} from '../types/board'

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


export const getNodeCenter = (node: DeviceNode) => {
    const w = node.width ?? 110
    const h = node.height ?? 90
    return {
        x: node.position.x + w / 2,
        y: node.position.y + h / 2,
    }
}

/**
 * 普通两节点连线的端点（保持你原来的实现）
 */
export const getLinkPoints = (fromNode: DeviceNode, toNode: DeviceNode) => {
    const fromCenter = getNodeCenter(fromNode)
    const toCenter = getNodeCenter(toNode)

    const fw = fromNode.width ?? 110
    const fh = fromNode.height ?? 90
    const fx1 = fromNode.position.x
    const fy1 = fromNode.position.y
    const fx2 = fx1 + fw
    const fy2 = fy1 + fh

    const tw = toNode.width ?? 110
    const th = toNode.height ?? 90
    const tx1 = toNode.position.x
    const ty1 = toNode.position.y
    const tx2 = tx1 + tw
    const ty2 = ty1 + th

    const dx = toCenter.x - fromCenter.x
    const dy = toCenter.y - fromCenter.y
    const EPS = 1e-6

    // 1) from
    let tFrom = 1
    if (Math.abs(dx) > EPS) {
        const tL = (fx1 - fromCenter.x) / dx
        const yL = fromCenter.y + tL * dy
        if (tL > 0 && yL >= fy1 && yL <= fy2) tFrom = Math.min(tFrom, tL)

        const tR = (fx2 - fromCenter.x) / dx
        const yR = fromCenter.y + tR * dy
        if (tR > 0 && yR >= fy1 && yR <= fy2) tFrom = Math.min(tFrom, tR)
    }
    if (Math.abs(dy) > EPS) {
        const tT = (fy1 - fromCenter.y) / dy
        const xT = fromCenter.x + tT * dx
        if (tT > 0 && xT >= fx1 && xT <= fx2) tFrom = Math.min(tFrom, tT)

        const tB = (fy2 - fromCenter.y) / dy
        const xB = fromCenter.x + tB * dx
        if (tB > 0 && xB >= fx1 && xB <= fx2) tFrom = Math.min(tFrom, tB)
    }
    const fromPoint = {
        x: fromCenter.x + dx * tFrom,
        y: fromCenter.y + dy * tFrom,
    }

    // 2) to (反向)
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
 * 在节点右侧画一条“半椭圆”样式的 path，用于配合 marker 画出自指箭头。
 * 会根据节点当前 width / height 自动缩放。
 */
export const getSelfLoopPath = (node: DeviceNode): string => {
    const w = node.width ?? 110
    const h = node.height ?? 90

    const right = node.position.x + w // 右边界
    const top = node.position.y

    // 自环在右侧，大致占据节点高度的中间一段
    const startY = top + h * 0.25        // 起点：右侧偏上
    const endY   = top + h * 0.75        // 终点：右侧偏下（箭头指回节点）
    const offsetX = Math.min(w, h) * 0.8 // 向右伸出去的弧度，跟节点大小一起缩放
    const ctrlOffsetY = h * 0.2          // 控制点上下“拱”的高度

    const startX = right                 // 起点就在节点右边界
    const endX   = right                 // 终点也在右边界，方便箭头指回节点

    const c1x = right + offsetX
    const c1y = startY - ctrlOffsetY

    const c2x = right + offsetX
    const c2y = endY + ctrlOffsetY

    // 标准三次贝塞尔曲线：M 起点 C 控制点1 控制点2 终点
    return `M ${startX} ${startY} C ${c1x} ${c1y} ${c2x} ${c2y} ${endX} ${endY}`
}