// src/utils/geometry.ts
import type { DeviceNode } from '../types/board'

export const getNodeCenter = (node: DeviceNode) => {
    const w = node.width ?? 110
    const h = node.height ?? 90
    return {
        x: node.position.x + w / 2,
        y: node.position.y + h / 2
    }
}

/**
 * 给两个节点，返回连线应该从哪个点出、在哪个点停（都在节点外框上）
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
        y: fromCenter.y + dy * tFrom
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
        y: toCenter.y + bdy * tTo
    }

    return { fromPoint, toPoint }
}