// src/utils/canvas/template.ts
import type { DeviceNode } from '../../types/node'
import type { DeviceTemplate } from '../../types/device'

/**
 * 根据 nodeId 找到对应的模板定义（templateName 匹配模板 name）
 */
export function getTemplateByNodeId(
    nodeId: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): DeviceTemplate | undefined {
    const n = nodes.find(n => n.id === nodeId)
    if (!n) return undefined
    return templates.find(t => t.name === n.templateName)
}
