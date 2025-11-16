// src/utils/spec.ts
import type {
    SpecSide,
    SpecCondition,
    SpecTargetType,
    SpecTemplateId
} from '../types/board'
import type { DeviceNode } from '../types/board'
import type { DeviceTemplate } from '../types/device'
import { getTemplateByNodeId } from './boardLayout'

/** 创建一个空条件（A / IF / THEN 通用） */
export function createEmptyCondition(side: SpecSide): SpecCondition {
    return {
        id: `cond_${side}_${Date.now()}_${Math.random().toString(16).slice(2)}`,
        side,
        deviceId: '',
        deviceLabel: '',
        targetType: 'state',
        key: '',
        relation: 'in',
        value: ''
    }
}

/** 根据模板 id 判断当前是单 A 还是 IF/THEN 规约 */
export function getSpecMode(templateId: SpecTemplateId | ''): 'single' | 'ifThen' {
    if (!templateId) return 'single'
    const num = Number(templateId)
    return num >= 4 && num !== 7 ? 'ifThen' : 'single'
}

/** A/B 里第二个下拉：State / 变量 / API 列表 */
export function getTargetOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
) {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) {
        return [{ label: 'State', value: 'State' }]
    }
    const vars =
        tpl.manifest?.ImpactedVariables?.map(v => ({ label: v, value: v })) ?? []
    const apis =
        tpl.manifest?.APIs?.map(api => ({ label: api.Name, value: api.Name })) ?? []

    return [{ label: 'State', value: 'State' }, ...vars, ...apis]
}

/** 根据选中的 key 推断这是 State / variable / api */
export function resolveTargetTypeByKey(
    cond: SpecCondition,
    key: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): SpecTargetType {
    if (key === 'State') return 'state'
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) return 'variable'

    const isVar = tpl.manifest?.ImpactedVariables?.includes(key)
    if (isVar) return 'variable'

    const isApi = (tpl.manifest?.APIs ?? []).some(api => api.Name === key)
    if (isApi) return 'api'

    return 'variable'
}

/** 关系运算符选项 */
export function getRelationOptions(cond: SpecCondition) {
    if (cond.targetType === 'state') return ['in', 'not in']
    if (cond.targetType === 'variable') return ['>=', '>', '<=', '<', '==', '!=']
    return ['happens']
}

/** value 下拉选项（State / API 对应的枚举值） */
export function getValueOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
) {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) return []
    if (cond.targetType === 'state') {
        return (tpl.manifest?.WorkingStates ?? []).map(ws => ws.Name)
    }
    if (cond.targetType === 'api') {
        return (tpl.manifest?.APIs ?? []).map(api => api.Name)
    }
    return []
}
