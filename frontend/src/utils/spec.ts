import type { DeviceNode } from '../types/node'
import type {
    SpecSide,
    SpecCondition,
    SpecTargetType,
    SpecTemplateId,
    Specification
} from '../types/spec'
import type { DeviceTemplate } from '../types/device'

/* =========================================
 * 小常量：关系运算符选项
 * =======================================*/

const STATE_RELATIONS = ['in', 'not in'] as const
// 数值型关系
const NUMERIC_RELATIONS = ['>=', '>', '<=', '<', '==', '!='] as const
/* =========================================
 * 条件创建 & 模式判断
 * =======================================*/

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

export function getSpecMode(templateId: SpecTemplateId | '' | null): 'single' | 'ifThen' | null {
    if (!templateId) return null
    const num = Number(templateId)
    // 假设 1,2,3,7 是单句，4,5,6 是 IF/THEN
    return num >= 4 && num !== 7 ? 'ifThen' : 'single'
}

export function getTemplateByNodeId(
    nodeId: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): DeviceTemplate | undefined {
    const n = nodes.find(n => n.id === nodeId)
    if (!n) return undefined
    return templates.find(t => t.manifest.Name === n.templateName)
}

/* =========================================
 * 目标字段（Target）逻辑
 * =======================================*/

/**
 * 获取“属性/API”下拉框的选项
 * 包括：'State'、ImpactedVariables、InternalVariables、APIs
 */
export function getTargetOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
) {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl || !tpl.manifest) {
        return [{ label: 'State', value: 'State' }]
    }

    const options = [{ label: 'State', value: 'State' }]

    // 1. Impacted Variables (String[])
    if (Array.isArray(tpl.manifest.ImpactedVariables)) {
        tpl.manifest.ImpactedVariables.forEach(v => {
            options.push({ label: v, value: v })
        })
    }

    // 2. [New] Internal Variables (Object[]) -> 提取 Name
    if (Array.isArray(tpl.manifest.InternalVariables)) {
        tpl.manifest.InternalVariables.forEach(iv => {
            if (iv.Name) {
                options.push({ label: iv.Name, value: iv.Name })
            }
        })
    }

    // 3. APIs
    if (Array.isArray(tpl.manifest.APIs)) {
        tpl.manifest.APIs.forEach(api => {
            if (api.Name) {
                options.push({ label: `${api.Name}`, value: api.Name })
            }
        })
    }

    return options
}


/* =========================================
 * 描述生成 (Natural Language)
 * =======================================*/

const describeCondition = (c: SpecCondition): string => {
    const device = c.deviceLabel || c.deviceId || '<?>'
    const target = c.targetType === 'state' ? 'state' : c.key || ''

    // 优化 API 显示
    if (c.targetType === 'api') {
        return `'${device}' executes '${target}'`
    }

    const relation = c.relation || ''
    const value = c.value?.trim()
    const valuePart = value ? ` '${value}'` : ''

    return `'${device}' ${target} ${relation}${valuePart}`
}

export const buildSpecText = (spec: Specification): string => {
    const aPart = spec.aConditions.map(describeCondition).join(' and ')
    const ifPart = spec.ifConditions.map(describeCondition).join(' and ')
    const thenPart = spec.thenConditions.map(describeCondition).join(' and ')

    const ensureNonEmpty = (text: string) =>
        text && text.trim().length > 0 ? text : spec.templateLabel

    switch (spec.templateId) {
        case '1': return ensureNonEmpty(aPart ? `${aPart} holds forever` : '')
        case '2': return ensureNonEmpty(aPart ? `${aPart} will happen later` : '')
        case '3': return ensureNonEmpty(aPart ? `${aPart} never happens` : '')
        case '4': return ensureNonEmpty(ifPart && thenPart ? `If ${ifPart}, then ${thenPart} immediately` : '')
        case '5': return ensureNonEmpty(ifPart && thenPart ? `If ${ifPart}, then ${thenPart} later` : '')
        case '6': return ensureNonEmpty(ifPart && thenPart ? `If ${ifPart}, then ${thenPart} later and forever` : '')
        case '7': return ensureNonEmpty(aPart ? `${aPart} fails due to untrusted` : '')
        default: return spec.templateLabel
    }
}

/* =========================================
 * 校验与清洗
 * =======================================*/

export const isEmptyCondition = (c: SpecCondition): boolean => {
    return !c.deviceId && !c.key && (!c.value || !c.value.toString().trim())
}

export const isCompleteCondition = (c: SpecCondition): boolean => {
    if (isEmptyCondition(c)) return false
    if (!c.deviceId || !c.targetType || !c.key) return false

    // API 只需要选了 key 就算完整
    if (c.targetType === 'api') return true

    // State / Variable 需要 relation 和 value
    return !!c.relation && !!(c.value && c.value.toString().trim())
}

export const validateAndCleanConditions = (
    conds: SpecCondition[]
): { cleaned: SpecCondition[]; hasIncomplete: boolean } => {
    const cleaned: SpecCondition[] = []
    let hasIncomplete = false
    for (const c of conds) {
        if (isEmptyCondition(c)) continue
        if (!isCompleteCondition(c)) {
            hasIncomplete = true
            break
        }
        cleaned.push(c)
    }
    return { cleaned, hasIncomplete }
}

export const isSameSpecification = (a: Specification, b: Specification): boolean => {
    if (a.templateId !== b.templateId) return false
    const sameConds = (xs: SpecCondition[], ys: SpecCondition[]) => {
        if (xs.length !== ys.length) return false
        return xs.every((x, i) => {
            const y = ys[i]
            return x.deviceId === y.deviceId &&
                x.key === y.key &&
                x.relation === y.relation &&
                x.value === y.value
        })
    }
    return sameConds(a.aConditions, b.aConditions) &&
        sameConds(a.ifConditions, b.ifConditions) &&
        sameConds(a.thenConditions, b.thenConditions)
}

export const updateSpecsForNodeRename = (
    specs: Specification[],
    nodeId: string,
    newLabel: string
): boolean => {
    let changed = false
    const update = (list: SpecCondition[]) => {
        list.forEach(c => {
            if (c.deviceId === nodeId && c.deviceLabel !== newLabel) {
                c.deviceLabel = newLabel
                changed = true
            }
        })
    }
    specs.forEach(s => { update(s.aConditions); update(s.ifConditions); update(s.thenConditions) })
    return changed
}

export const isSpecRelatedToNode = (spec: Specification, nodeId: string) => {
    const check = (list: SpecCondition[]) => list.some(c => c.deviceId === nodeId)
    return check(spec.aConditions) || check(spec.ifConditions) || check(spec.thenConditions)
}

export const removeSpecsForNode = (
    specs: Specification[],
    nodeId: string,
): { nextSpecs: Specification[]; removed: Specification[] } => {
    const next: Specification[] = []
    const removed: Specification[] = []
    specs.forEach(s => {
        if (isSpecRelatedToNode(s, nodeId)) removed.push(s)
        else next.push(s)
    })
    return { nextSpecs: next, removed }
}