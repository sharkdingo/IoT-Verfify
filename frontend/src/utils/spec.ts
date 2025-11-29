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

/**
 * 根据选中的 key 推断 targetType
 */
export function resolveTargetTypeByKey(
    cond: SpecCondition,
    key: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): SpecTargetType {
    if (key === 'State') return 'state'

    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl || !tpl.manifest) return 'variable'

    // 检查是否是 API
    const isApi = (tpl.manifest.APIs || []).some(api => api.Name === key)
    if (isApi) return 'api'

    // 默认为变量 (无论是 Impacted 还是 Internal)
    return 'variable'
}

/* =========================================
 * 关系运算符 & 值选项
 * =======================================*/

/**
 * 获取关系运算符
 * [优化] 根据变量类型（是否枚举）返回不同的运算符
 */
export function getRelationOptions(cond: SpecCondition): string[] {
    if (cond.targetType === 'state') return [...STATE_RELATIONS]
    if (cond.targetType === 'api') return [''] // API 通常不需要关系符，或者用 'happens'

    // Variable 类型：尝试判断是否为枚举
    // 注意：这里需要传入更多上下文才能精确判断，暂且根据是否能获取到 values 来判断
    // 但 getRelationOptions 在 UI 中通常是直接调用的。
    // 为了简单起见，变量默认给所有运算符。如果要做精细控制，需要重构调用处传入 context。
    // 这里我们返回全集，由用户自己选。
    return [...NUMERIC_RELATIONS]
}

/**
 * 获取 Value 下拉框的选项
 * [New] 支持从 InternalVariable.Values 中提取枚举值
 */
export function getValueOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): string[] {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl || !tpl.manifest) return []

    // 1. State: 返回 WorkingStates
    if (cond.targetType === 'state') {
        return (tpl.manifest.WorkingStates || []).map(ws => ws.Name)
    }

    // 2. Variable: 检查是否有定义好的枚举值 (InternalVariables)
    if (cond.targetType === 'variable') {
        const iv = (tpl.manifest.InternalVariables || []).find(v => v.Name === cond.key)
        if (iv && Array.isArray(iv.Values) && iv.Values.length > 0) {
            return iv.Values
        }
        // ImpactedVariables 通常没有定义 Values，返回空数组（前端显示输入框）
    }

    // 3. API: 之前逻辑是让 API 选 API 名？通常 API 不需要 value，除非是参数
    // 这里保持兼容，返回空
    return []
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