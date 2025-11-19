// src/utils/spec.ts
import type {
    SpecSide,
    SpecCondition,
    SpecTargetType,
    SpecTemplateId,
    Specification,
    DeviceNode
} from '../types/board'
import type { DeviceTemplate } from '../types/device'
import { getTemplateByNodeId } from './boardLayout'

/* =========================================
 * 小常量：关系运算符选项（避免魔法字符串）
 * =======================================*/

const STATE_RELATIONS = ['in', 'not in'] as const
const VARIABLE_RELATIONS = ['>=', '>', '<=', '<', '==', '!='] as const
const API_RELATIONS = [''] as const

/* =========================================
 * 条件创建 & 模式判断
 * =======================================*/

/**
 * 创建一个空条件（A / IF / THEN 通用）
 */
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

/**
 * 根据模板 id 判断当前是单 A 规约还是 IF/THEN 规约
 * - 1,2,3,7 => single
 * - 4,5,6   => ifThen
 */
export function getSpecMode(templateId: SpecTemplateId | ''): 'single' | 'ifThen' {
    if (!templateId) return 'single'
    const num = Number(templateId)
    return num >= 4 && num !== 7 ? 'ifThen' : 'single'
}

/* =========================================
 * 目标字段（State / 变量 / API）相关
 * =======================================*/

/**
 * A/B 里的第二个下拉：State / 变量 / API 列表
 */
export function getTargetOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
) {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) {
        // 没找到模板时至少给一个 State
        return [{ label: 'State', value: 'State' }]
    }

    const vars =
        tpl.manifest?.ImpactedVariables?.map(v => ({ label: v, value: v })) ?? []

    const apis =
        tpl.manifest?.APIs?.map(api => ({ label: api.Name, value: api.Name })) ?? []

    return [{ label: 'State', value: 'State' }, ...vars, ...apis]
}

/**
 * 根据选中的 key 推断 targetType（state / variable / api）
 */
export function resolveTargetTypeByKey(
    cond: SpecCondition,
    key: string,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): SpecTargetType {
    if (key === 'State') return 'state'

    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) return 'variable' // 保守处理

    const isVar = tpl.manifest?.ImpactedVariables?.includes(key)
    if (isVar) return 'variable'

    const isApi = (tpl.manifest?.APIs ?? []).some(api => api.Name === key)
    if (isApi) return 'api'

    // 兜底：当成普通变量处理
    return 'variable'
}

/* =========================================
 * 关系运算符 & 值枚举
 * =======================================*/

/**
 * 关系运算符选项
 */
export function getRelationOptions(cond: SpecCondition): string[] {
    if (cond.targetType === 'state') return [...STATE_RELATIONS]
    if (cond.targetType === 'variable') return [...VARIABLE_RELATIONS]
    // api
    return [...API_RELATIONS]
}

/**
 * value 下拉选项（State / API 对应的枚举值）
 */
export function getValueOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
): string[] {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl) return []

    if (cond.targetType === 'state') {
        return (tpl.manifest?.WorkingStates ?? []).map(ws => ws.Name)
    }
    if (cond.targetType === 'api') {
        // 当前你的逻辑是让 API 也能选具体的 API 名作为 value
        return (tpl.manifest?.APIs ?? []).map(api => api.Name)
    }
    // variable：自由输入，不提供枚举
    return []
}

/* =========================================
 * 规约转自然语言（StatusPanel / DeviceDialog 共用）
 * =======================================*/

/**
 * 把单个条件转成一个短语：
 *  - state：   'AC_Cooler' state in 'Working'
 *  - variable：'AC_Cooler' temp >= '25'
 *  - api：     'AC_Cooler' Turn_On happens
 */
const describeCondition = (c: SpecCondition): string => {
    const device = c.deviceLabel || c.deviceId || '<?>'

    const target =
        c.targetType === 'state'
            ? 'state'
            : c.key || '' // variable / api 都用 key 展示

    const relation = c.relation || ''

    // value 可能为空（例如 api happens 时），则不加引号
    const value = c.value?.trim()
    const valuePart = value ? ` '${value}'` : ''

    return `'${device}' ${target} ${relation}${valuePart}`
}

/**
 * 根据 templateId 把整条规约串成一句英文描述
 * 与 StatusPanel / DeviceDialog 中展示逻辑保持一致
 */
export const buildSpecText = (spec: Specification): string => {
    const aPart = spec.aConditions.map(describeCondition).join(' and ')
    const ifPart = spec.ifConditions.map(describeCondition).join(' and ')
    const thenPart = spec.thenConditions.map(describeCondition).join(' and ')

    const ensureNonEmpty = (text: string) =>
        text && text.trim().length > 0 ? text : spec.templateLabel

    switch (spec.templateId) {
        case '1':
            // A holds forever
            return ensureNonEmpty(aPart ? `${aPart} holds forever` : '')
        case '2':
            // A will happen later
            return ensureNonEmpty(aPart ? `${aPart} will happen later` : '')
        case '3':
            // A never happens
            return ensureNonEmpty(aPart ? `${aPart} never happens` : '')
        case '4':
            // IF A happens, B should happen at the same time
            return ensureNonEmpty(
                ifPart && thenPart
                    ? `If ${ifPart} happens, then ${thenPart} should happen at the same time`
                    : ''
            )
        case '5':
            // IF A happens, B should happen later
            return ensureNonEmpty(
                ifPart && thenPart
                    ? `If ${ifPart} happens, then ${thenPart} should happen later`
                    : ''
            )
        case '6':
            // IF A happens, B should happen later and last forever
            return ensureNonEmpty(
                ifPart && thenPart
                    ? `If ${ifPart} happens, then ${thenPart} should happen later and last forever`
                    : ''
            )
        case '7':
            // A will not happen because of something untrusted
            return ensureNonEmpty(
                aPart ? `${aPart} will not happen because of something untrusted` : ''
            )
        default:
            return spec.templateLabel
    }
}

/* =========================================
 * 条件完整性校验：空行 / 半残行 / 完整行
 * =======================================*/

/**
 * 一行条件是否“完全空”
 * 只看用户真正会改动的字段：
 * - 没选设备
 * - 没选 key（State / 变量 / API）
 * - 没填 value
 * relation 默认值（例如 'in'）不算“有内容”
 */
export const isEmptyCondition = (c: SpecCondition): boolean => {
    const hasDevice = !!c.deviceId
    const hasKey = !!c.key
    const hasValue = !!(c.value && c.value.toString().trim())
    // 只要三者都是空，就认为这一行是“完全空白”，可以被忽略
    return !hasDevice && !hasKey && !hasValue
}

/**
 * 一行条件是否“完整”
 * 与表单渲染逻辑严格对应：
 *  - API：device + targetType = 'api' + key 即可
 *  - state / variable：还必须有 relation + value
 */
export const isCompleteCondition = (c: SpecCondition): boolean => {
    if (isEmptyCondition(c)) return false
    // 没选设备 / 类型 / 目标键，一定不完整
    if (!c.deviceId || !c.targetType || !c.key) return false
    // ① API：设备 + 类型(api) + key 就够了
    if (c.targetType === 'api') {
        return true
    }
    // ② state / variable：还必须要有 relation + value
    if (c.targetType === 'state' || c.targetType === 'variable') {
        return !!c.relation && !!(c.value && c.value.toString().trim())
    }
    // 其他未知类型，一律当不完整处理（防御性）
    return false
}

/**
 * 对某一侧（A / IF / THEN）的条件做校验并去掉“完全空”的行
 * - 完全空行：丢弃
 * - 非空但不完整：标记 hasIncomplete = true
 * - 完整：进入 cleaned
 */
export const validateAndCleanConditions = (
    conds: SpecCondition[]
): { cleaned: SpecCondition[]; hasIncomplete: boolean } => {
    const cleaned: SpecCondition[] = []
    let hasIncomplete = false
    for (const c of conds) {
        if (isEmptyCondition(c)) {
            // 完全空行 → 直接忽略
            continue
        }
        if (!isCompleteCondition(c)) {
            // 有内容，但没填完 → 整体标记为不完整
            hasIncomplete = true
            break
        }
        cleaned.push(c)
    }
    return { cleaned, hasIncomplete }
}

/**
 * 比较两条规约在“模板 + 条件列表”维度上是否完全相同
 */
export const isSameSpecification = (a: Specification, b: Specification): boolean => {
    if (a.templateId !== b.templateId) return false

    const sameCondArray = (xs: SpecCondition[], ys: SpecCondition[]) => {
        if (xs.length !== ys.length) return false
        return xs.every((c, i) => {
            const d = ys[i]
            return (
                c.side === d.side &&
                c.deviceId === d.deviceId &&
                c.deviceLabel === d.deviceLabel &&
                c.targetType === d.targetType &&
                c.key === d.key &&
                c.relation === d.relation &&
                String(c.value) === String(d.value)
            )
        })
    }

    return (
        sameCondArray(a.aConditions, b.aConditions) &&
        sameCondArray(a.ifConditions, b.ifConditions) &&
        sameCondArray(a.thenConditions, b.thenConditions)
    )
}
