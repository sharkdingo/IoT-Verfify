import type { DeviceNode } from '../types/node'
import type {
    SpecSide,
    SpecCondition,
    SpecTemplateId,
    Specification
} from '../types/spec'
import type { DeviceTemplate } from '../types/device'
import { specTemplateDetails } from '../assets/config/specTemplates'
import { normalizeModelRelation } from './modelRequest'

interface SpecFormulaContext {
    nodes?: DeviceNode[]
    deviceTemplates?: DeviceTemplate[]
}

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
    const target = String(n.templateName || '').trim().toLowerCase()
    return templates.find(t => {
        const names = [t.name, t.manifest?.Name]
            .map(name => String(name || '').trim().toLowerCase())
            .filter(Boolean)
        return names.includes(target)
    })
}

/* =========================================
 * 目标字段（Target）逻辑
 * =======================================*/

/**
 * 获取“属性/API”下拉框的选项
 * 返回值必须跟后端/NuSMV 语义一致：
 * - state 固定使用 key=state
 * - api 只能使用 Signal=true 的 API
 * - trust/privacy use propertyScope + a user-domain mode/variable key
 */
export function getTargetOptions(
    cond: SpecCondition,
    nodes: DeviceNode[],
    templates: DeviceTemplate[]
) {
    const tpl = getTemplateByNodeId(cond.deviceId, nodes, templates)
    if (!tpl || !tpl.manifest) {
        return [{ label: 'State', value: 'state' }]
    }

    const manifest = tpl.manifest

    if (cond.targetType === 'state') {
        return [{ label: 'State', value: 'state' }]
    }

    if (cond.targetType === 'mode') {
        return (manifest.Modes || [])
            .filter(Boolean)
            .map(mode => ({ label: mode, value: mode }))
    }

    if (cond.targetType === 'api') {
        return (manifest.APIs || [])
            .filter(api => api?.Name && api.Signal === true)
            .map(api => ({ label: api.Name, value: api.Name }))
    }

    const variableOptions = (manifest.InternalVariables || [])
        .filter(iv => iv?.Name)
        .map(iv => ({ label: iv.Name, value: iv.Name }))

    if (cond.targetType === 'variable') {
        return variableOptions
    }

    const modes = manifest.Modes || []
    const statePropertyOptions = modes.filter(Boolean).map(mode => ({
        label: modes.length === 1 ? 'Current state' : `Current ${mode} state`,
        value: mode,
        propertyScope: 'state' as const
    }))
    const variablePropertyOptions = variableOptions.map(option => ({
        ...option,
        propertyScope: 'variable' as const
    }))

    return [...statePropertyOptions, ...variablePropertyOptions]
}


/* =========================================
 * 描述生成 (Natural Language)
 * =======================================*/

const describeCondition = (c: SpecCondition): string => {
    const device = c.deviceLabel || c.deviceId || '<?>'
    const target = c.targetType === 'state'
        ? 'state'
        : (c.targetType === 'trust' || c.targetType === 'privacy') && c.propertyScope === 'state'
            ? `current ${c.key} state`
            : c.key || ''

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

const previewQuote = (value: unknown): string =>
    JSON.stringify(String(value ?? '?'))

const previewDevice = (condition: SpecCondition, context?: SpecFormulaContext): string => {
    const currentLabel = context?.nodes?.find(node => node.id === condition.deviceId)?.label
    const label = String(currentLabel || condition.deviceLabel || '').trim()
    return previewQuote(label || 'Unknown device')
}

const previewManifest = (
    condition: SpecCondition,
    context?: SpecFormulaContext
): DeviceTemplate['manifest'] | undefined => {
    if (!context?.nodes || !context.deviceTemplates) return undefined
    return getTemplateByNodeId(condition.deviceId, context.nodes, context.deviceTemplates)?.manifest
}

const previewVariableTarget = (condition: SpecCondition, context?: SpecFormulaContext): string => {
    const key = String(condition.key || '').trim()
    const variable = (previewManifest(condition, context)?.InternalVariables || [])
        .find(candidate => candidate?.Name === key)
    return variable?.IsInside === false
        ? `Environment.${previewQuote(key)}`
        : `${previewDevice(condition, context)}.${previewQuote(key)}`
}

const previewConditionTarget = (condition: SpecCondition, context?: SpecFormulaContext): string => {
    const device = previewDevice(condition, context)
    const key = previewQuote(String(condition.key || '').trim())
    switch (condition.targetType) {
        case 'state':
            return `${device}.state`
        case 'variable':
            return previewVariableTarget(condition, context)
        case 'api':
            return `actionEvent(${device}, ${key})`
        case 'trust': {
            const source = condition.propertyScope === 'state'
                ? `${device}.current ${key} state`
                : previewVariableTarget(condition, context)
            return `controlSource(${source})`
        }
        case 'privacy': {
            const source = condition.propertyScope === 'state'
                ? `${device}.current ${key} state`
                : previewVariableTarget(condition, context)
            return `sensitivity(${source})`
        }
        default:
            return `${device}.${key}`
    }
}

const previewScalar = (value: unknown): string => {
    const text = String(value ?? '').trim()
    if (/^-?\d+(?:\.\d+)?$/.test(text)) return text
    if (/^(?:true|false|trusted|untrusted|public|private)$/i.test(text)) return text.toLowerCase()
    return previewQuote(text)
}

const previewConditionValue = (condition: SpecCondition, relation: string): string => {
    if (relation !== 'in' && relation !== 'not in') return previewScalar(condition.value)
    const delimiter = condition.targetType === 'state' ? /[,|]/ : /[,;|]/
    const values = String(condition.value || '')
        .split(delimiter)
        .map(value => value.trim())
        .filter(Boolean)
        .map(previewScalar)
    return `{${values.join(', ')}}`
}

const conditionToFormulaTerm = (condition: SpecCondition, context?: SpecFormulaContext): string => {
    if (!condition?.deviceId || !condition.key) return ''
    const target = previewConditionTarget(condition, context)
    if (condition.targetType === 'api') return target
    const relation = normalizeModelRelation(condition.relation) || '='
    return `${target} ${relation} ${previewConditionValue(condition, relation)}`
}

const conditionGroupToFormula = (conditions: SpecCondition[] = [], context?: SpecFormulaContext): string => {
    const terms = conditions.map(condition => conditionToFormulaTerm(condition, context)).filter(Boolean)
    return terms.length > 0 ? terms.join(' AND ') : 'TRUE'
}

const conditionGroupToSafetyBody = (conditions: SpecCondition[] = [], context?: SpecFormulaContext): string => {
    const conditionTerms = conditions.map(condition => conditionToFormulaTerm(condition, context)).filter(Boolean)
    const untrustedSources = conditions.map(condition => {
        const source = previewConditionTarget(condition, context)
        return source ? `controlSource(${source}) = untrusted` : ''
    }).filter(Boolean)
    if (conditionTerms.length === 0) return 'TRUE'
    const sourceTerm = untrustedSources.length > 1
        ? `(${untrustedSources.join(' OR ')})`
        : untrustedSources[0] || 'untrustedSource(unknown)'
    return `${conditionTerms.join(' AND ')} AND ${sourceTerm}`
}

export const buildSpecFormula = (spec: Pick<Specification,
    'templateId' | 'templateLabel' | 'aConditions' | 'ifConditions' | 'thenConditions'>,
    context?: SpecFormulaContext): string => {
    const template = specTemplateDetails.find(t => t.id === spec.templateId)
    if (!template) return spec.templateLabel || 'Unknown specification'

    const aPart = conditionGroupToFormula(spec.aConditions || [], context)
    const ifPart = conditionGroupToFormula(spec.ifConditions || [], context)
    const thenPart = conditionGroupToFormula(spec.thenConditions || [], context)

    switch (template.type) {
        case 'always':
            return `CTL AG(${aPart})`
        case 'eventually':
            return `CTL AF(${aPart})`
        case 'never':
            return `CTL AG NOT (${aPart})`
        case 'immediate':
            return `CTL AG((${ifPart}) -> AX(${thenPart}))`
        case 'response':
            return `CTL AG((${ifPart}) -> AF(${thenPart}))`
        case 'persistence':
            return `LTL G((${ifPart}) -> F G(${thenPart}))`
        case 'safety':
            return `CTL AG NOT (${conditionGroupToSafetyBody(spec.aConditions || [], context)})`
        default:
            return template.formulaPreview
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
    if ((c.targetType === 'trust' || c.targetType === 'privacy')
        && !['state', 'variable'].includes(c.propertyScope || '')) return false
    if (c.targetType !== 'trust' && c.targetType !== 'privacy' && c.propertyScope) return false

    // API 条件表示 signal API 被触发；保存/建模时会固定为 "= TRUE"。
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

const normalizeSpecificationSetValue = (
    value: unknown,
    relation: string,
    targetType: string
): string => {
    const normalized = String(value ?? '').trim()
    if (targetType === 'api') return normalized.toUpperCase()
    if (relation !== 'in' && relation !== 'not in') return normalized
    const delimiter = targetType === 'state' ? /[,|]/ : /[,;|]/
    return normalized.split(delimiter).map(part => part.trim()).filter(Boolean).sort().join(',')
}

const specificationConditionKeys = (conditions: SpecCondition[] = []): string[] =>
    conditions.map(condition => {
        const targetType = String(condition.targetType || '').trim().toLowerCase()
        const relation = normalizeModelRelation(condition.relation) || String(condition.relation || '').trim()
        return JSON.stringify({
            deviceId: String(condition.deviceId || '').trim(),
            targetType,
            propertyScope: String(condition.propertyScope || '').trim().toLowerCase(),
            key: String(condition.key || '').trim(),
            relation,
            value: normalizeSpecificationSetValue(condition.value, relation, targetType)
        })
    }).sort()

export const buildSpecificationSemanticKey = (specification: Pick<
    Specification,
    'templateId' | 'aConditions' | 'ifConditions' | 'thenConditions'
>): string => JSON.stringify({
    templateId: String(specification.templateId ?? '').trim(),
    aConditions: specificationConditionKeys(specification.aConditions),
    ifConditions: specificationConditionKeys(specification.ifConditions),
    thenConditions: specificationConditionKeys(specification.thenConditions)
})

export const isSameSpecification = (a: Specification, b: Specification): boolean =>
    buildSpecificationSemanticKey(a) === buildSpecificationSemanticKey(b)

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
    specs.forEach(s => {
        update(s.aConditions)
        update(s.ifConditions)
        update(s.thenConditions)
        ;(s.devices || []).forEach(d => {
            if (d.deviceId === nodeId && d.deviceLabel !== newLabel) {
                d.deviceLabel = newLabel
                changed = true
            }
        })
    })
    return changed
}

export const isSpecRelatedToNode = (spec: Specification, nodeId: string) => {
    // 检查规约选择的设备
    if (spec.devices && spec.devices.some(d => d.deviceId === nodeId)) return true
    
    // 检查条件中是否包含该设备
    const check = (list: SpecCondition[]) => list && list.length > 0 && list.some(c => c.deviceId === nodeId)
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
