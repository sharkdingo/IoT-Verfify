import type { DeviceNode } from '../types/node'
import type {
    SpecCondition,
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

function getTemplateByNodeId(
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

export const isSpecRelatedToNode = (spec: Specification, nodeId: string) => {
    // 检查规约选择的设备
    if (spec.devices && spec.devices.some(d => d.deviceId === nodeId)) return true
    
    // 检查条件中是否包含该设备
    const check = (list: SpecCondition[]) => list && list.length > 0 && list.some(c => c.deviceId === nodeId)
    return check(spec.aConditions) || check(spec.ifConditions) || check(spec.thenConditions)
}

/**
 * Collapse a specification's conditions into its distinct device references.
 *
 * A specification stores one entry per referenced device, accumulating the `api` keys that its
 * conditions select. `lookupNodes` supplies labels for readability only; the `deviceId` is the
 * authoritative identity, so an unknown node degrades to showing the id rather than dropping
 * the reference.
 */
export function buildSpecDeviceRefsFromConditions(
    conditions: SpecCondition[],
    lookupNodes: DeviceNode[]
) {
    const byDevice = new Map<string, { deviceId: string; deviceLabel: string; selectedApis: string[] }>()
    conditions.forEach(condition => {
        if (!condition.deviceId) return
        const existing = byDevice.get(condition.deviceId)
        if (existing) {
            if (condition.targetType === 'api' && condition.key && !existing.selectedApis.includes(condition.key)) {
                existing.selectedApis.push(condition.key)
            }
            return
        }
        const node = lookupNodes.find(candidate => candidate.id === condition.deviceId)
        byDevice.set(condition.deviceId, {
            deviceId: condition.deviceId,
            deviceLabel: condition.deviceLabel || node?.label || condition.deviceId,
            selectedApis: condition.targetType === 'api' && condition.key ? [condition.key] : []
        })
    })
    return Array.from(byDevice.values())
}
