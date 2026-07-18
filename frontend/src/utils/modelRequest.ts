import type { DeviceTemplate } from '@/types/device'
import type { ModelEnvironmentVariable } from '@/types/model'
import type { DeviceNode } from '@/types/node'
import type { RuleForm, RuleSourceItemType } from '@/types/rule'
import type { Specification } from '@/types/spec'
import type { VerificationRequest } from '@/types/verify'
import type { SimulationRequest } from '@/types/simulation'
import type { AttackScenario } from '@/types/attackScenario'

interface ModelRequestBase {
  nodes: DeviceNode[]
  deviceTemplates: DeviceTemplate[]
  environmentVariables?: ModelEnvironmentVariable[]
  rules: RuleForm[]
  attackScenario?: AttackScenario
  /** @deprecated Test/helper compatibility; new callers must provide attackScenario. */
  isAttack?: boolean
  /** @deprecated Test/helper compatibility; new callers must provide attackScenario. */
  attackBudget?: number
  enablePrivacy: boolean
}

const NUSMV_RESERVED_WORDS = new Set([
  'module', 'var', 'ivar', 'frozenvar', 'define', 'constants', 'assign',
  'init', 'trans', 'invar', 'invars', 'spec', 'ctlspec', 'ltlspec',
  'fairness', 'compassion', 'justice', 'isa', 'fun', 'pred',
  'mirror', 'invarspec', 'compute',
  'case', 'esac', 'next', 'self',
  'true', 'false', 'boolean', 'integer', 'word', 'signed', 'unsigned',
  'process', 'array', 'of', 'mod', 'union', 'in', 'xor', 'xnor',
  'abs', 'max', 'min', 'count', 'toint', 'typeof',
  'swconst', 'wordconst', 'uwconst', 'resize', 'extend',
  'signed_word', 'unsigned_word',
  'ex', 'ax', 'ef', 'af', 'eg', 'ag',
  'e', 'f', 'o', 'g', 'h', 'x', 'y', 'z', 'w', 'a', 'u', 's', 'v', 't',
  'bu', 'ebf', 'abf', 'ebg', 'abg'
])

export const normalizeNuSmvDeviceName = (name: string): string => {
  if (!name) return name
  let normalized = name.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase()
  if (!normalized || /^_+$/.test(normalized)) normalized = 'device_0'
  if (/^\d/.test(normalized)) normalized = `_${normalized}`
  return NUSMV_RESERVED_WORDS.has(normalized) ? `_${normalized}` : normalized
}

export const normalizeNuSmvValue = (value: string): string => {
  if (!value) return value
  if (/^"\d+"$/.test(value) || /^'\d+'$/.test(value)) {
    return value.replace(/^["']|["']$/g, '')
  }
  return value
}

export const normalizeModelRelation = (relation?: string | null): string | undefined => {
  if (relation === null || relation === undefined) return undefined
  const trimmed = String(relation).trim()
  if (!trimmed) return undefined

  switch (trimmed.toUpperCase()) {
    case 'EQ':
    case '==':
      return '='
    case 'NEQ':
    case '!=':
      return '!='
    case 'GT':
      return '>'
    case 'GTE':
      return '>='
    case 'LT':
      return '<'
    case 'LTE':
      return '<='
    case 'IN':
      return 'in'
    case 'NOT_IN':
    case 'NOT IN':
      return 'not in'
    default:
      return trimmed
  }
}

const hasModelConditionValue = (value: unknown) => {
  if (value === null || value === undefined) return false
  if (typeof value === 'string') return value.trim() !== ''
  return true
}

const VALUE_BASED_RULE_SOURCE_TYPES = new Set<RuleSourceItemType>(['variable', 'mode', 'state'])

const resolveDeviceVarName = (deviceId?: string | null): string =>
  normalizeNuSmvDeviceName(String(deviceId || ''))

const requireRuleSourceType = (type?: RuleSourceItemType): RuleSourceItemType => {
  if (!type) {
    throw new Error('Rule condition targetType is required')
  }
  return type
}

const requireValueBasedRuleSource = (source: any, sourceType: RuleSourceItemType) => {
  if (!source.relation || !hasModelConditionValue(source.value)) {
    throw new Error(`Rule ${sourceType} condition requires relation and value`)
  }
  return {
    relation: normalizeModelRelation(source.relation) || String(source.relation),
    value: normalizeNuSmvValue(String(source.value))
  }
}

const findTemplateForNode = (node: DeviceNode, deviceTemplates: DeviceTemplate[]) => {
  const target = String(node.templateName || '').trim().toLowerCase()
  if (!target) return undefined
  return deviceTemplates.find(template => {
    const names = [template.name, template.manifest?.Name]
      .map(name => String(name || '').trim().toLowerCase())
      .filter(Boolean)
    return names.includes(target)
  })
}

const isEnvironmentTemplateVariable = (variable?: { IsInside?: boolean } | null) =>
  !!variable && variable.IsInside !== true

const findTemplateVariable = (template: DeviceTemplate | undefined, variableName?: string | null) => {
  const name = String(variableName || '').trim()
  if (!name) return undefined
  return (template?.manifest?.InternalVariables || []).find(variable => variable?.Name === name)
}

const localNodeVariables = (node: DeviceNode, template: DeviceTemplate | undefined) => {
  const variables = Array.isArray((node as any).variables)
    ? (node as any).variables
    : undefined
  if (!variables || !template?.manifest?.InternalVariables) return variables
  return variables.filter((variable: any) =>
    !isEnvironmentTemplateVariable(findTemplateVariable(template, variable?.name)))
}

const localNodePrivacies = (node: DeviceNode, template: DeviceTemplate | undefined) => {
  const privacies = Array.isArray((node as any).privacies)
    ? (node as any).privacies
    : undefined
  if (!privacies || !template?.manifest?.InternalVariables) return privacies
  return privacies.filter((privacy: any) =>
    !isEnvironmentTemplateVariable(findTemplateVariable(template, privacy?.name)))
}

const buildDevices = (nodes: DeviceNode[], deviceTemplates: DeviceTemplate[]) => {
  return nodes
    .map(node => {
      const template = findTemplateForNode(node, deviceTemplates)
      const manifest = template?.manifest

      const variables = localNodeVariables(node, template)
      const privacies = localNodePrivacies(node, template)

      const hasModes = Array.isArray(manifest?.Modes)
        && manifest.Modes.length > 0
        && Array.isArray(manifest?.WorkingStates)
        && manifest.WorkingStates.length > 0

      return {
        varName: resolveDeviceVarName(node.id),
        deviceLabel: node.label || node.id,
        templateName: node.templateName,
        state: hasModes ? node.state : undefined,
        currentStateTrust: hasModes ? (node as any).currentStateTrust : undefined,
        currentStatePrivacy: hasModes ? (node as any).currentStatePrivacy : undefined,
        ...(variables && variables.length > 0 ? { variables } : {}),
        ...(privacies && privacies.length > 0 ? { privacies } : {})
      }
    })
}

const persistedRuleId = (rawId?: string): number | undefined => {
  if (!rawId || !/^\d+$/.test(rawId.trim())) return undefined
  const parsed = Number(rawId)
  return Number.isSafeInteger(parsed) && parsed > 0 ? parsed : undefined
}

const buildRules = (rules: RuleForm[]) => {
  return rules.map(rule => ({
    ...(persistedRuleId(rule.id) !== undefined ? { id: persistedRuleId(rule.id) } : {}),
    conditions: (rule.sources || []).map(source => {
      const sourceType = requireRuleSourceType(source.itemType)
      const shouldSendRelation = VALUE_BASED_RULE_SOURCE_TYPES.has(sourceType)
      const valueCondition = shouldSendRelation
        ? requireValueBasedRuleSource(source, sourceType)
        : null
      return {
        deviceName: resolveDeviceVarName(source.fromId),
        attribute: sourceType === 'state' ? 'state' : (source.fromApi || ''),
        targetType: sourceType,
        relation: valueCondition?.relation,
        value: valueCondition?.value
      }
    }),
    command: {
      deviceName: resolveDeviceVarName(rule.toId),
      action: rule.toApi || '',
      contentDevice: rule.contentDevice
        ? resolveDeviceVarName(rule.contentDevice)
        : null,
      content: rule.content || null
    },
    ruleString: rule.name || ''
  }))
}

const buildSpecs = (specifications: Specification[]) => {
  const resolveConditionRef = (ref: string | null | undefined) =>
    ref ? resolveDeviceVarName(ref) : ref

  const mapCondition = (condition: any) => ({
    ...condition,
    deviceId: resolveConditionRef(condition.deviceId),
    relation: condition.targetType === 'api'
      ? (normalizeModelRelation(condition.relation) || '=')
      : (normalizeModelRelation(condition.relation) || condition.relation),
    value: normalizeNuSmvValue(
      condition.targetType === 'api' && !hasModelConditionValue(condition.value)
        ? 'TRUE'
        : hasModelConditionValue(condition.value)
          ? String(condition.value)
          : ''
    )
  })

  return specifications.map(spec => ({
    ...spec,
    devices: (spec.devices || []).map(device => ({
      ...device,
      deviceId: resolveConditionRef(device.deviceId) || ''
    })),
    aConditions: (spec.aConditions || []).map(mapCondition),
    ifConditions: (spec.ifConditions || []).map(mapCondition),
    thenConditions: (spec.thenConditions || []).map(mapCondition)
  }))
}

const buildEnvironmentVariables = (environmentVariables?: ModelEnvironmentVariable[]) =>
  (environmentVariables || [])
    .map((variable, index) => {
      const name = String(variable?.name || '').trim()
      if (!name) {
        throw new Error(`Environment variable ${index + 1} requires a name; it was not omitted from the model request`)
      }
      return {
        name,
        value: variable.value === null || variable.value === undefined
          ? null
          : normalizeNuSmvValue(String(variable.value).trim()),
        trust: variable.trust ? String(variable.trust).trim() : null,
        privacy: variable.privacy ? String(variable.privacy).trim() : null
      }
    })

const buildAttackScenario = (attackScenario: AttackScenario): AttackScenario => {
  if (attackScenario.mode === 'NONE') {
    return { mode: 'NONE', budget: 0, points: [] }
  }
  if (attackScenario.mode === 'ANY_UP_TO_BUDGET') {
    return {
      mode: 'ANY_UP_TO_BUDGET',
      budget: attackScenario.budget,
      points: []
    }
  }
  return {
    mode: 'EXACT_POINTS',
    points: (attackScenario.points || []).map(point => point.kind === 'DEVICE'
      ? { kind: 'DEVICE' as const, deviceId: resolveDeviceVarName(point.deviceId) }
      : { kind: 'AUTOMATION_LINK' as const, ruleId: point.ruleId })
  }
}

const resolveAttackScenario = (params: ModelRequestBase): AttackScenario =>
  params.attackScenario || (params.isAttack
    ? { mode: 'ANY_UP_TO_BUDGET', budget: params.attackBudget, points: [] }
    : { mode: 'NONE', budget: 0, points: [] })

export const buildVerificationRequestPayload = (
  params: ModelRequestBase & { specifications: Specification[] }
): VerificationRequest => ({
  devices: buildDevices(params.nodes, params.deviceTemplates),
  environmentVariables: buildEnvironmentVariables(params.environmentVariables),
  rules: buildRules(params.rules),
  specs: buildSpecs(params.specifications),
  attackScenario: buildAttackScenario(resolveAttackScenario(params)),
  enablePrivacy: params.enablePrivacy
})

export const buildSimulationRequestPayload = (
  params: ModelRequestBase & { steps: number }
): SimulationRequest => ({
  devices: buildDevices(params.nodes, params.deviceTemplates),
  environmentVariables: buildEnvironmentVariables(params.environmentVariables),
  rules: buildRules(params.rules),
  steps: params.steps,
  attackScenario: buildAttackScenario(resolveAttackScenario(params)),
  enablePrivacy: params.enablePrivacy
})

const canonicalizeModelValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(canonicalizeModelValue)
  if (!value || typeof value !== 'object') return value
  return Object.keys(value as Record<string, unknown>)
    .sort()
    .reduce<Record<string, unknown>>((result, key) => {
      const nested = (value as Record<string, unknown>)[key]
      if (nested !== undefined) result[key] = canonicalizeModelValue(nested)
      return result
    }, {})
}

/**
 * Local comparison only. The server remains authoritative for the captured snapshot; this signature
 * lets the current tab warn when its board changed while a run was in flight.
 */
export const buildModelRunSignature = (
  request: VerificationRequest | SimulationRequest,
  deviceTemplates: DeviceTemplate[]
): string => {
  const referencedNames = new Set(request.devices
    .map(device => String(device.templateName || '').trim().toLowerCase())
    .filter(Boolean))
  const templates = deviceTemplates
    .filter(template => {
      const aliases = [template.name, template.manifest?.Name]
        .map(name => String(name || '').trim().toLowerCase())
        .filter(Boolean)
      return aliases.some(alias => referencedNames.has(alias))
    })
    .map(template => ({
      name: String(template.name || template.manifest?.Name || '').trim().toLowerCase(),
      manifest: template.manifest
    }))
    .sort((left, right) => left.name.localeCompare(right.name))

  return JSON.stringify(canonicalizeModelValue({ request, templates }))
}
