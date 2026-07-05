import type { DeviceTemplate } from '@/types/device'
import type { DeviceNode } from '@/types/node'
import type { RuleForm } from '@/types/rule'
import type { Specification } from '@/types/spec'
import type { VerificationRequest } from '@/types/verify'
import type { SimulationRequest } from '@/types/simulation'

type ResolveNodeLabel = (refValue?: string | null) => string

interface ModelRequestBase {
  nodes: DeviceNode[]
  deviceTemplates: DeviceTemplate[]
  rules: RuleForm[]
  resolveNodeLabel: ResolveNodeLabel
  isAttack: boolean
  intensity: number
  enablePrivacy: boolean
}

export const normalizeNuSmvDeviceName = (name: string): string => {
  if (!name) return name
  return /^\d/.test(name) ? `d_${name}` : name
}

export const normalizeNuSmvValue = (value: string): string => {
  if (!value) return value
  if (/^"\d+"$/.test(value) || /^'\d+'$/.test(value)) {
    return value.replace(/^["']|["']$/g, '')
  }
  return value
}

const buildDevices = (nodes: DeviceNode[], deviceTemplates: DeviceTemplate[]) => {
  return nodes
    .filter(node => !node.templateName.startsWith('variable_'))
    .map(node => {
      const template = deviceTemplates.find(t => t.manifest?.Name === node.templateName)
      const manifest = template?.manifest

      let variables = (node as any).variables || []
      if ((!variables || variables.length === 0) && manifest?.InternalVariables) {
        variables = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          value: v.Default || '0',
          trust: 'trusted'
        }))
      }

      let privacies = (node as any).privacies || []
      if ((!privacies || privacies.length === 0) && manifest?.InternalVariables) {
        privacies = manifest.InternalVariables.map((v: any) => ({
          name: v.Name,
          privacy: v.Privacy || 'public'
        }))
      }

      return {
        varName: normalizeNuSmvDeviceName(node.label),
        templateName: node.templateName,
        state: node.state,
        currentStateTrust: (node as any).currentStateTrust || 'trusted',
        variables,
        privacies
      }
    })
}

const buildRules = (rules: RuleForm[], resolveNodeLabel: ResolveNodeLabel) => {
  return rules.map(rule => ({
    conditions: (rule.sources || []).map(source => ({
      deviceName: normalizeNuSmvDeviceName(resolveNodeLabel(source.fromId)),
      attribute: source.fromApi || '',
      relation: source.relation || '=',
      value: normalizeNuSmvValue(source.value || 'true')
    })),
    command: {
      deviceName: normalizeNuSmvDeviceName(resolveNodeLabel(rule.toId)),
      action: rule.toApi || '',
      contentDevice: null,
      content: null
    },
    ruleString: rule.name || ''
  }))
}

const buildSpecs = (specifications: Specification[], resolveNodeLabel: ResolveNodeLabel) => {
  // Specs may come from older saved boards where condition.deviceId is a canvas node id
  // rather than the display label used as the NuSMV varName. Resolve both fields through
  // the same ref helper before applying the digit-leading d_ convention, so verification
  // and simulation snapshots line up with backend DeviceReferenceResolver.
  const resolveConditionRef = (ref: string | null | undefined) =>
    ref ? normalizeNuSmvDeviceName(resolveNodeLabel(ref)) : ref

  const mapCondition = (condition: any) => ({
    ...condition,
    deviceId: resolveConditionRef(condition.deviceId),
    deviceLabel: resolveConditionRef(condition.deviceLabel),
    value: normalizeNuSmvValue(condition.value || '')
  })

  return specifications.map(spec => ({
    ...spec,
    aConditions: (spec.aConditions || []).map(mapCondition),
    ifConditions: (spec.ifConditions || []).map(mapCondition),
    thenConditions: (spec.thenConditions || []).map(mapCondition)
  }))
}

export const buildVerificationRequestPayload = (
  params: ModelRequestBase & { specifications: Specification[] }
): VerificationRequest => ({
  devices: buildDevices(params.nodes, params.deviceTemplates),
  rules: buildRules(params.rules, params.resolveNodeLabel),
  specs: buildSpecs(params.specifications, params.resolveNodeLabel),
  isAttack: params.isAttack,
  intensity: params.intensity,
  enablePrivacy: params.enablePrivacy
})

export const buildSimulationRequestPayload = (
  params: ModelRequestBase & { steps: number }
): SimulationRequest => ({
  devices: buildDevices(params.nodes, params.deviceTemplates),
  rules: buildRules(params.rules, params.resolveNodeLabel),
  steps: params.steps,
  isAttack: params.isAttack,
  intensity: params.intensity,
  enablePrivacy: params.enablePrivacy
})
