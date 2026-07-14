import type { DeviceTemplate } from '@/types/device'
import type { DeviceNode } from '@/types/node'
import type { RuleForm } from '@/types/rule'

export interface BoardAttackSurface {
  effectfulDeviceIds: Set<string>
  devicePointCount: number
  automationLinkPointCount: number
  totalPointCount: number
}

export type AttackSelectionIssue = 'NO_MODELED_EFFECT' | 'INVALID_BUDGET'

/** Validate a selected run option without rewriting the user's form state. */
export const getAttackSelectionIssue = (
  enabled: boolean,
  budget: unknown,
  maximum: number
): AttackSelectionIssue | null => {
  if (!enabled) return null
  if (!Number.isInteger(maximum) || maximum < 1) return 'NO_MODELED_EFFECT'
  if (typeof budget !== 'number' || !Number.isInteger(budget) || budget < 1 || budget > maximum) {
    return 'INVALID_BUDGET'
  }
  return null
}

/** Count only compromise choices that can change generated-model behavior. */
export const analyzeBoardAttackSurface = (
  nodes: DeviceNode[],
  rules: RuleForm[],
  resolveTemplate: (node: DeviceNode) => DeviceTemplate | null | undefined
): BoardAttackSurface => {
  const existingDeviceIds = new Set(nodes.map(node => node.id))
  const effectfulDeviceIds = new Set<string>()

  for (const rule of rules) {
    if (existingDeviceIds.has(rule.toId)) effectfulDeviceIds.add(rule.toId)
  }

  for (const node of nodes) {
    const hasFalsifiableReading = (resolveTemplate(node)?.manifest?.InternalVariables || [])
      .some(variable => variable.FalsifiableWhenCompromised === true)
    if (hasFalsifiableReading) effectfulDeviceIds.add(node.id)
  }

  const devicePointCount = effectfulDeviceIds.size
  const automationLinkPointCount = rules.length
  return {
    effectfulDeviceIds,
    devicePointCount,
    automationLinkPointCount,
    totalPointCount: devicePointCount + automationLinkPointCount
  }
}
