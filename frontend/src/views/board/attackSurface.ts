import type { DeviceTemplate } from '@/types/device'
import type { DeviceNode } from '@/types/node'
import type { RuleForm } from '@/types/rule'
import type { AttackPoint, AttackScenarioMode } from '@/types/attackScenario'
import { normalizeNuSmvDeviceName } from '@/utils/modelRequest'

export const ATTACK_POINT_HARD_MAX = 50

export interface BoardAttackPointOption {
  key: string
  kind: 'DEVICE' | 'AUTOMATION_LINK'
  deviceId?: string
  ruleId?: number
  label: string
  selectable: boolean
}

export interface BoardAttackSurface {
  effectfulDeviceIds: Set<string>
  devicePointCount: number
  automationLinkPointCount: number
  totalPointCount: number
  points: BoardAttackPointOption[]
}

export type AttackSelectionIssue =
  | 'NO_MODELED_EFFECT'
  | 'INVALID_BUDGET'
  | 'EXPLICIT_POINTS_REQUIRED'
  | 'TOO_MANY_EXPLICIT_POINTS'
  | 'UNAVAILABLE_EXPLICIT_POINT'
  | 'EXHAUSTIVE_NOT_ALLOWED'

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

export const getAttackScenarioIssue = (
  mode: AttackScenarioMode,
  budget: unknown,
  selectedKeys: string[],
  surface: BoardAttackSurface,
  allowExhaustive: boolean
): AttackSelectionIssue | null => {
  if (mode === 'NONE') return null
  if (surface.totalPointCount < 1) return 'NO_MODELED_EFFECT'
  if (mode === 'ANY_UP_TO_BUDGET') {
    if (!allowExhaustive) return 'EXHAUSTIVE_NOT_ALLOWED'
    return getAttackSelectionIssue(true, budget, Math.min(ATTACK_POINT_HARD_MAX, surface.totalPointCount))
  }
  if (selectedKeys.length < 1) return 'EXPLICIT_POINTS_REQUIRED'
  if (selectedKeys.length > ATTACK_POINT_HARD_MAX) return 'TOO_MANY_EXPLICIT_POINTS'
  const pointsByKey = new Map(surface.points.map(point => [point.key, point]))
  if (selectedKeys.some(key => !pointsByKey.get(key)?.selectable)) {
    return 'UNAVAILABLE_EXPLICIT_POINT'
  }
  return null
}

export const selectedAttackPoints = (
  surface: BoardAttackSurface,
  selectedKeys: string[]
): AttackPoint[] => {
  const keys = new Set(selectedKeys)
  return surface.points
    .filter(point => keys.has(point.key) && point.selectable)
    .map(point => point.kind === 'DEVICE'
      ? { kind: 'DEVICE' as const, deviceId: point.deviceId! }
      : { kind: 'AUTOMATION_LINK' as const, ruleId: point.ruleId! })
}

const persistedRuleId = (rawId?: string): number | undefined => {
  if (!rawId || !/^\d+$/.test(rawId.trim())) return undefined
  const parsed = Number(rawId)
  return Number.isSafeInteger(parsed) && parsed > 0 ? parsed : undefined
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
  const devicePoints: BoardAttackPointOption[] = nodes
    .filter(node => effectfulDeviceIds.has(node.id))
    .map(node => ({
      key: `DEVICE:${node.id}`,
      kind: 'DEVICE',
      deviceId: normalizeNuSmvDeviceName(node.id),
      label: node.label || node.id,
      selectable: true
    }))
  const linkPoints: BoardAttackPointOption[] = rules.map((rule, index) => {
    const ruleId = persistedRuleId(rule.id)
    return {
      key: ruleId ? `AUTOMATION_LINK:${ruleId}` : `AUTOMATION_LINK:UNSAVED:${index}`,
      kind: 'AUTOMATION_LINK',
      ruleId,
      label: rule.name || `Rule ${index + 1}`,
      selectable: ruleId !== undefined
    }
  })
  return {
    effectfulDeviceIds,
    devicePointCount,
    automationLinkPointCount,
    totalPointCount: devicePointCount + automationLinkPointCount,
    points: [...devicePoints, ...linkPoints]
  }
}
