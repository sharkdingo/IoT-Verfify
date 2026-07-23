import type { DeviceEdge } from '@/types/edge'
import { normalizeNuSmvDeviceName } from './modelRequest'

export type TraceVariableLike = {
  name: string
  value?: unknown
  trust?: string
}

export type TraceTrustPrivacyLike = {
  name: string
  propertyScope?: 'state' | 'variable' | 'content'
  mode?: string
  trust?: boolean | null
  privacy?: string
}

export type TraceDeviceLike = {
  deviceId?: string | null
  deviceLabel?: string | null
  state?: string | null
  mode?: string | null
  compromised?: boolean | null
  variables?: TraceVariableLike[]
  trustPrivacy?: TraceTrustPrivacyLike[]
  privacies?: TraceTrustPrivacyLike[]
}

export type TraceStateLike = {
  devices?: TraceDeviceLike[]
  envVariables?: TraceVariableLike[]
  triggeredRules?: Array<{ ruleIndex: number; ruleId?: string | null; ruleLabel?: string | null }>
  compromisedAutomationLinks?: Array<{ ruleIndex: number; ruleId?: string | null; ruleLabel?: string | null }>
}

export type TracePlaybackLike = {
  states?: TraceStateLike[]
  selectedStateIndex?: number
} | null | undefined

export const toTraceDeviceId = (nodeId: string): string =>
  normalizeNuSmvDeviceName(nodeId).toLowerCase()

export const traceDeviceMatchesId = (device: { deviceId?: string | null }, nodeId: string): boolean =>
  !!device.deviceId && device.deviceId.toLowerCase() === toTraceDeviceId(nodeId)

export const normalizeTraceComparable = (value: unknown) =>
  String(value ?? '').trim()

export const formatRuleApiSignalName = (raw: string): string => {
  const cleaned = String(raw ?? '').replace(/[^a-zA-Z0-9_]/g, '_')
  return cleaned.trim() ? `${cleaned}_a` : String(raw ?? '')
}

const normalizeTraceVariableName = (name: string) =>
  normalizeNuSmvDeviceName(name).toLowerCase()

const traceDeviceNameCandidates = (name: string) => {
  const raw = String(name || '').trim().toLowerCase()
  const normalized = normalizeTraceVariableName(name)
  return new Set([
    raw,
    normalized
  ].filter(Boolean))
}

const traceEnvironmentNameCandidates = (name: string) => {
  const raw = String(name || '').trim().toLowerCase()
  const normalized = normalizeTraceVariableName(name)
  return new Set([
    raw,
    normalized
  ].filter(Boolean))
}

export const traceVariableMatchesName = (variable: TraceVariableLike, name: string) => {
  const variableLower = variable.name.toLowerCase()
  const normalizedVariableLower = normalizeTraceVariableName(variable.name)
  const candidates = traceDeviceNameCandidates(name)
  return candidates.has(variableLower) || candidates.has(normalizedVariableLower)
}

export const traceEnvironmentVariableMatchesName = (variable: TraceVariableLike, name: string) => {
  const variableLower = variable.name.toLowerCase()
  const normalizedVariableLower = normalizeTraceVariableName(variable.name)
  const candidates = traceEnvironmentNameCandidates(name)
  return candidates.has(variableLower) || candidates.has(normalizedVariableLower)
}

const splitTraceComparableParts = (value: string) =>
  value
    .split(/[;,]/)
    .map(item => item.trim())
    .filter(Boolean)

export const traceValueEquals = (actualText: string, expectedText: string): boolean => {
  const actualLower = actualText.toLowerCase()
  const expectedLower = expectedText.toLowerCase()
  if (actualLower === expectedLower) return true
  return splitTraceComparableParts(actualText)
    .some(part => part.toLowerCase() === expectedLower)
}

export const compareTraceValue = (actual: unknown, relation: string | undefined, expected: unknown): boolean => {
  const actualText = normalizeTraceComparable(actual)
  const expectedText = normalizeTraceComparable(expected)
  const normalizedRelation = relation || '='
  const actualNumber = Number(actualText)
  const expectedNumber = Number(expectedText)
  const bothNumeric = Number.isFinite(actualNumber) && Number.isFinite(expectedNumber)
  const expectedSet = expectedText
    .split(',')
    .map(item => item.trim())
    .filter(Boolean)

  switch (normalizedRelation) {
    case '=':
    case '==':
    case 'EQ':
      return traceValueEquals(actualText, expectedText)
    case '!=':
    case 'NEQ':
      return !traceValueEquals(actualText, expectedText)
    case '>':
    case 'GT':
      return bothNumeric && actualNumber > expectedNumber
    case '>=':
    case 'GTE':
      return bothNumeric && actualNumber >= expectedNumber
    case '<':
    case 'LT':
      return bothNumeric && actualNumber < expectedNumber
    case '<=':
    case 'LTE':
      return bothNumeric && actualNumber <= expectedNumber
    case 'in':
      return expectedSet.some(item => item.toLowerCase() === actualText.toLowerCase())
    case 'not in':
    case 'not_in':
      return !expectedSet.some(item => item.toLowerCase() === actualText.toLowerCase())
    default:
      return traceValueEquals(actualText, expectedText)
  }
}

export const findTraceVariableAtOrBefore = (
  trace: TracePlaybackLike,
  nodeId: string,
  variableName: string,
  endIndex: number
): TraceVariableLike | null => {
  if (!trace?.states?.length) return null
  const boundedIndex = Math.min(Math.max(endIndex, 0), trace.states.length - 1)

  for (let i = boundedIndex; i >= 0; i--) {
    const state = trace.states[i]
    if (!state?.devices) continue
    const device = state.devices.find(d => traceDeviceMatchesId(d, nodeId))
    const variable = device?.variables?.find(v => traceVariableMatchesName(v, variableName))
    if (variable) return variable
  }
  return null
}

export const findTraceEnvironmentVariableAtOrBefore = (
  trace: TracePlaybackLike,
  variableName: string,
  endIndex: number
): TraceVariableLike | null => {
  if (!trace?.states?.length) return null
  const boundedIndex = Math.min(Math.max(endIndex, 0), trace.states.length - 1)

  for (let i = boundedIndex; i >= 0; i--) {
    const state = trace.states[i]
    if (!state?.envVariables) continue
    const variable = state.envVariables.find(v => traceEnvironmentVariableMatchesName(v, variableName))
    if (variable) return variable
  }
  return null
}

const getLatestTraceDeviceForNodeAtOrBefore = (
  trace: TracePlaybackLike,
  nodeId: string,
  endIndex: number
): TraceDeviceLike | null => {
  if (!trace?.states?.length) return null
  const boundedIndex = Math.min(Math.max(endIndex, 0), trace.states.length - 1)
  for (let i = boundedIndex; i >= 0; i--) {
    const state = trace.states[i]
    if (!state?.devices) continue
    const device = state.devices.find(d => traceDeviceMatchesId(d, nodeId))
    if (device) return device
  }
  return null
}

const getLatestTraceStateAtOrBefore = (
  trace: TracePlaybackLike,
  nodeId: string,
  endIndex: number
): string | null =>
  getLatestTraceDeviceForNodeAtOrBefore(trace, nodeId, endIndex)?.state || null

export const getTraceValueForEdge = (
  edge: DeviceEdge,
  trace: TracePlaybackLike,
  stateIndex = trace?.selectedStateIndex || 0
): string | null => {
  const traceDevice = getLatestTraceDeviceForNodeAtOrBefore(trace, edge.from, stateIndex)
  if (edge.itemType === 'state') {
    return traceDevice?.state || getLatestTraceStateAtOrBefore(trace, edge.from, stateIndex)
  }
  if (edge.itemType === 'mode') {
    if (edge.fromApi) {
      const modeVariable = findTraceVariableAtOrBefore(trace, edge.from, edge.fromApi, stateIndex)
      if (modeVariable) return normalizeTraceComparable(modeVariable.value)
    }
    return traceDevice?.mode || traceDevice?.state || getLatestTraceStateAtOrBefore(trace, edge.from, stateIndex)
  }
  if (edge.fromApi && edge.itemType === 'variable') {
    const variable = findTraceVariableAtOrBefore(trace, edge.from, edge.fromApi, stateIndex)
    if (variable) return normalizeTraceComparable(variable.value)

    const environmentVariable = findTraceEnvironmentVariableAtOrBefore(trace, edge.fromApi, stateIndex)
    return environmentVariable ? normalizeTraceComparable(environmentVariable.value) : null
  }
  if (edge.fromApi && edge.itemType === 'api') {
    const directSignal = findTraceVariableAtOrBefore(trace, edge.from, edge.fromApi, stateIndex)
    if (directSignal) return normalizeTraceComparable(directSignal.value)
    const generatedSignal = findTraceVariableAtOrBefore(
      trace,
      edge.from,
      formatRuleApiSignalName(edge.fromApi),
      stateIndex
    )
    if (generatedSignal) return normalizeTraceComparable(generatedSignal.value)
  }
  return null
}

const hasValue = (value?: string | null) =>
  value !== null && value !== undefined && String(value).trim() !== ''

export const isEdgeConditionSatisfied = (
  edge: DeviceEdge,
  trace: TracePlaybackLike,
  stateIndex = trace?.selectedStateIndex || 0
): boolean => {
  if (!trace?.states || trace.selectedStateIndex === undefined || trace.selectedStateIndex < 0) return false
  const actual = getTraceValueForEdge(edge, trace, stateIndex)
  if (actual === null || actual === undefined) return false
  if (!hasValue(edge.value) && edge.itemType === 'api') {
    return traceValueEquals(normalizeTraceComparable(actual), 'TRUE')
  }
  return compareTraceValue(actual, edge.relation || '=', edge.value)
}

export const getTraceEdgeEvaluationIndex = (trace: TracePlaybackLike) => {
  const selectedIndex = trace?.selectedStateIndex ?? 0
  return selectedIndex > 0 ? selectedIndex - 1 : selectedIndex
}

type FrozenRuleIdentity = {
  ruleIndex: number
  ruleId?: string | null
}

const edgeMatchesFrozenRule = (
  edge: DeviceEdge,
  allEdges: DeviceEdge[],
  frozenRule: FrozenRuleIdentity
): boolean => {
  if (!edge.ruleId || frozenRule.ruleId == null || !Number.isSafeInteger(edge.ruleIndex)) {
    return false
  }
  if (String(edge.ruleId) !== String(frozenRule.ruleId)) return false

  const currentIndexes = new Set<number>()
  for (const candidate of allEdges) {
    if (candidate.ruleId == null || String(candidate.ruleId) !== String(edge.ruleId)) continue
    if (!Number.isSafeInteger(candidate.ruleIndex)) return false
    currentIndexes.add(candidate.ruleIndex as number)
  }
  return currentIndexes.size === 1 && currentIndexes.has(edge.ruleIndex as number)
}

export const isEdgeActiveInTrace = (
  edge: DeviceEdge,
  allEdges: DeviceEdge[],
  trace: TracePlaybackLike
): boolean => {
  if (!trace?.states || trace.selectedStateIndex === undefined || trace.selectedStateIndex < 0) return false
  const triggeredRules = trace.states[trace.selectedStateIndex]?.triggeredRules
  if (!Array.isArray(triggeredRules)) return false
  return triggeredRules.some(rule => edgeMatchesFrozenRule(edge, allEdges, rule))
}

export const isEdgeCompromisedInTrace = (
  edge: DeviceEdge,
  allEdges: DeviceEdge[],
  trace: TracePlaybackLike
): boolean => {
  if (!trace?.states || trace.selectedStateIndex === undefined || trace.selectedStateIndex < 0) return false
  const compromisedLinks = trace.states[trace.selectedStateIndex]?.compromisedAutomationLinks
  if (!Array.isArray(compromisedLinks)) return false
  return compromisedLinks.some(rule => edgeMatchesFrozenRule(edge, allEdges, rule))
}

export const shouldAnimateEdgeFlow = (
  edge: DeviceEdge,
  allEdges: DeviceEdge[],
  trace: TracePlaybackLike
): boolean => {
  if (!trace?.states || trace.selectedStateIndex === undefined || trace.selectedStateIndex < 0) {
    return false
  }
  return isEdgeActiveInTrace(edge, allEdges, trace)
    && !isEdgeCompromisedInTrace(edge, allEdges, trace)
}
