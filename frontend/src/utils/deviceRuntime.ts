import type { DeviceTemplate, InternalVariable, WorkingState } from '@/types/device'
import type { DeviceNode } from '@/types/node'

export const TRUST_OPTIONS = ['trusted', 'untrusted'] as const
export const PRIVACY_OPTIONS = ['public', 'private'] as const

export type TrustValue = typeof TRUST_OPTIONS[number]
export type PrivacyValue = typeof PRIVACY_OPTIONS[number]

export interface DeviceRuntimeConfig {
  state?: string
  currentStateTrust?: string
  currentStatePrivacy?: string
  variables?: DeviceNode['variables']
  privacies?: DeviceNode['privacies']
}

type DeviceRuntimeSource = Omit<DeviceRuntimeConfig,
  'currentStateTrust' | 'currentStatePrivacy'> & {
    currentStateTrust?: string | null
    currentStatePrivacy?: string | null
  }

export interface DeviceRuntimeDraft {
  state: string
  currentStateTrust: string
  currentStatePrivacy: string
  variables: Record<string, string>
  variableTrusts: Record<string, string>
  privacies: Record<string, string>
}

export interface BuildDeviceRuntimeConfigOptions {
  includeEmptyCollections?: boolean
  variableScope?: 'all' | 'local' | 'environment'
}

export interface ValidateDeviceRuntimeConfigOptions {
  variableScope?: 'all' | 'local' | 'environment'
}

type Translate = (key: string, params?: Record<string, unknown>) => string

export const normalizeRuntimeValue = (value: unknown) => String(value ?? '').trim()

export const createDeviceRuntimeDraft = (): DeviceRuntimeDraft => ({
  state: '',
  currentStateTrust: '',
  currentStatePrivacy: '',
  variables: {},
  variableTrusts: {},
  privacies: {}
})

export const getTemplateWorkingStates = (template?: DeviceTemplate | null): WorkingState[] =>
  Array.isArray(template?.manifest?.WorkingStates)
    ? template.manifest.WorkingStates.filter(state => normalizeRuntimeValue(state?.Name))
    : []

export const getTemplateInternalVariables = (template?: DeviceTemplate | null): InternalVariable[] =>
  Array.isArray(template?.manifest?.InternalVariables)
    ? template.manifest.InternalVariables.filter(variable => normalizeRuntimeValue(variable?.Name))
    : []

export const isTemplateLocalVariable = (variable: InternalVariable) =>
  variable.IsInside === true

export const isTemplateEnvironmentVariable = (variable: InternalVariable) =>
  variable.IsInside !== true

export const getTemplateLocalVariables = (template?: DeviceTemplate | null): InternalVariable[] =>
  getTemplateInternalVariables(template).filter(isTemplateLocalVariable)

export const getTemplateEnvironmentVariables = (template?: DeviceTemplate | null): InternalVariable[] =>
  getTemplateInternalVariables(template).filter(isTemplateEnvironmentVariable)

const getScopedTemplateVariables = (
  template: DeviceTemplate,
  scope: 'all' | 'local' | 'environment' = 'all'
) => {
  if (scope === 'local') return getTemplateLocalVariables(template)
  if (scope === 'environment') return getTemplateEnvironmentVariables(template)
  return getTemplateInternalVariables(template)
}

export const findTemplateStateTrust = (
  template: DeviceTemplate | null | undefined,
  stateName: string
) => {
  const state = getTemplateWorkingStates(template).find(item => item.Name === stateName)
  return state?.Trust || ''
}

export const findTemplateStatePrivacy = (
  template: DeviceTemplate | null | undefined,
  stateName: string
) => {
  const state = getTemplateWorkingStates(template).find(item => item.Name === stateName)
  return state?.Privacy || ''
}

export const templateVariableHasEnumValues = (variable: InternalVariable) =>
  Array.isArray(variable.Values) && variable.Values.length > 0

export const templateVariableUsesNumericBounds = (variable: InternalVariable) =>
  variable.LowerBound !== undefined && variable.LowerBound !== null
  || variable.UpperBound !== undefined && variable.UpperBound !== null

export const getTemplateVariableDefaultValue = (variable: InternalVariable): string => {
  if (templateVariableHasEnumValues(variable)) return String(variable.Values![0])
  if (variable.LowerBound !== undefined && variable.LowerBound !== null) {
    return String(variable.LowerBound)
  }
  return ''
}

export const resetDeviceRuntimeDraft = (
  draft: DeviceRuntimeDraft,
  template?: DeviceTemplate | null
) => {
  const states = getTemplateWorkingStates(template)
  draft.state = template?.manifest?.InitState || states[0]?.Name || ''
  draft.currentStateTrust = ''
  draft.currentStatePrivacy = ''
  draft.variables = {}
  draft.variableTrusts = {}
  draft.privacies = {}

  getTemplateInternalVariables(template).forEach(variable => {
    const name = variable.Name
    draft.variables[name] = getTemplateVariableDefaultValue(variable)
    draft.variableTrusts[name] = ''
    draft.privacies[name] = ''
  })
}

export const buildDeviceRuntimeConfig = (
  template: DeviceTemplate,
  runtime: DeviceRuntimeDraft,
  options: BuildDeviceRuntimeConfigOptions = {}
): DeviceRuntimeConfig | undefined => {
  const config: DeviceRuntimeConfig = {}
  const hasModes = Array.isArray(template.manifest?.Modes)
    && template.manifest.Modes.length > 0
    && getTemplateWorkingStates(template).length > 0

  if (hasModes && normalizeRuntimeValue(runtime.state)) {
    config.state = normalizeRuntimeValue(runtime.state)
    const requestedTrust = normalizeRuntimeValue(runtime.currentStateTrust).toLowerCase()
    const requestedPrivacy = normalizeRuntimeValue(runtime.currentStatePrivacy).toLowerCase()
    if (requestedTrust) config.currentStateTrust = requestedTrust
    if (requestedPrivacy) config.currentStatePrivacy = requestedPrivacy
  }

  const scopedVariables = getScopedTemplateVariables(template, options.variableScope)

  const variables = scopedVariables
    .map(variable => {
      const name = variable.Name
      const value = normalizeRuntimeValue(runtime.variables[name])
      if (!value) return null
      const requestedTrust = normalizeRuntimeValue(runtime.variableTrusts[name]).toLowerCase()
      return { name, value, ...(requestedTrust ? { trust: requestedTrust } : {}) }
    })
    .filter((item): item is { name: string, value: string, trust?: string } => Boolean(item))

  if (variables.length > 0 || (options.includeEmptyCollections && scopedVariables.length > 0)) {
    config.variables = variables
  }

  const privacies = scopedVariables
    .map(variable => {
      const name = variable.Name
      const requestedPrivacy = normalizeRuntimeValue(runtime.privacies[name]).toLowerCase()
      return requestedPrivacy ? { name, privacy: requestedPrivacy } : null
    })
    .filter((item): item is { name: string, privacy: string } => Boolean(item))

  if (privacies.length > 0 || (options.includeEmptyCollections && scopedVariables.length > 0)) {
    config.privacies = privacies
  }

  return Object.keys(config).length > 0 ? config : undefined
}

export const materializeDeviceRuntimeConfig = (
  template: DeviceTemplate,
  runtime?: DeviceRuntimeSource,
  options: BuildDeviceRuntimeConfigOptions = {}
): DeviceRuntimeConfig | undefined => {
  const draft = createDeviceRuntimeDraft()
  resetDeviceRuntimeDraft(draft, template)

  if (runtime?.state !== undefined) draft.state = normalizeRuntimeValue(runtime.state)
  if (runtime?.currentStateTrust !== undefined) {
    draft.currentStateTrust = normalizeRuntimeValue(runtime.currentStateTrust).toLowerCase()
  }
  if (runtime?.currentStatePrivacy !== undefined) {
    draft.currentStatePrivacy = normalizeRuntimeValue(runtime.currentStatePrivacy).toLowerCase()
  }
  for (const variable of runtime?.variables || []) {
    draft.variables[variable.name] = normalizeRuntimeValue(variable.value)
    if (variable.trust !== undefined) {
      draft.variableTrusts[variable.name] = normalizeRuntimeValue(variable.trust).toLowerCase()
    }
  }
  for (const privacy of runtime?.privacies || []) {
    draft.privacies[privacy.name] = normalizeRuntimeValue(privacy.privacy).toLowerCase()
  }

  return buildDeviceRuntimeConfig(template, draft, options)
}

export const deviceRuntimeConfigsEqual = (
  template: DeviceTemplate,
  left: DeviceRuntimeSource | undefined,
  right: DeviceRuntimeSource | undefined,
  options: BuildDeviceRuntimeConfigOptions = {}
) => JSON.stringify(materializeDeviceRuntimeConfig(template, left, options))
  === JSON.stringify(materializeDeviceRuntimeConfig(template, right, options))

export const validateDeviceRuntimeConfig = (
  template: DeviceTemplate,
  runtime: DeviceRuntimeConfig | undefined,
  t: Translate,
  options: ValidateDeviceRuntimeConfigOptions = {}
) => {
  if (!runtime) return ''

  const states = getTemplateWorkingStates(template).map(state => state.Name)
  const hasModes = Array.isArray(template.manifest?.Modes)
    && template.manifest.Modes.length > 0
    && states.length > 0
  if (runtime.state && hasModes && states.length > 0 && !states.includes(runtime.state)) {
    return t('app.deviceImportInvalidState', { state: runtime.state })
  }
  if (runtime.state && !hasModes && runtime.state.toLowerCase() !== 'working') {
    return t('app.deviceImportStateWithoutModes')
  }
  if (!hasModes && runtime.currentStateTrust) {
    return t('app.deviceImportStateTrustWithoutModes')
  }
  if (!hasModes && runtime.currentStatePrivacy) {
    return t('app.deviceImportStatePrivacyWithoutModes')
  }
  if (runtime.currentStateTrust && !TRUST_OPTIONS.includes(runtime.currentStateTrust as TrustValue)) {
    return t('app.deviceImportInvalidTrust', { value: runtime.currentStateTrust })
  }
  if (runtime.currentStatePrivacy && !PRIVACY_OPTIONS.includes(runtime.currentStatePrivacy as PrivacyValue)) {
    return t('app.deviceImportInvalidPrivacy', { value: runtime.currentStatePrivacy })
  }

  const variableMap = new Map(getScopedTemplateVariables(template, options.variableScope).map(variable => [variable.Name, variable]))
  const allVariableMap = new Map(getTemplateInternalVariables(template).map(variable => [variable.Name, variable]))
  const seenVariables = new Set<string>()
  for (const variable of runtime.variables || []) {
    const manifestVariable = variableMap.get(variable.name)
    if (seenVariables.has(variable.name)) {
      return t('app.deviceImportDuplicateVariable', { name: variable.name })
    }
    seenVariables.add(variable.name)
    if (!manifestVariable) {
      const unscopedVariable = allVariableMap.get(variable.name)
      if (options.variableScope === 'local' && unscopedVariable && isTemplateEnvironmentVariable(unscopedVariable)) {
        return t('app.deviceImportEnvironmentVariableNotDeviceRuntime', { name: variable.name })
      }
      return t('app.deviceImportInvalidVariable', { name: variable.name })
    }
    if (variable.trust && !TRUST_OPTIONS.includes(variable.trust as TrustValue)) {
      return t('app.deviceImportInvalidTrust', { value: variable.trust })
    }
    if (templateVariableHasEnumValues(manifestVariable)
      && !manifestVariable.Values!.map(String).includes(String(variable.value))) {
      return t('app.deviceImportInvalidVariableValue', { name: variable.name, value: variable.value })
    }
    if (templateVariableUsesNumericBounds(manifestVariable)) {
      const numericValue = Number(variable.value)
      if (!Number.isFinite(numericValue)) {
        return t('app.deviceImportInvalidVariableValue', { name: variable.name, value: variable.value })
      }
      if (manifestVariable.LowerBound !== undefined && numericValue < manifestVariable.LowerBound) {
        return t('app.deviceImportInvalidVariableValue', { name: variable.name, value: variable.value })
      }
      if (manifestVariable.UpperBound !== undefined && numericValue > manifestVariable.UpperBound) {
        return t('app.deviceImportInvalidVariableValue', { name: variable.name, value: variable.value })
      }
    }
  }

  const seenPrivacies = new Set<string>()
  for (const privacy of runtime.privacies || []) {
    if (seenPrivacies.has(privacy.name)) {
      return t('app.deviceImportDuplicatePrivacy', { name: privacy.name })
    }
    seenPrivacies.add(privacy.name)
    if (!variableMap.has(privacy.name)) {
      const unscopedVariable = allVariableMap.get(privacy.name)
      if (options.variableScope === 'local' && unscopedVariable && isTemplateEnvironmentVariable(unscopedVariable)) {
        return t('app.deviceImportEnvironmentVariableNotDeviceRuntime', { name: privacy.name })
      }
      return t('app.deviceImportInvalidPrivacyTarget', { name: privacy.name })
    }
    if (!PRIVACY_OPTIONS.includes(privacy.privacy as PrivacyValue)) {
      return t('app.deviceImportInvalidPrivacy', { value: privacy.privacy })
    }
  }

  return ''
}
