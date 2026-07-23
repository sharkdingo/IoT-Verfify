const MODEL_TOKEN_SOURCES = new Set(['BUNDLED', 'CUSTOM', 'UNKNOWN'])
const PROPERTY_SCOPES = new Set(['state', 'variable', 'content'])
const TRUST_VALUES = new Set(['trusted', 'untrusted'])
const PRIVACY_VALUES = new Set(['private', 'public'])

type ContractFailure = (detail: string) => never

interface TraceStateValidationOptions {
  firstStateIndex: 0 | 1
  fail: ContractFailure
}

const record = (
  value: unknown,
  path: string,
  fail: ContractFailure
): Record<string, any> => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    return fail(`${path} must be an object`)
  }
  return value as Record<string, any>
}

const requiredText = (
  value: Record<string, any>,
  field: string,
  path: string,
  fail: ContractFailure,
  allowBlank = false
) => {
  if (typeof value[field] !== 'string' || (!allowBlank && !value[field].trim())) {
    fail(`${path}.${field} must be ${allowBlank ? 'text' : 'non-blank text'}`)
  }
}

const optionalText = (
  value: Record<string, any>,
  field: string,
  path: string,
  fail: ContractFailure,
  allowedValues?: ReadonlySet<string>,
  allowBlank = false
) => {
  const candidate = value[field]
  if (candidate === undefined || candidate === null) return
  if (typeof candidate !== 'string'
    || (allowedValues ? !allowedValues.has(candidate) : (!allowBlank && !candidate.trim()))) {
    fail(`${path}.${field} is invalid`)
  }
}

const optionalArray = (
  value: Record<string, any>,
  field: string,
  path: string,
  fail: ContractFailure
): unknown[] => {
  const candidate = value[field]
  if (candidate === undefined || candidate === null) return []
  if (!Array.isArray(candidate)) fail(`${path}.${field} must be an array when present`)
  return candidate
}

const requiredArray = (
  value: Record<string, any>,
  field: string,
  path: string,
  fail: ContractFailure
): unknown[] => {
  const candidate = value[field]
  if (!Array.isArray(candidate)) fail(`${path}.${field} must be an array`)
  return candidate
}

const validateModelTokenSource = (
  value: Record<string, any>,
  path: string,
  fail: ContractFailure
): string => {
  const source = value.modelTokenSource
  if (typeof source !== 'string' || !MODEL_TOKEN_SOURCES.has(source)) {
    fail(`${path}.modelTokenSource is invalid`)
  }
  return source
}

const validateTraceVariable = (
  value: unknown,
  path: string,
  fail: ContractFailure
): { name: string, modelTokenSource: string } => {
  const variable = record(value, path, fail)
  requiredText(variable, 'name', path, fail)
  requiredText(variable, 'value', path, fail, true)
  optionalText(variable, 'trust', path, fail, TRUST_VALUES)
  return {
    name: variable.name,
    modelTokenSource: validateModelTokenSource(variable, path, fail)
  }
}

const validateTrustPrivacy = (
  value: unknown,
  path: string,
  fail: ContractFailure,
  evidenceKind: 'trust' | 'privacy' | 'either'
) => {
  const entry = record(value, path, fail)
  requiredText(entry, 'name', path, fail)
  if (typeof entry.propertyScope !== 'string' || !PROPERTY_SCOPES.has(entry.propertyScope)) {
    fail(`${path}.propertyScope is invalid`)
  }
  optionalText(entry, 'mode', path, fail)
  if ((entry.propertyScope === 'state') !== (typeof entry.mode === 'string' && Boolean(entry.mode.trim()))) {
    fail(`${path}.mode must be non-blank only for state-scoped entries`)
  }
  if (entry.trust !== undefined && entry.trust !== null && typeof entry.trust !== 'boolean') {
    fail(`${path}.trust must be boolean or null when present`)
  }
  optionalText(entry, 'privacy', path, fail, PRIVACY_VALUES)
  const hasTrust = typeof entry.trust === 'boolean'
  const hasPrivacy = typeof entry.privacy === 'string'
  if (evidenceKind === 'trust' && (!hasTrust || hasPrivacy)) {
    fail(`${path} must contain trust evidence only`)
  }
  if (evidenceKind === 'privacy' && (!hasPrivacy || hasTrust)) {
    fail(`${path} must contain privacy evidence only`)
  }
  if (evidenceKind === 'either' && !hasTrust && !hasPrivacy) {
    fail(`${path} must contain trust or privacy evidence`)
  }
  return `${entry.propertyScope}\u0000${entry.mode ?? ''}\u0000${entry.name}`
}

const validateTrustPrivacyList = (
  values: unknown[],
  path: string,
  fail: ContractFailure,
  evidenceKind: 'trust' | 'privacy' | 'either'
) => {
  const identities = new Set<string>()
  values.forEach((entry, index) => {
    const identity = validateTrustPrivacy(entry, `${path}[${index}]`, fail, evidenceKind)
    if (identities.has(identity)) fail(`${path} must have unique property identities`)
    identities.add(identity)
  })
}

const validateTriggeredRule = (
  value: unknown,
  path: string,
  fail: ContractFailure
): number => {
  const rule = record(value, path, fail)
  if (!Number.isSafeInteger(rule.ruleIndex) || rule.ruleIndex < 0) {
    fail(`${path}.ruleIndex must be a non-negative integer`)
  }
  optionalText(rule, 'ruleId', path, fail)
  optionalText(rule, 'ruleLabel', path, fail, undefined, true)
  return rule.ruleIndex
}

const validateTriggeredRuleList = (
  values: unknown[],
  path: string,
  fail: ContractFailure
) => {
  const indexes = new Set<number>()
  values.forEach((rule, index) => {
    const ruleIndex = validateTriggeredRule(rule, `${path}[${index}]`, fail)
    if (indexes.has(ruleIndex)) fail(`${path} must have unique ruleIndex values`)
    indexes.add(ruleIndex)
  })
}

export const validateTraceStatePayload = (
  value: unknown,
  options: TraceStateValidationOptions
): void => {
  if (!Array.isArray(value) || value.length === 0) {
    options.fail('states must be a non-empty array')
  }

  const frozenDevices = new Map<string, {
    deviceLabel: string
    templateName: string
    modelTokenSource: string
  }>()
  let frozenDeviceIds: Set<string> | null = null
  const frozenDeviceVariableNames = new Map<string, Set<string>>()
  const frozenEnvironmentSources = new Map<string, string>()
  const frozenStateVariableNames = new Map<string, Set<string>>()

  const sameNames = (left: ReadonlySet<string>, right: ReadonlySet<string>) =>
    left.size === right.size && [...left].every(name => right.has(name))

  value.forEach((stateValue: unknown, stateOffset: number) => {
    const statePath = `states[${stateOffset}]`
    const state = record(stateValue, statePath, options.fail)
    const expectedStateIndex = options.firstStateIndex + stateOffset
    if (!Number.isSafeInteger(state.stateIndex) || state.stateIndex !== expectedStateIndex) {
      options.fail(`${statePath}.stateIndex must equal ${expectedStateIndex}`)
    }

    const devices = requiredArray(state, 'devices', statePath, options.fail)
    const triggeredRules = requiredArray(state, 'triggeredRules', statePath, options.fail)
    const compromisedLinks = requiredArray(
      state,
      'compromisedAutomationLinks',
      statePath,
      options.fail
    )

    validateTriggeredRuleList(
      triggeredRules, `${statePath}.triggeredRules`, options.fail)
    validateTriggeredRuleList(
      compromisedLinks, `${statePath}.compromisedAutomationLinks`, options.fail)

    const deviceIds = new Set<string>()
    devices.forEach((deviceValue, deviceIndex) => {
      const devicePath = `${statePath}.devices[${deviceIndex}]`
      const device = record(deviceValue, devicePath, options.fail)
      requiredText(device, 'deviceId', devicePath, options.fail)
      if (deviceIds.has(device.deviceId)) {
        options.fail(`${statePath}.devices must have unique deviceId values`)
      }
      deviceIds.add(device.deviceId)
      requiredText(device, 'deviceLabel', devicePath, options.fail)
      requiredText(device, 'templateName', devicePath, options.fail)
      const deviceTokenSource = validateModelTokenSource(device, devicePath, options.fail)
      const frozenDevice = frozenDevices.get(device.deviceId)
      if (frozenDevice && (frozenDevice.deviceLabel !== device.deviceLabel
        || frozenDevice.templateName !== device.templateName
        || frozenDevice.modelTokenSource !== deviceTokenSource)) {
        options.fail(`${devicePath} identity and modelTokenSource must stay frozen across states`)
      }
      frozenDevices.set(device.deviceId, {
        deviceLabel: device.deviceLabel,
        templateName: device.templateName,
        modelTokenSource: deviceTokenSource
      })
      optionalText(device, 'state', devicePath, options.fail, undefined, true)
      optionalText(device, 'mode', devicePath, options.fail, undefined, true)
      if (device.compromised !== undefined
        && device.compromised !== null
        && typeof device.compromised !== 'boolean') {
        options.fail(`${devicePath}.compromised must be boolean when present`)
      }

      const variables = requiredArray(device, 'variables', devicePath, options.fail)
      const variableNames = new Set<string>()
      variables.forEach((variable, variableIndex) => {
        const validated = validateTraceVariable(
          variable,
          `${devicePath}.variables[${variableIndex}]`,
          options.fail
        )
        if (variableNames.has(validated.name)) {
          options.fail(`${devicePath}.variables must have unique names`)
        }
        variableNames.add(validated.name)
        if (validated.modelTokenSource !== deviceTokenSource) {
          options.fail(`${devicePath}.variables must use the device modelTokenSource`)
        }
      })
      const frozenVariables = frozenDeviceVariableNames.get(device.deviceId)
      if (frozenVariables && !sameNames(frozenVariables, variableNames)) {
        options.fail(`${devicePath}.variables must keep the same complete name set across states`)
      }
      frozenDeviceVariableNames.set(device.deviceId, new Set(variableNames))
      validateTrustPrivacyList(
        optionalArray(device, 'trustPrivacy', devicePath, options.fail),
        `${devicePath}.trustPrivacy`,
        options.fail,
        'trust'
      )
      validateTrustPrivacyList(
        optionalArray(device, 'privacies', devicePath, options.fail),
        `${devicePath}.privacies`,
        options.fail,
        'privacy'
      )
    })
    if (frozenDeviceIds && !sameNames(frozenDeviceIds, deviceIds)) {
      options.fail(`${statePath}.devices must keep the same complete deviceId set across states`)
    }
    frozenDeviceIds = new Set(deviceIds)

    validateTrustPrivacyList(
      optionalArray(state, 'trustPrivacies', statePath, options.fail),
      `${statePath}.trustPrivacies`,
      options.fail,
      'either'
    )
    for (const field of ['envVariables', 'globalVariables']) {
      const variableNames = new Set<string>()
      optionalArray(state, field, statePath, options.fail).forEach((variable, variableIndex) => {
        const validated = validateTraceVariable(
          variable,
          `${statePath}.${field}[${variableIndex}]`,
          options.fail
        )
        if (variableNames.has(validated.name)) {
          options.fail(`${statePath}.${field} must have unique names`)
        }
        variableNames.add(validated.name)
        if (field === 'envVariables') {
          const frozenSource = frozenEnvironmentSources.get(validated.name)
          if (frozenSource && frozenSource !== validated.modelTokenSource) {
            options.fail(`${statePath}.${field}[${variableIndex}].modelTokenSource must stay frozen across states`)
          }
          frozenEnvironmentSources.set(validated.name, validated.modelTokenSource)
        }
        if (field === 'globalVariables' && validated.modelTokenSource !== 'UNKNOWN') {
          options.fail(`${statePath}.globalVariables must use UNKNOWN modelTokenSource`)
        }
      })
      const frozenNames = frozenStateVariableNames.get(field)
      if (frozenNames && !sameNames(frozenNames, variableNames)) {
        options.fail(`${statePath}.${field} must keep the same complete name set across states`)
      }
      frozenStateVariableNames.set(field, new Set(variableNames))
    }
  })
}
