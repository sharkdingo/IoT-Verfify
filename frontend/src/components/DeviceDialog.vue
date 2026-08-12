<script setup lang="ts">
import {ref, watch, computed, nextTick} from 'vue'
import {useI18n} from 'vue-i18n'
import { useModalAccessibility } from '@/composables/useModalAccessibility'

import type {DeviceManifest, DeviceTemplate, InternalVariable} from '../types/device'
import type {DeviceNode} from '../types/node'
import type {Specification} from '../types/spec'
import { buildSpecFormula } from '@/utils/spec'
import { verdictVariableSourceKeys } from '@/views/board/verdictVariableSource'
import { resolveImpactEnvironmentDefinition } from '@/utils/device'
import { specTemplateDetails } from '@/assets/config/specTemplates'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'
import { resolveEffectiveNodeState } from '@/utils/canvas/nodeState'
import { confirmDestructive } from '@/utils/feedback'
import { deviceIconFor } from '@/utils/deviceIcon'
import {
  PRIVACY_OPTIONS,
  TRUST_OPTIONS,
  buildDeviceRuntimeConfig,
  createDeviceRuntimeDraft,
  getTemplateLocalVariables,
  getTemplateVariableDefaultValue,
  getTemplateWorkingStates,
  resetDeviceRuntimeDraft,
  templateVariableHasEnumValues,
  templateVariableUsesNumericBounds,
  validateDeviceRuntimeConfig,
  type DeviceRuntimeConfig,
  type DeviceRuntimeDraft
} from '@/utils/deviceRuntime'

const props = defineProps<{
  visible: boolean
  deviceName: string
  description: string
  label: string
  nodeId?: string
  manifest?: DeviceManifest | null
  nodes?: DeviceNode[]
  deviceTemplates?: DeviceTemplate[]
  specs?: Specification[]
  runtimeSaving?: boolean
  deleteLoading?: boolean
  suspended?: boolean
}>()

const emit = defineEmits<{
  (e: 'update:visible', value: boolean): void
  (e: 'rename'): void
  (e: 'delete'): void
  (e: 'save-runtime', nodeId: string, runtime: DeviceRuntimeConfig): void
}>()

const {t} = useI18n()

const innerVisible = ref(props.visible)

/* 同步 props -> local state */
watch(() => props.visible, v => (innerVisible.value = v))

const onDelete = () => emit('delete')
const onRename = () => emit('rename')

const isDialogOpen = computed(() => innerVisible.value && props.suspended !== true)

/* ---------- 核心展示数据提取 ---------- */

const manifest = computed<DeviceManifest | null>(() => props.manifest ?? null)

function formatDeviceModelToken(value: unknown): string {
  const raw = value === null || value === undefined ? '' : String(value)
  return currentTemplate.value?.defaultTemplate === true
    ? formatBuiltInModelToken(raw, key => t(key))
    : raw
}

type StateDisplaySegment = {
  mode: string
  value: string
}

const stateModeLabel = (index: number) => {
  const mode = manifest.value?.Modes?.[index]?.trim()
  return mode ? formatDeviceModelToken(mode) : `${t('app.mode')} ${index + 1}`
}

const getStateDisplaySegments = (rawState?: string | null): StateDisplaySegment[] => {
  const raw = String(rawState ?? '').trim()
  if (!raw || raw === '_') return []

  const modes = manifest.value?.Modes || []
  const parts = raw.includes(';') || modes.length > 1
    ? raw.split(';')
    : [raw]

  return parts
    .map((part, index) => ({
      mode: stateModeLabel(index),
      value: formatDeviceModelToken(part.trim())
    }))
    .filter(segment => segment.value && segment.value !== '_')
}

const formatStateForDisplay = (rawState?: string | null, emptyLabel = t('app.anyState')) => {
  const raw = String(rawState ?? '').trim()
  if (!raw || raw === '_') return emptyLabel

  const modes = manifest.value?.Modes || []
  const segments = getStateDisplaySegments(raw)
  if (!segments.length) return emptyLabel
  if (!raw.includes(';') && modes.length <= 1) return segments[0].value
  return segments.map(segment => `${segment.mode}: ${segment.value}`).join(' · ')
}

const getManifestModes = () =>
  (manifest.value?.Modes || [])
    .map(mode => String(mode || '').trim())
    .filter(Boolean)
    .map(formatDeviceModelToken)

const currentNode = computed(() =>
  props.nodes?.find(node => node.id === props.nodeId) || null
)

const currentTemplate = computed<DeviceTemplate | null>(() => {
  const m = manifest.value
  if (!m) return null
  const matched = props.deviceTemplates?.find(template =>
    template.name === props.deviceName
    || template.name === m.Name
    || template.manifest?.Name === props.deviceName
    || template.manifest?.Name === m.Name
  )
  return matched || {
    name: props.deviceName || m.Name,
    manifest: m,
    defaultTemplate: false
  }
})

const runtimeSchemaIdentity = computed(() => {
  const template = currentTemplate.value
  if (!template) return ''
  const templateManifest = template.manifest
  return JSON.stringify({
    templateName: template.name,
    manifestName: templateManifest.Name,
    modes: templateManifest.Modes || [],
    initState: templateManifest.InitState || '',
    states: (templateManifest.WorkingStates || []).map(state => ({
      name: state.Name,
      trust: state.Trust,
      privacy: state.Privacy
    })),
    localVariables: getTemplateLocalVariables(template).map(variable => ({
      name: variable.Name,
      values: variable.Values || [],
      lowerBound: variable.LowerBound,
      upperBound: variable.UpperBound,
      trust: variable.Trust,
      privacy: variable.Privacy,
      falsifiableWhenCompromised: variable.FalsifiableWhenCompromised === true
    }))
  })
})

const runtimeDraft = ref(createDeviceRuntimeDraft())
const runtimeDraftBaseline = ref(createDeviceRuntimeDraft())
const runtimeDraftConflictFields = ref<string[]>([])
const runtimeSchemaConflict = ref(false)
let runtimeSaveSnapshot: {
  submitted: DeviceRuntimeDraft
  acknowledged: DeviceRuntimeDraft
} | null = null

const cloneRuntimeDraft = (draft: DeviceRuntimeDraft): DeviceRuntimeDraft => ({
  state: draft.state,
  currentStateTrust: draft.currentStateTrust,
  currentStatePrivacy: draft.currentStatePrivacy,
  variables: { ...draft.variables },
  variableTrusts: { ...draft.variableTrusts },
  privacies: { ...draft.privacies }
})

// The runtime endpoint canonicalizes whitespace and security labels before it
// returns the authoritative node. Compare that canonical form so an own save
// acknowledgement is not mistaken for a conflicting edit made in another tab.
const normalizeRuntimeDraftValue = (value: unknown, securityLabel = false) => {
  const normalized = String(value ?? '').trim()
  return securityLabel ? normalized.toLowerCase() : normalized
}

const canonicalizeRuntimeDraft = (draft: DeviceRuntimeDraft): DeviceRuntimeDraft => {
  const normalizeRecord = (record: Record<string, string>, securityLabel = false) =>
    Object.fromEntries(Object.entries(record).map(([name, value]) => [
      name,
      normalizeRuntimeDraftValue(value, securityLabel)
    ]))

  return {
    state: normalizeRuntimeDraftValue(draft.state),
    currentStateTrust: normalizeRuntimeDraftValue(draft.currentStateTrust, true),
    currentStatePrivacy: normalizeRuntimeDraftValue(draft.currentStatePrivacy, true),
    variables: normalizeRecord(draft.variables),
    variableTrusts: normalizeRecord(draft.variableTrusts, true),
    privacies: normalizeRecord(draft.privacies, true)
  }
}

const materializeSubmittedRuntimeDraft = (
  template: DeviceTemplate,
  runtime: DeviceRuntimeConfig
): DeviceRuntimeDraft => {
  const draft = createDeviceRuntimeDraft()
  resetDeviceRuntimeDraft(draft, template)

  if (runtime.state !== undefined) draft.state = normalizeRuntimeDraftValue(runtime.state)
  if (runtime.currentStateTrust !== undefined) {
    draft.currentStateTrust = normalizeRuntimeDraftValue(runtime.currentStateTrust, true)
  }
  if (runtime.currentStatePrivacy !== undefined) {
    draft.currentStatePrivacy = normalizeRuntimeDraftValue(runtime.currentStatePrivacy, true)
  }
  for (const variable of runtime.variables || []) {
    draft.variables[variable.name] = normalizeRuntimeDraftValue(variable.value)
    if (variable.trust !== undefined) {
      draft.variableTrusts[variable.name] = normalizeRuntimeDraftValue(variable.trust, true)
    }
  }
  for (const privacy of runtime.privacies || []) {
    draft.privacies[privacy.name] = normalizeRuntimeDraftValue(privacy.privacy, true)
  }

  return canonicalizeRuntimeDraft(draft)
}

const runtimeDraftValuesEqual = (
  left: unknown,
  right: unknown,
  securityLabel = false
) => normalizeRuntimeDraftValue(left, securityLabel)
  === normalizeRuntimeDraftValue(right, securityLabel)

type RuntimeStateContext = Pick<
  DeviceRuntimeDraft,
  'state' | 'currentStateTrust' | 'currentStatePrivacy'
>

const RUNTIME_STATE_CONTEXT_CONFLICT = 'stateContext'

const runtimeStateContext = (draft: DeviceRuntimeDraft): RuntimeStateContext => ({
  state: draft.state,
  currentStateTrust: draft.currentStateTrust,
  currentStatePrivacy: draft.currentStatePrivacy
})

const runtimeStateContextsEqual = (
  left: RuntimeStateContext,
  right: RuntimeStateContext
) => runtimeDraftValuesEqual(left.state, right.state)
  && runtimeDraftValuesEqual(left.currentStateTrust, right.currentStateTrust, true)
  && runtimeDraftValuesEqual(left.currentStatePrivacy, right.currentStatePrivacy, true)

const applyRuntimeStateContext = (
  draft: DeviceRuntimeDraft,
  context: RuntimeStateContext
) => {
  draft.state = context.state
  draft.currentStateTrust = context.currentStateTrust
  draft.currentStatePrivacy = context.currentStatePrivacy
}

const runtimeDraftRecordsEqual = (
  left: Record<string, string>,
  right: Record<string, string>,
  securityLabel = false
) => {
  const keys = new Set([...Object.keys(left), ...Object.keys(right)])
  return [...keys].every(key => runtimeDraftValuesEqual(
    left[key],
    right[key],
    securityLabel
  ))
}

const runtimeDraftsEqual = (left: DeviceRuntimeDraft, right: DeviceRuntimeDraft) =>
  runtimeDraftValuesEqual(left.state, right.state)
  && runtimeDraftValuesEqual(left.currentStateTrust, right.currentStateTrust, true)
  && runtimeDraftValuesEqual(left.currentStatePrivacy, right.currentStatePrivacy, true)
  && runtimeDraftRecordsEqual(left.variables, right.variables)
  && runtimeDraftRecordsEqual(left.variableTrusts, right.variableTrusts, true)
  && runtimeDraftRecordsEqual(left.privacies, right.privacies, true)

const runtimeWorkingStates = computed(() =>
  getTemplateWorkingStates(currentTemplate.value)
)

const runtimeInternalVariables = computed(() =>
  getTemplateLocalVariables(currentTemplate.value)
)

const runtimeStateTemplateDefaults = computed(() => {
  const state = runtimeWorkingStates.value.find(item => item.Name === runtimeDraft.value.state)
  return {
    trust: state?.Trust || 'trusted',
    privacy: state?.Privacy || 'public'
  }
})

const runtimeHasModes = computed(() => {
  const m = currentTemplate.value?.manifest
  return Array.isArray(m?.Modes)
    && m.Modes.length > 0
    && runtimeWorkingStates.value.length > 0
})

const hasRuntimeFields = computed(() =>
  Boolean(currentTemplate.value && (runtimeHasModes.value || runtimeInternalVariables.value.length > 0))
)

const hasRuntimeDraftConflict = computed(() =>
  runtimeSchemaConflict.value || runtimeDraftConflictFields.value.length > 0
)

const hasUnsavedRuntimeDraft = computed(() =>
  hasRuntimeFields.value
  && (hasRuntimeDraftConflict.value
    || !runtimeDraftsEqual(runtimeDraft.value, runtimeDraftBaseline.value))
)

let closeConfirmation: Promise<boolean> | null = null

const prepareClose = async (): Promise<boolean> => {
  if (props.runtimeSaving) return false
  if (!hasUnsavedRuntimeDraft.value) return true
  if (closeConfirmation) return closeConfirmation

  // Single-flight: a second close attempt joins the confirmation already on screen.
  closeConfirmation = confirmDestructive({
    title: t('app.deviceRuntimeDiscardTitle'),
    message: t('app.deviceRuntimeDiscardMessage'),
    confirmText: t('app.discardChanges')
  }).finally(() => {
    closeConfirmation = null
  })
  return closeConfirmation
}

const requestClose = async (): Promise<boolean> => {
  if (!innerVisible.value || !await prepareClose() || !innerVisible.value) return false
  innerVisible.value = false
  emit('update:visible', false)
  return true
}

defineExpose({ prepareClose, requestClose })

const { setDialogRef, handleModalKeydown } = useModalAccessibility(
  isDialogOpen,
  () => { void requestClose() }
)

const variableInputPlaceholder = (variable: InternalVariable) => {
  if (templateVariableUsesNumericBounds(variable)) {
    const lower = variable.LowerBound ?? '-∞'
    const upper = variable.UpperBound ?? '∞'
    const defaultValue = getTemplateVariableDefaultValue(variable)
    return defaultValue
      ? `${t('app.useTemplateDefaultWithValue', { value: defaultValue })} / ${lower} - ${upper}`
      : `${lower} - ${upper}`
  }
  return t('app.enterValuePlaceholder')
}

const createRuntimeDraftFromNode = () => {
  const template = currentTemplate.value
  const draft = createDeviceRuntimeDraft()
  resetDeviceRuntimeDraft(draft, template)

  const node = currentNode.value
  if (node) {
    if (runtimeHasModes.value && node.state) {
      draft.state = resolveEffectiveNodeState(node.state, template?.manifest, draft.state)
      draft.currentStateTrust = node.currentStateTrust || ''
      draft.currentStatePrivacy = node.currentStatePrivacy || ''
    }

    for (const variable of node.variables || []) {
      if (!variable?.name) continue
      draft.variables[variable.name] = variable.value ?? ''
      draft.variableTrusts[variable.name] = variable.trust || ''
    }

    for (const privacy of node.privacies || []) {
      if (!privacy?.name) continue
      draft.privacies[privacy.name] = privacy.privacy || ''
    }
  }

  return canonicalizeRuntimeDraft(draft)
}

const replaceRuntimeDraft = (draft: DeviceRuntimeDraft) => {
  runtimeDraft.value = cloneRuntimeDraft(draft)
  runtimeDraftBaseline.value = cloneRuntimeDraft(draft)
  runtimeDraftConflictFields.value = []
  runtimeSchemaConflict.value = false
}

const syncRuntimeDraftFromNode = () => {
  runtimeSaveSnapshot = null
  replaceRuntimeDraft(createRuntimeDraftFromNode())
}

const runtimeVariableValueFitsCurrentSchema = (variable: InternalVariable, value: string) => {
  const normalizedValue = value.trim()
  if (!normalizedValue) return true
  if (templateVariableHasEnumValues(variable)) {
    return variable.Values!.map(String).includes(normalizedValue)
  }
  if (!templateVariableUsesNumericBounds(variable)) return true
  const numericValue = Number(normalizedValue)
  return Number.isFinite(numericValue)
    && (variable.LowerBound === undefined || numericValue >= variable.LowerBound)
    && (variable.UpperBound === undefined || numericValue <= variable.UpperBound)
}

const reconcileRuntimeDraftForSchemaChange = () => {
  runtimeSaveSnapshot = null
  const incomingDraft = createRuntimeDraftFromNode()
  const baselineDraft = runtimeDraftBaseline.value
  const currentDraft = runtimeDraft.value
  const mergedDraft = cloneRuntimeDraft(incomingDraft)
  const preserveChanged = (
    currentValue = '',
    baselineValue = '',
    securityLabel = false
  ) => !runtimeDraftValuesEqual(currentValue, baselineValue, securityLabel)

  const currentStateContext = runtimeStateContext(currentDraft)
  const baselineStateContext = runtimeStateContext(baselineDraft)
  const supportedStates = new Set(runtimeWorkingStates.value.map(state => state.Name))
  const stateContextFitsCurrentSchema = runtimeHasModes.value
    && supportedStates.has(currentStateContext.state)
    && (!currentStateContext.currentStateTrust
      || TRUST_OPTIONS.some(option => option === currentStateContext.currentStateTrust))
    && (!currentStateContext.currentStatePrivacy
      || PRIVACY_OPTIONS.some(option => option === currentStateContext.currentStatePrivacy))
  if (!runtimeStateContextsEqual(currentStateContext, baselineStateContext)
    && stateContextFitsCurrentSchema) {
    applyRuntimeStateContext(mergedDraft, currentStateContext)
  }

  for (const variable of runtimeInternalVariables.value) {
    const name = variable.Name
    const currentValue = currentDraft.variables[name] ?? ''
    if (preserveChanged(currentValue, baselineDraft.variables[name] ?? '')
      && runtimeVariableValueFitsCurrentSchema(variable, currentValue)) {
      mergedDraft.variables[name] = currentValue
    }
    const currentTrust = currentDraft.variableTrusts[name] ?? ''
    if (preserveChanged(currentTrust, baselineDraft.variableTrusts[name] ?? '', true)
      && (!currentTrust || TRUST_OPTIONS.some(option => option === currentTrust))) {
      mergedDraft.variableTrusts[name] = currentTrust
    }
    const currentPrivacy = currentDraft.privacies[name] ?? ''
    if (preserveChanged(currentPrivacy, baselineDraft.privacies[name] ?? '', true)
      && (!currentPrivacy || PRIVACY_OPTIONS.some(option => option === currentPrivacy))) {
      mergedDraft.privacies[name] = currentPrivacy
    }
  }

  runtimeDraft.value = mergedDraft
  runtimeDraftBaseline.value = cloneRuntimeDraft(incomingDraft)
  runtimeDraftConflictFields.value = []
  runtimeSchemaConflict.value = true
}

const reconcileRuntimeDraftFromNode = () => {
  const incomingDraft = createRuntimeDraftFromNode()
  const baselineDraft = runtimeDraftBaseline.value
  const currentDraft = runtimeDraft.value
  const existingConflicts = new Set(runtimeDraftConflictFields.value)
  const nextConflicts = new Set<string>()

  const mergeValue = (
    path: string,
    baselineValue = '',
    currentValue = '',
    incomingValue = '',
    submittedValue?: string,
    acknowledgedValue?: string
  ) => {
    const securityLabel = path.startsWith('variableTrusts.') || path.startsWith('privacies.')
    const valuesEqual = (left: unknown, right: unknown) => runtimeDraftValuesEqual(
      left,
      right,
      securityLabel
    )
    if (existingConflicts.has(path)) {
      if (valuesEqual(currentValue, incomingValue)) return incomingValue
      nextConflicts.add(path)
      return currentValue
    }
    if (runtimeSaveSnapshot && valuesEqual(incomingValue, acknowledgedValue)) {
      // Adopt the server's materialized value when the field is unchanged since Save.
      // A difference from the submitted draft was typed while the request was in flight.
      return valuesEqual(currentValue, submittedValue) ? incomingValue : currentValue
    }
    if (valuesEqual(currentValue, baselineValue)) return incomingValue
    if (valuesEqual(incomingValue, baselineValue) || valuesEqual(currentValue, incomingValue)) {
      return currentValue
    }
    nextConflicts.add(path)
    return currentValue
  }

  const mergedDraft = createDeviceRuntimeDraft()
  const baselineStateContext = runtimeStateContext(baselineDraft)
  const currentStateContext = runtimeStateContext(currentDraft)
  const incomingStateContext = runtimeStateContext(incomingDraft)
  const submittedStateContext = runtimeSaveSnapshot
    ? runtimeStateContext(runtimeSaveSnapshot.submitted)
    : null
  const acknowledgedStateContext = runtimeSaveSnapshot
    ? runtimeStateContext(runtimeSaveSnapshot.acknowledged)
    : null
  let mergedStateContext = currentStateContext
  if (existingConflicts.has(RUNTIME_STATE_CONTEXT_CONFLICT)) {
    if (runtimeStateContextsEqual(currentStateContext, incomingStateContext)) {
      mergedStateContext = incomingStateContext
    } else {
      nextConflicts.add(RUNTIME_STATE_CONTEXT_CONFLICT)
    }
  } else if (submittedStateContext && acknowledgedStateContext
    && runtimeStateContextsEqual(incomingStateContext, acknowledgedStateContext)) {
    mergedStateContext = runtimeStateContextsEqual(currentStateContext, submittedStateContext)
      ? incomingStateContext
      : currentStateContext
  } else if (runtimeStateContextsEqual(currentStateContext, baselineStateContext)) {
    mergedStateContext = incomingStateContext
  } else if (runtimeStateContextsEqual(incomingStateContext, baselineStateContext)
    || runtimeStateContextsEqual(currentStateContext, incomingStateContext)) {
    mergedStateContext = currentStateContext
  } else {
    nextConflicts.add(RUNTIME_STATE_CONTEXT_CONFLICT)
  }
  applyRuntimeStateContext(mergedDraft, mergedStateContext)

  for (const field of ['variables', 'variableTrusts', 'privacies'] as const) {
    const names = new Set([
      ...Object.keys(baselineDraft[field]),
      ...Object.keys(currentDraft[field]),
      ...Object.keys(incomingDraft[field])
    ])
    for (const name of names) {
      mergedDraft[field][name] = mergeValue(
        `${field}.${name}`,
        baselineDraft[field][name],
        currentDraft[field][name],
        incomingDraft[field][name],
        runtimeSaveSnapshot?.submitted[field][name],
        runtimeSaveSnapshot?.acknowledged[field][name]
      )
    }
  }

  runtimeDraft.value = mergedDraft
  runtimeDraftBaseline.value = cloneRuntimeDraft(incomingDraft)
  runtimeDraftConflictFields.value = [...nextConflicts].sort()
}

const adoptLatestRuntimeDraft = () => {
  const incomingDraft = createRuntimeDraftFromNode()
  if (runtimeSchemaConflict.value) {
    replaceRuntimeDraft(incomingDraft)
    return
  }
  const resolvedDraft = cloneRuntimeDraft(runtimeDraft.value)
  for (const path of runtimeDraftConflictFields.value) {
    if (path === RUNTIME_STATE_CONTEXT_CONFLICT) {
      applyRuntimeStateContext(resolvedDraft, runtimeStateContext(incomingDraft))
      continue
    }
    const separator = path.indexOf('.')
    if (separator < 1) continue
    const field = path.slice(0, separator) as 'variables' | 'variableTrusts' | 'privacies'
    const name = path.slice(separator + 1)
    if (!name || !(field in resolvedDraft)) continue
    resolvedDraft[field][name] = incomingDraft[field][name] ?? ''
  }
  runtimeDraft.value = resolvedDraft
  runtimeDraftBaseline.value = cloneRuntimeDraft(incomingDraft)
  runtimeDraftConflictFields.value = []
}

const keepLocalRuntimeDraft = () => {
  runtimeDraftBaseline.value = cloneRuntimeDraft(createRuntimeDraftFromNode())
  runtimeDraftConflictFields.value = []
  runtimeSchemaConflict.value = false
}

watch(
  () => [props.visible, props.nodeId, runtimeSchemaIdentity.value] as const,
  ([visible, nodeId, schemaIdentity], previous) => {
    if (!visible) return
    const [wasVisible, previousNodeId, previousSchemaIdentity] = previous || []
    if (!wasVisible || nodeId !== previousNodeId) {
      syncRuntimeDraftFromNode()
    } else if (schemaIdentity !== previousSchemaIdentity) {
      if (runtimeDraftsEqual(runtimeDraft.value, runtimeDraftBaseline.value)) {
        syncRuntimeDraftFromNode()
      } else {
        reconcileRuntimeDraftForSchemaChange()
      }
    }
  },
  { immediate: true }
)

watch(
  () => [props.nodes, props.manifest, props.deviceTemplates] as const,
  () => {
    if (props.visible) reconcileRuntimeDraftFromNode()
  }
)

watch(
  () => props.runtimeSaving,
  saving => {
    if (!saving) runtimeSaveSnapshot = null
  },
  { flush: 'post' }
)

/**
 * Why the runtime draft cannot be saved yet, or `null` when it is valid. Drives both the save
 * button's disabled state and the inline message beside it, so the reason stays visible while
 * the user fixes the fields instead of fading in a toast.
 */
const runtimeSaveBlockedReason = computed<string | null>(() => {
  const template = currentTemplate.value
  if (!template || !currentNode.value || !props.nodeId) return null
  // The schema/field conflict already renders its own detailed panel below.
  if (hasRuntimeDraftConflict.value) return t('app.deviceRuntimeConflictUnresolved')

  const runtime = buildDeviceRuntimeConfig(template, runtimeDraft.value, {
    includeEmptyCollections: true,
    variableScope: 'local'
  }) || {}
  return validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'local' }) || null
})

const saveRuntime = () => {
  const template = currentTemplate.value
  const node = currentNode.value
  if (!template || !node || !props.nodeId) return
  // Reported inline by `runtimeSaveBlockedReason`, which also disables the save button.
  if (runtimeSaveBlockedReason.value) return

  const runtime = buildDeviceRuntimeConfig(template, runtimeDraft.value, {
    includeEmptyCollections: true,
    variableScope: 'local'
  }) || {}

  runtimeSaveSnapshot = {
    submitted: canonicalizeRuntimeDraft(runtimeDraft.value),
    acknowledged: materializeSubmittedRuntimeDraft(template, runtime)
  }
  emit('save-runtime', props.nodeId, runtime)
  void nextTick(() => {
    // The parent can reject the request before entering its saving state (for example when
    // playback locks mutations). Do not leave that non-request fencing later refreshes.
    if (!props.runtimeSaving) runtimeSaveSnapshot = null
  })
}

// 1. 基础信息数据
const basicInfo = computed(() => {
  const m = manifest.value
  if (!m) return {}
  const modes = getManifestModes()

  return {
    name: m.Name,
    instanceName: props.label,
    description: m.Description || props.description || t('app.null'),
    initState: m.InitState,
    initStateLabel: modes.length > 0
      ? formatStateForDisplay(m.InitState, t('app.notSpecified'))
      : t('app.noStateMachine'),
    modes,
    impactedVariables: m.ImpactedVariables?.map(formatDeviceModelToken)
  }
})

// 2. 变量列表 (合并 Internal 和 Impacted，并展示隐私/信任)
const variables = computed(() => {
  const m = manifest.value
  if (!m) return []
  const list: any[] = []
  const impactedSet = new Set((m.ImpactedVariables || []).map(name => String(name || '').trim()).filter(Boolean))

  // Internal Variables (完整对象)
  if (m.InternalVariables) {
    m.InternalVariables.forEach(iv => {
      // 智能格式化 Value 列：显示枚举值 或 数值范围
      let valDisplay = ''
      // The owner predicates, not a local `!== undefined` pair: a board response serializes an absent
      // bound as `null`, which passed that test and rendered `[null, 30]`.
      if (templateVariableHasEnumValues(iv)) valDisplay = iv.Values!.map(formatDeviceModelToken).join(' / ')
      else if (templateVariableUsesNumericBounds(iv)) valDisplay = `[${iv.LowerBound}, ${iv.UpperBound}]`

      const isEnvironment = iv.IsInside !== true
      list.push({
        name: iv.Name,
        displayName: formatDeviceModelToken(iv.Name),
        range: valDisplay || (isEnvironment ? t('app.fromEnvironmentPool') : ''),
        trust: iv.Trust,
        privacy: iv.Privacy,
        falsifiableWhenCompromised: iv.FalsifiableWhenCompromised === true,
        type: isEnvironment ? t('app.environmentVariable') : t('app.internalVariable'),
        isInternal: !isEnvironment,
        affectsEnvironment: impactedSet.has(iv.Name)
      })
    })
  }

  // Impacted Variables (外部引用)
  if (m.ImpactedVariables) {
    m.ImpactedVariables.forEach(vName => {
      // 避免重复显示
      if (!list.some(item => item.name === vName)) {
        const definition = resolveImpactEnvironmentDefinition(m, vName)
        const range = definition && templateVariableHasEnumValues(definition)
          ? definition.Values!.map(formatDeviceModelToken).join(' / ')
          : definition && templateVariableUsesNumericBounds(definition)
            ? `[${definition.LowerBound}, ${definition.UpperBound}]`
            : ''
        list.push({
          name: vName,
          displayName: formatDeviceModelToken(vName),
          range,
          trust: definition?.Trust || null,
          privacy: definition?.Privacy || null,
          falsifiableWhenCompromised: null,
          type: t('app.affectsEnvironment'),
          isInternal: false,
          affectsEnvironment: true
        })
      }
    })
  }
  return list
})

// 3. 状态列表
const states = computed(() => {
  const m = manifest.value
  if (!m || !m.WorkingStates) return []
  return m.WorkingStates.map(s => ({
    name: s.Name,
    displayName: formatStateForDisplay(s.Name, t('app.null')),
    description: s.Description,
    trust: s.Trust,
    privacy: s.Privacy
  }))
})

// 4. API列表
const apis = computed(() => {
  const m = manifest.value
  if (!m || !m.APIs) return []
  return m.APIs.map(api => ({
    name: api.Name,
    displayName: formatDeviceModelToken(api.Name),
    description: api.Description || '',
    startState: api.StartState,
    endState: api.EndState,
    startStateLabel: formatStateForDisplay(api.StartState, t('app.anyState')),
    endStateLabel: formatStateForDisplay(api.EndState, t('app.noStateChange')),
    trigger: formatTrigger(api.Trigger),
    signal: api.Signal || false,
    acceptsContent: api.AcceptsContent === true
  }))
})

// Trigger is an object { Attribute, Relation, Value }; render it as readable text.
const formatTrigger = (trigger: any): string => {
  if (!trigger) return t('app.userRole')
  if (typeof trigger !== 'object') return t('app.userRole')
  const relation = String(trigger.Relation || '=').trim().toLowerCase()
  const relationLabels: Record<string, string> = {
    '=': t('app.relationEquals'),
    '!=': t('app.relationNotEquals'),
    '>': t('app.relationGreater'),
    '<': t('app.relationLess'),
    '>=': t('app.relationGreaterEqual'),
    '<=': t('app.relationLessEqual'),
    in: t('app.relationIn'),
    'not in': t('app.relationNotIn'),
    not_in: t('app.relationNotIn')
  }
  const rel = relationLabels[relation] || String(trigger.Relation || '=')
  const value = trigger.Value !== undefined && trigger.Value !== ''
    ? ` ${rel} ${formatDeviceModelToken(trigger.Value)}`
    : ''
  return trigger.Attribute
    ? `${formatDeviceModelToken(trigger.Attribute)}${value}`
    : t('app.userRole')
}

// 获取设备图标
/* `getDeviceIcon` moved to `utils/deviceIcon.ts`: RuleBuilderDialog had a near-identical copy that had
   drifted in both directions. */
const getDeviceIcon = (deviceName: string) => deviceIconFor(deviceName)

const getSpecFormulaKind = (spec: Specification, formula: string) => {
  if (spec.templateId === '6') return 'LTL'
  if (spec.templateId) return 'CTL'
  const normalized = String(formula || '').trim().toUpperCase()
  if (normalized.startsWith('LTLSPEC')) return 'LTL'
  if (normalized.startsWith('CTLSPEC')) return 'CTL'
  return t('app.modelFormulaKind')
}

// 获取设备相关的规约
const deviceSpecs = computed(() => {
  if (!props.specs || !props.nodeId) {
    return []
  }

  const currentDeviceId = props.nodeId // 使用正确的设备ID
  
  // 检查条件中是否包含该设备
  const checkConditionsForDevice = (spec: Specification) => {
    const allConditions = [
      ...(spec.aConditions || []),
      ...(spec.ifConditions || []),
      ...(spec.thenConditions || [])
    ]
    return allConditions.some(cond => cond && cond.deviceId === currentDeviceId)
  }
  
  return props.specs
    .filter(spec => {
      // 检查多设备规约
      if (spec.devices && Array.isArray(spec.devices) && spec.devices.some(d => d && d.deviceId === currentDeviceId)) return true
      // 检查条件中是否包含该设备
      if (checkConditionsForDevice(spec)) return true
      return false
    })
    .map(spec => {
      const template = specTemplateDetails.find(candidate => candidate.id === spec.templateId)
      const specType = template?.labelKey
        ? t(template.labelKey)
        : spec.templateLabel || template?.label || t('app.unknown')

      // 处理设备信息显示
      let deviceInfo = ''
      if (spec.devices && spec.devices.length > 0) {
        const deviceLabels = spec.devices.map(d => d.deviceLabel || d.deviceId).join(', ')
        deviceInfo = deviceLabels
      } else {
        const allConditions = [
          ...(spec.aConditions || []),
          ...(spec.ifConditions || []),
          ...(spec.thenConditions || [])
        ]
        const deviceLabels = Array.from(new Set(
          allConditions
            .map(c => c.deviceLabel || c.deviceId)
            .filter(Boolean)
        ))
        deviceInfo = deviceLabels.length > 0 ? deviceLabels.join(', ') : t('app.global')
      }

      const formula = buildSpecFormula(spec, {
        nodes: props.nodes || []
      })

      return {
        id: spec.id,
        // Named in the user's words; the formula above distinguishes the readings only by the token before
        // the dot, and renders an unrecorded one as a literal `<unresolved>`.
        variableSourceLabels: verdictVariableSourceKeys(spec)
          .map(key => ({ key, label: t(key), unresolved: key === 'app.specVariableSourceUnresolvedShort' })),
        type: specType,
        formula,
        formulaKind: getSpecFormulaKind(spec, formula),
        devices: deviceInfo
      }
    })
})
</script>

<template>
  <!-- 自定义模态框 -->
  <teleport to="body">
    <transition name="iot-dialog" appear>
      <div
        v-if="isDialogOpen"
        class="iot-dialog-overlay"
        @keydown="handleModalKeydown"
        @click.self="requestClose"
      >
          <div
            :ref="setDialogRef"
            data-testid="device-dialog"
            class="iot-dialog iot-dialog--md device-dialog-surface"
            role="dialog"
            aria-modal="true"
            aria-labelledby="device-dialog-title"
            tabindex="-1"
          >

            <!-- Header -->
            <div class="iot-dialog__header">
              <span class="iot-dialog__icon" aria-hidden="true">
                <span class="material-icons-round">{{ getDeviceIcon(deviceName) }}</span>
              </span>
              <div class="iot-dialog__heading">
                <h2 id="device-dialog-title" class="iot-dialog__title">{{ t('app.deviceInfo') }}</h2>
                <p class="iot-dialog__subtitle truncate" :title="label">{{ label }}</p>
              </div>
              <button type="button" data-testid="device-dialog-close" @click="requestClose" :disabled="runtimeSaving" class="iot-dialog__close" :aria-label="t('app.close')">
                <span class="material-icons-round text-xl" aria-hidden="true">close</span>
              </button>
            </div>

            <!-- Body -->
            <div class="device-dialog-body iot-dialog__body iot-scroll-region min-w-0 space-y-6 overflow-x-hidden sm:space-y-8">
              <div
                v-if="!manifest"
                data-testid="device-template-details-unavailable"
                class="rounded-lg board-surface-warning px-4 py-3 text-sm leading-6 board-text-warning"
              >
                {{ t('app.deviceTemplateDetailsUnavailable', { template: deviceName }) }}
              </div>

              <!-- Basic Info -->
              <section>
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceBasic') }}</h2>
                </div>
                
                <!-- 基本信息表格 -->
                <div class="board-card board-card--raised overflow-hidden border border-slate-200 rounded-xl">
                  <table class="device-basic-table w-full table-fixed text-left border-collapse">
                    <thead>
                      <tr class="bg-slate-50 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider w-1/3">{{ t('app.property') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.value') }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100">
                      <!-- Template Name -->
                      <tr class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.name') }}</td>
                        <td class="device-basic-value break-words px-4 py-3 text-sm font-bold text-slate-800">{{ basicInfo.name || deviceName }}</td>
                      </tr>
                      
                      <!-- Instance Name -->
                      <tr class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.instanceName') }}</td>
                        <td class="device-basic-value break-words px-4 py-3 text-sm font-medium text-slate-700">{{ basicInfo.instanceName || label }}</td>
                      </tr>

                      <!-- Modes -->
                      <tr v-if="manifest" class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.modes') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-1.5">
                            <template v-if="basicInfo.modes && basicInfo.modes.length">
                              <span
                                v-for="mode in basicInfo.modes"
                                :key="mode"
                                class="max-w-full break-all whitespace-normal px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded-md font-medium border border-slate-200"
                              >
                                {{ formatDeviceModelToken(mode) }}
                              </span>
                            </template>
                            <span
                              v-else
                              class="px-2 py-0.5 bg-slate-100 text-slate-500 text-xs rounded-md font-medium border border-slate-200"
                            >
                              {{ t('app.noStateMachine') }}
                            </span>
                  </div>
                        </td>
                      </tr>

                      <!-- Initial State -->
                      <tr v-if="manifest" class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.initState') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex min-w-0 items-center gap-2">
                            <span class="h-2 w-2 shrink-0 rounded-full bg-[color:var(--success)] animate-pulse"></span>
                    <span class="device-basic-value min-w-0 break-words text-sm font-medium text-slate-700" :title="basicInfo.initStateLabel">{{ basicInfo.initStateLabel }}</span>
                  </div>
                        </td>
                      </tr>

                      <!-- Description -->
                      <tr v-if="manifest" class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.description') }}</td>
                        <td class="device-basic-value break-words px-4 py-3 text-sm text-slate-600 leading-relaxed">{{ basicInfo.description || '-' }}</td>
                      </tr>

                      <!-- Impacted Variables -->
                      <tr v-if="basicInfo.impactedVariables && basicInfo.impactedVariables.length" class="board-card--muted hover:transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.impactedVariables') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-2">
                      <span v-for="variable in basicInfo.impactedVariables" :key="variable"
                                  class="max-w-full break-all whitespace-normal px-2.5 py-1 board-chip-info board-text-info text-xs font-medium rounded-md border board-border-subtle">
                        {{ variable }}
                      </span>
                    </div>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
                <details v-if="nodeId" class="mt-3 rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs text-slate-600">
                  <summary class="cursor-pointer font-semibold text-slate-700">{{ t('app.technicalDetails') }}</summary>
                  <div class="mt-2 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                    <span class="font-medium text-slate-500">{{ t('app.deviceTechnicalId') }}</span>
                    <code class="board-card break-all rounded px-2 py-1 text-[11px] text-slate-700">{{ nodeId }}</code>
                  </div>
                </details>
              </section>

              <!-- Instance runtime overrides -->
              <section v-if="hasRuntimeFields" data-testid="device-instance-runtime">
                <div class="flex items-center justify-between gap-3 mb-4">
                  <div class="flex items-center gap-2 min-w-0">
                    <div class="w-1 h-5 bg-[color:var(--accent)] rounded-full"></div>
                    <div class="min-w-0">
                      <h2 class="text-lg font-semibold text-slate-800">{{ t('app.instanceRuntime') }}</h2>
                      <p class="text-xs text-slate-500 mt-0.5">{{ t('app.instanceRuntimeHint') }}</p>
                    </div>
                  </div>
                  <button
                    type="button"
                    data-testid="device-runtime-save"
                    @click="saveRuntime"
                    :disabled="runtimeSaving || Boolean(runtimeSaveBlockedReason)"
                    :aria-describedby="runtimeSaveBlockedReason && !hasRuntimeDraftConflict
                      ? 'device-runtime-save-blocked-reason'
                      : undefined"
                    class="inline-flex min-h-11 shrink-0 items-center justify-center gap-2 rounded-lg bg-[color:var(--accent-fill)] px-4 py-2 text-xs font-bold text-white shadow-sm transition-all hover:bg-[color:var(--accent-fill-hover)] disabled:cursor-not-allowed disabled:board-chip-info"
                  >
                    <span v-if="runtimeSaving" class="h-3.5 w-3.5 animate-spin rounded-full border-2 border-white/40 border-t-white" aria-hidden="true"></span>
                    <span v-else class="material-symbols-outlined text-sm" aria-hidden="true">save</span>
                    {{ t('app.saveInstanceConfig') }}
                  </button>
                </div>

                <!-- Validation reason. The schema/field conflict has its own richer panel
                     below, so this only covers the remaining runtime validation failures. -->
                <p
                  v-if="runtimeSaveBlockedReason && !hasRuntimeDraftConflict"
                  id="device-runtime-save-blocked-reason"
                  role="status"
                  data-testid="device-runtime-blocked-reason"
                  class="mb-3 text-xs font-semibold leading-5 board-text-danger"
                >
                  {{ runtimeSaveBlockedReason }}
                </p>

                <div
                  v-if="hasRuntimeDraftConflict"
                  data-testid="device-runtime-conflict"
                  class="device-runtime-conflict mb-3 rounded-lg board-surface-warning px-3 py-3 text-sm board-text-warning"
                  role="alert"
                >
                  <p
                    v-if="runtimeSchemaConflict"
                    data-testid="device-runtime-schema-conflict"
                  >
                    {{ t('app.deviceRuntimeSchemaConflict') }}
                  </p>
                  <p v-if="runtimeDraftConflictFields.length > 0">
                    {{ t('app.deviceRuntimeConflict', { count: runtimeDraftConflictFields.length }) }}
                  </p>
                  <div class="mt-3 flex flex-wrap gap-2">
                    <button
                      type="button"
                      data-testid="device-runtime-adopt-latest"
                      class="device-runtime-adopt-latest min-h-11 rounded-md border border-[color:var(--warning-border)] bg-white px-3 py-1.5 text-xs font-semibold board-text-warning hover:board-chip-warning"
                      @click="adoptLatestRuntimeDraft"
                    >
                      {{ t('app.deviceRuntimeUseLatest') }}
                    </button>
                    <button
                      type="button"
                      data-testid="device-runtime-keep-local"
                      class="min-h-11 rounded-md bg-[color:var(--warning-fill)] px-3 py-1.5 text-xs font-semibold text-white hover:bg-[color-mix(in_srgb,var(--warning)_84%,#000)]"
                      @click="keepLocalRuntimeDraft"
                    >
                      {{ runtimeSchemaConflict
                        ? t('app.deviceRuntimeContinueCompatible')
                        : t('app.deviceRuntimeKeepMine') }}
                    </button>
                  </div>
                </div>

                <div class="device-runtime-panel space-y-3 rounded-xl border board-border-subtle board-chip-info p-4">
                  <div v-if="runtimeHasModes" class="grid grid-cols-1 gap-3">
                    <label class="min-w-0">
                      <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase tracking-wide text-slate-500">{{ t('app.initialState') }}</span>
                      <select
                        v-model="runtimeDraft.state"
                        data-testid="device-runtime-state"
                        class="w-full rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700 shadow-sm focus:border-[color:var(--accent)] focus:ring-2 focus:ring-[color:var(--accent-border)]"
                      >
                        <option v-for="state in runtimeWorkingStates" :key="state.Name" :value="state.Name">
                          {{ formatStateForDisplay(state.Name, state.Name) }}
                        </option>
                      </select>
                    </label>

                  </div>

                  <div v-if="runtimeInternalVariables.length > 0" class="space-y-2">
                    <div
                      v-for="variable in runtimeInternalVariables"
                      :key="variable.Name"
                      class="board-card board-card--raised rounded-lg border border-slate-200 p-3"
                    >
                      <div class="mb-2 flex min-w-0 items-center justify-between gap-2">
                        <div class="min-w-0">
                          <span class="block truncate text-xs font-bold text-slate-700" :title="formatDeviceModelToken(variable.Name)">{{ formatDeviceModelToken(variable.Name) }}</span>
                          <span class="text-[length:var(--iot-font-min)] font-semibold text-slate-500">
                            {{ variable.IsInside !== true ? t('app.environmentVariable') : t('app.internalVariable') }}
                          </span>
                        </div>
                        <span v-if="templateVariableUsesNumericBounds(variable)" class="shrink-0 text-[length:var(--iot-font-min)] font-semibold text-slate-500">
                          {{ variableInputPlaceholder(variable) }}
                        </span>
                      </div>

                      <div class="grid grid-cols-1 gap-2">
                        <label class="min-w-0">
                          <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase text-slate-500">{{ t('app.variableValue') }}</span>
                          <select
                            v-if="templateVariableHasEnumValues(variable)"
                            v-model="runtimeDraft.variables[variable.Name]"
                            :data-testid="`device-runtime-variable-${variable.Name}`"
                            class="board-card w-full min-w-0 rounded-lg border border-slate-200 px-3 py-2 text-sm text-slate-700"
                          >
                            <option value="">{{ t('app.useTemplateDefaultWithValue', { value: formatDeviceModelToken(getTemplateVariableDefaultValue(variable)) }) }}</option>
                            <option v-for="value in variable.Values" :key="value" :value="String(value)">{{ formatDeviceModelToken(value) }}</option>
                          </select>
                          <input
                            v-else
                            v-model="runtimeDraft.variables[variable.Name]"
                            :data-testid="`device-runtime-variable-${variable.Name}`"
                            class="board-card w-full min-w-0 rounded-lg border border-slate-200 px-3 py-2 text-sm text-slate-700 placeholder:text-slate-400"
                            :placeholder="variableInputPlaceholder(variable)"
                            type="text"
                          />
                        </label>

                      </div>
                    </div>
                  </div>

                  <details class="device-runtime-security border-t board-border-subtle pt-3" data-testid="device-runtime-advanced-security">
                    <summary class="flex cursor-pointer list-none items-center justify-between gap-3 text-xs font-bold board-text-info">
                      <span class="inline-flex items-center gap-2">
                        <span class="material-symbols-outlined text-base" aria-hidden="true">tune</span>
                        {{ t('app.advancedTrustPrivacyOverrides') }}
                      </span>
                      <span class="material-symbols-outlined text-base" aria-hidden="true">expand_more</span>
                    </summary>
                    <p class="mt-2 text-[11px] leading-4 text-slate-500">{{ t('app.advancedTrustPrivacyOverridesHint') }}</p>

                    <div v-if="runtimeHasModes" class="mt-3 grid grid-cols-1 gap-3 sm:grid-cols-2">
                      <label class="min-w-0">
                        <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase tracking-wide text-slate-500">{{ t('app.stateTrust') }}</span>
                        <select
                          v-model="runtimeDraft.currentStateTrust"
                          data-testid="device-runtime-state-trust"
                          class="board-card w-full rounded-lg border border-slate-200 px-3 py-2 text-sm text-slate-700"
                        >
                          <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${runtimeStateTemplateDefaults.trust}`) }) }}</option>
                          <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                        </select>
                      </label>

                      <label class="min-w-0">
                        <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase tracking-wide text-slate-500">{{ t('app.statePrivacy') }}</span>
                        <select
                          v-model="runtimeDraft.currentStatePrivacy"
                          data-testid="device-runtime-state-privacy"
                          class="board-card w-full rounded-lg border border-slate-200 px-3 py-2 text-sm text-slate-700"
                        >
                          <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${runtimeStateTemplateDefaults.privacy}`) }) }}</option>
                          <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
                        </select>
                      </label>
                    </div>

                    <div v-if="runtimeInternalVariables.length > 0" class="mt-3 space-y-2">
                      <div
                        v-for="variable in runtimeInternalVariables"
                        :key="`security-${variable.Name}`"
                        class="grid grid-cols-1 gap-2 border-t border-slate-200 pt-2 sm:grid-cols-[minmax(0,1fr)_8rem_8rem]"
                      >
                        <span class="self-center break-words text-xs font-semibold text-slate-600">{{ formatDeviceModelToken(variable.Name) }}</span>
                        <label class="min-w-0">
                          <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase text-slate-500">{{ t('app.variableTrust') }}</span>
                          <select
                            v-model="runtimeDraft.variableTrusts[variable.Name]"
                            :data-testid="`device-runtime-variable-trust-${variable.Name}`"
                            class="board-card w-full min-w-0 rounded-lg border border-slate-200 px-2 py-2 text-xs text-slate-700"
                          >
                            <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${variable.Trust}`) }) }}</option>
                            <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                          </select>
                        </label>
                        <label class="min-w-0">
                          <span class="mb-1 block text-[length:var(--iot-font-min)] font-bold uppercase text-slate-500">{{ t('app.privacy') }}</span>
                          <select
                            v-model="runtimeDraft.privacies[variable.Name]"
                            :data-testid="`device-runtime-privacy-${variable.Name}`"
                            class="board-card w-full min-w-0 rounded-lg border border-slate-200 px-2 py-2 text-xs text-slate-700"
                          >
                            <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${variable.Privacy}`) }) }}</option>
                            <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
                          </select>
                        </label>
                      </div>
                    </div>
                  </details>
                </div>
              </section>

              <!-- Variables -->
              <section v-if="variables.length">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceVariables') }}</h2>
                </div>
                <div class="iot-scroll-region-x border border-slate-200 rounded-xl shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-gradient-to-r from-slate-50 to-slate-100 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.name') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.range') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.trust') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.privacy') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.compromiseBehavior') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.type') }}</th>
                      </tr>
                    </thead>
                    <tbody class="board-card divide-y divide-slate-100">
                      <tr v-for="(v, idx) in variables" :key="idx" class="hover:board-chip-info transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700" :title="v.displayName">{{ v.displayName }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 font-mono" :title="v.range || '-'">{{ v.range || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="v.trust === 'trusted' ? 'board-chip-success board-text-success' :
                                    v.trust === 'untrusted' ? 'board-chip-danger board-text-danger' :
                                    'bg-slate-100 text-slate-600'">
                            {{ v.trust ? t(`app.${v.trust}`) : '-' }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="v.privacy === 'private' ? 'board-chip-info board-text-info' :
                                    v.privacy === 'public' ? '' :
                                    'bg-slate-100 text-slate-600'">
                            {{ v.privacy ? t(`app.${v.privacy}`) : '-' }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span
                            v-if="v.falsifiableWhenCompromised !== null"
                            class="inline-flex items-center gap-1 rounded px-2 py-0.5 text-xs font-medium"
                            :class="v.falsifiableWhenCompromised ? 'board-chip-warning board-text-warning' : 'bg-slate-100 text-slate-600'"
                          >
                            <span class="material-symbols-outlined text-sm" aria-hidden="true">
                              {{ v.falsifiableWhenCompromised ? 'data_alert' : 'verified_user' }}
                            </span>
                            {{ v.falsifiableWhenCompromised ? t('app.readingMayBeFalsified') : t('app.notFalsifiedByAttackModel') }}
                          </span>
                          <span v-else>-</span>
                        </td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-1.5">
                          <span
                            class="inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium"
                            :class="v.isInternal ? 'board-chip-info board-text-info' : 'board-chip-success board-text-success'"
                          >
                            {{ v.type }}
                          </span>
                          <span
                            v-if="v.affectsEnvironment"
                            class="inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium board-chip-info board-text-info"
                          >
                            {{ t('app.affectsEnvironmentShort') }}
                          </span>
                          </div>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- States -->
              <section v-if="manifest" data-testid="device-dialog-states">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceStates') }}</h2>
                </div>
                <div class="iot-scroll-region-x border border-slate-200 rounded-xl shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-gradient-to-r from-slate-50 to-slate-100 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.name') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.description') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.trust') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.privacy') }}</th>
                      </tr>
                    </thead>
                    <tbody class="board-card divide-y divide-slate-100">
                      <tr v-if="states.length === 0">
                        <td class="px-4 py-8 text-center text-slate-500 text-sm italic" colspan="4">
                          {{ t('app.noData') }}
                        </td>
                      </tr>
                      <tr v-for="(s, idx) in states" :key="idx" class="hover:board-chip-info transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700" :title="s.displayName">{{ s.displayName }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">{{ s.description || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="s.trust === 'trusted' ? 'board-chip-success board-text-success' : 'board-chip-danger board-text-danger'">
                            {{ t(`app.${s.trust}`) }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="s.privacy === 'public' ? 'board-chip-info board-text-info' : 
                                    s.privacy === 'private' ? '' : 
                                    'bg-slate-100 text-slate-600'">
                            {{ t(`app.${s.privacy}`) }}
                          </span>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- APIs Section -->
              <section v-if="apis.length > 0" data-testid="device-dialog-apis" class="min-w-0">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-[color:var(--success)] rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceApis') }}</h2>
                </div>
                <div class="grid grid-cols-1 md:grid-cols-2 gap-4">
                  <div
                    v-for="(api, idx) in apis"
                    :key="idx"
                    class="device-api-card min-w-0 bg-white border border-slate-200 rounded-xl p-4 hover:shadow-md transition-all hover:board-border-subtle group"
                  >
                    <div class="flex min-w-0 flex-wrap items-start justify-between gap-2 mb-3">
                      <div class="flex min-w-0 items-center gap-2">
                        <div class="w-8 h-8 board-chip-success rounded-lg flex items-center justify-center group-hover:transition-colors">
                        <span class="material-icons-round board-text-success text-lg">api</span>
                        </div>
                        <span class="min-w-0 break-words text-sm font-bold text-slate-800" :title="api.displayName">{{ api.displayName }}</span>
                      </div>
                      <div class="flex flex-wrap justify-end gap-1">
                        <span v-if="api.signal" class="text-[length:var(--iot-font-min)] px-1.5 py-0.5 board-chip-warning board-text-warning rounded font-medium border board-border-subtle">
                          {{ t('app.signal') }}
                        </span>
                        <span v-if="api.acceptsContent" class="text-[length:var(--iot-font-min)] px-1.5 py-0.5 board-chip-info board-text-info rounded font-medium border border-[color:var(--accent-border)]">
                          {{ t('app.acceptsContentSensitivity') }}
                        </span>
                      </div>
                    </div>
                    <p v-if="api.description" class="text-xs text-slate-600 mb-4 line-clamp-2">
                      {{ api.description }}
                    </p>
                    <div class="device-api-transition flex min-w-0 flex-wrap items-center gap-2 text-xs bg-slate-50 p-2 rounded-lg border border-slate-100">
                      <div class="flex items-center gap-1 text-slate-500 min-w-0">
                        <span class="material-icons-round text-sm font-bold">play_arrow</span>
                        <span class="font-medium text-slate-700 truncate max-w-[10rem]" :title="api.startStateLabel">{{ api.startStateLabel }}</span>
                      </div>
                      <span class="text-slate-500 shrink-0">→</span>
                      <div class="flex items-center gap-1 text-slate-500 min-w-0">
                        <span class="material-icons-round text-sm font-bold">stop</span>
                        <span class="font-medium text-slate-700 truncate max-w-[12rem]" :title="api.endStateLabel">{{ api.endStateLabel }}</span>
                      </div>
                      <div class="flex-1"></div>
                      <span class="min-w-0 break-all text-[length:var(--iot-font-min)] font-semibold uppercase text-slate-500">{{ t('app.trigger') }}: {{ api.trigger }}</span>
                    </div>
                  </div>
                </div>
              </section>

              <!-- Specifications Section -->
              <section v-if="manifest && deviceSpecs.length > 0" class="min-w-0">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-[color:var(--danger)] rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.specifications') }}</h2>
                </div>
                  <div v-if="deviceSpecs.length === 0" class="bg-slate-50 border border-slate-200 rounded-xl p-8 text-center">
                  <span class="material-icons-round text-slate-500 text-4xl mb-2 block">verified</span>
                    <p class="text-sm text-slate-500">{{ t('app.noSpecs') }}</p>
                </div>
                <div v-else class="space-y-3">
                  <div
                    v-for="spec in deviceSpecs"
                    :key="spec.id"
                    class="device-spec-card min-w-0 bg-white border border-slate-200 rounded-xl p-4 transition-all hover:shadow-md hover:border-[color:var(--danger)]"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex min-w-0 flex-1 items-center gap-2">
                        <div class="flex h-8 w-8 shrink-0 items-center justify-center rounded-lg board-chip-danger">
                          <span class="material-icons-round board-text-danger text-lg">verified</span>
                        </div>
                        <div class="flex-1 min-w-0">
                          <span class="text-sm font-bold block truncate text-slate-800">{{ spec.type }}</span>
                          <span class="text-xs text-slate-500 mt-0.5 block truncate">
                            <span class="font-medium text-slate-500">{{ t('app.target') }}:</span> {{ spec.devices }}
                          </span>
                        </div>
                      </div>
                    </div>
                    <div class="bg-slate-50 rounded-lg p-3 border border-slate-100">
                      <div class="mb-1 flex items-center gap-2">
                        <p class="text-[11px] text-slate-500 uppercase font-bold tracking-wider">{{ t('app.formulaPreview') }}</p>
                        <span class="board-card rounded px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold text-slate-600">{{ spec.formulaKind }}</span>
                      </div>
                      <div class="text-xs text-slate-700 leading-relaxed font-mono break-all">
                      {{ spec.formula }}
                      </div>
                      <div v-if="spec.variableSourceLabels.length" class="mt-1 flex flex-wrap gap-1">
                        <!-- An unresolved reading blocks the run; do not render it as a neutral fact. -->
                        <span
                          v-for="entry in spec.variableSourceLabels"
                          :key="entry.key"
                          class="rounded border px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-semibold"
                          :class="entry.unresolved
                            ? 'board-chip-danger board-text-danger border-[color:var(--danger-border)]'
                            : 'border-slate-200 bg-slate-100 text-slate-600'"
                          data-testid="device-dialog-spec-variable-source"
                        >{{ entry.label }}</span>
                      </div>
                      <details class="mt-2 text-[11px] text-slate-500">
                        <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                        <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                          <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                          <code class="board-card break-all rounded px-2 py-1 text-[11px] text-slate-700">{{ spec.id }}</code>
                        </div>
                      </details>
                    </div>
                  </div>
                </div>
              </section>
            </div>

            <!-- Footer -->
            <div class="device-dialog-footer iot-dialog__footer flex-wrap">
              <button
                v-if="nodeId"
                type="button"
                data-testid="device-rename"
                @click="onRename"
                :disabled="runtimeSaving"
                class="iot-dialog-btn iot-dialog-btn--quiet iot-dialog__footer-aside"
              >
                <span class="material-icons-round text-lg" aria-hidden="true">edit</span>
                {{ t('app.rename') }}
              </button>
                <button type="button" data-testid="device-dialog-footer-close" @click="requestClose" :disabled="runtimeSaving" class="iot-dialog-btn iot-dialog-btn--ghost">
                  {{ t('app.close') }}
                </button>
              <button
                type="button"
                data-testid="device-delete"
                @click="onDelete"
                :disabled="deleteLoading || runtimeSaving"
                :aria-busy="deleteLoading"
                class="iot-dialog-btn iot-dialog-btn--danger"
              >
                <span v-if="deleteLoading" class="iot-dialog-btn__spinner" aria-hidden="true"></span>
                <span v-else class="material-icons-round text-lg" aria-hidden="true">delete_outline</span>
                {{ deleteLoading ? t('app.loading') : t('app.deleteDevice') }}
              </button>
            </div>
          </div>
      </div>
    </transition>
  </teleport>
</template>

<style scoped>
/*
 * Overflow containment for the body and its sections — deliberately NOT the surface.
 *
 * `.device-dialog-surface` used to be in this list, and because a scoped rule carries `[data-v-…]` it
 * outranked the `max-w-4xl` on the same element (0-2-0 against 0-1-0). So the 896px cap never applied and the
 * dialog grew to the viewport: measured 2516×1433 on a 2548×1465 screen, 98.7% × 97.8%, with content that
 * needed nowhere near that width. The surface needs no `max-width: 100%` of its own — it is a flex column
 * already bounded by the Tailwind cap and the overlay's padding.
 */
.device-dialog-body,
.device-dialog-body > section,
.device-dialog-body > section > * {
  min-width: 0;
  max-width: 100%;
}

.device-api-transition > .flex-1 {
  display: none;
}

.device-basic-value {
  overflow-wrap: anywhere;
}

:global(:root[data-theme='dark'] .device-dialog-surface) {
  background: var(--surface-panel);
  color: var(--text);
}

:global(:root[data-theme='dark'] .device-dialog-surface .bg-white),
:global(:root[data-theme='dark'] .device-dialog-surface .bg-slate-50),
:global(:root[data-theme='dark'] .device-dialog-surface .bg-slate-50\/50),
:global(:root[data-theme='dark'] .device-dialog-surface .bg-slate-100) {
  background-color: var(--surface-elevated) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="from-white"]),
:global(:root[data-theme='dark'] .device-dialog-surface [class*="from-slate-50"]) {
  background-image: none !important;
  background-color: var(--surface-elevated) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="hover:bg-slate-"]:hover) {
  background-color: var(--surface-muted) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="hover:bg-blue-"]:hover) {
  background-color: color-mix(in srgb, var(--accent) 18%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="hover:bg-emerald-"]:hover),
:global(:root[data-theme='dark'] .device-dialog-surface .group:hover [class*="group-hover:bg-emerald-"]) {
  background-color: color-mix(in srgb, var(--success) 18%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="hover:bg-rose-"]:hover) {
  background-color: color-mix(in srgb, #f43f5e 18%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-900),
:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-800),
:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-700) {
  color: var(--text) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-600),
:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-500),
:global(:root[data-theme='dark'] .device-dialog-surface .text-slate-400) {
  color: var(--text-muted) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .border-slate-100),
:global(:root[data-theme='dark'] .device-dialog-surface .border-slate-200),
:global(:root[data-theme='dark'] .device-dialog-surface .divide-slate-100) {
  border-color: var(--border) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-panel) {
  border-color: color-mix(in srgb, var(--accent-strong) 42%, var(--border)) !important;
  background-color: color-mix(in srgb, var(--accent-strong) 10%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-security) {
  border-color: color-mix(in srgb, var(--accent-strong) 34%, var(--border)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-security > summary) {
  color: color-mix(in srgb, #a78bfa 72%, var(--text)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface input),
:global(:root[data-theme='dark'] .device-dialog-surface select),
:global(:root[data-theme='dark'] .device-dialog-surface textarea) {
  border-color: var(--border) !important;
  background: var(--surface-control) !important;
  color: var(--text) !important;
  color-scheme: dark;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict) {
  border-color: color-mix(in srgb, var(--warning) 55%, var(--border)) !important;
  background-color: color-mix(in srgb, var(--warning) 14%, var(--surface-elevated)) !important;
  color: var(--text) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict button) {
  border-color: color-mix(in srgb, var(--warning) 58%, var(--border)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest) {
  border-color: var(--warning) !important;
  background-color: #451a03 !important;
  color: #fef3c7 !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest:hover) {
  background-color: #78350f !important;
  color: var(--warning-surface) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest:focus-visible) {
  outline: 2px solid var(--warning);
  outline-offset: 2px;
}

</style>
