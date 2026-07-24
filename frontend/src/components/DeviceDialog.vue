<script setup lang="ts">
import {ref, watch, computed, nextTick} from 'vue'
import {useI18n} from 'vue-i18n'
import { ElMessage } from 'element-plus'
import { useModalAccessibility } from '@/composables/useModalAccessibility'

import type {DeviceManifest, DeviceTemplate, InternalVariable} from '../types/device'
import type {DeviceNode} from '../types/node'
import type {DeviceEdge} from '../types/edge'
import type {Specification} from '../types/spec'
import { buildSpecFormula } from '@/utils/spec'
import { resolveImpactEnvironmentDefinition } from '@/utils/device'
import { specTemplateDetails } from '@/assets/config/specTemplates'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'
import { resolveEffectiveNodeState } from '@/utils/canvas/nodeState'
import {
  PRIVACY_OPTIONS,
  TRUST_OPTIONS,
  buildDeviceRuntimeConfig,
  createDeviceRuntimeDraft,
  getTemplateLocalVariables,
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
  rules?: DeviceEdge[]
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

const close = () => {
  innerVisible.value = false
  emit('update:visible', false)
}

const onDelete = () => emit('delete')
const onRename = () => emit('rename')

const isDialogOpen = computed(() => innerVisible.value && props.suspended !== true)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, close)

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
let runtimeSaveDraft: DeviceRuntimeDraft | null = null

const cloneRuntimeDraft = (draft: DeviceRuntimeDraft): DeviceRuntimeDraft => ({
  state: draft.state,
  currentStateTrust: draft.currentStateTrust,
  currentStatePrivacy: draft.currentStatePrivacy,
  variables: { ...draft.variables },
  variableTrusts: { ...draft.variableTrusts },
  privacies: { ...draft.privacies }
})

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
) => left.state === right.state
  && left.currentStateTrust === right.currentStateTrust
  && left.currentStatePrivacy === right.currentStatePrivacy

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
  right: Record<string, string>
) => {
  const keys = new Set([...Object.keys(left), ...Object.keys(right)])
  return [...keys].every(key => (left[key] ?? '') === (right[key] ?? ''))
}

const runtimeDraftsEqual = (left: DeviceRuntimeDraft, right: DeviceRuntimeDraft) =>
  left.state === right.state
  && left.currentStateTrust === right.currentStateTrust
  && left.currentStatePrivacy === right.currentStatePrivacy
  && runtimeDraftRecordsEqual(left.variables, right.variables)
  && runtimeDraftRecordsEqual(left.variableTrusts, right.variableTrusts)
  && runtimeDraftRecordsEqual(left.privacies, right.privacies)

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

const variableInputPlaceholder = (variable: InternalVariable) => {
  if (templateVariableUsesNumericBounds(variable)) {
    const lower = variable.LowerBound ?? '-∞'
    const upper = variable.UpperBound ?? '∞'
    return `${lower} - ${upper}`
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

  return draft
}

const replaceRuntimeDraft = (draft: DeviceRuntimeDraft) => {
  runtimeDraft.value = cloneRuntimeDraft(draft)
  runtimeDraftBaseline.value = cloneRuntimeDraft(draft)
  runtimeDraftConflictFields.value = []
  runtimeSchemaConflict.value = false
}

const syncRuntimeDraftFromNode = () => {
  runtimeSaveDraft = null
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
  runtimeSaveDraft = null
  const incomingDraft = createRuntimeDraftFromNode()
  const baselineDraft = runtimeDraftBaseline.value
  const currentDraft = runtimeDraft.value
  const mergedDraft = cloneRuntimeDraft(incomingDraft)
  const preserveChanged = (currentValue = '', baselineValue = '') => currentValue !== baselineValue

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
    if (preserveChanged(currentTrust, baselineDraft.variableTrusts[name] ?? '')
      && (!currentTrust || TRUST_OPTIONS.some(option => option === currentTrust))) {
      mergedDraft.variableTrusts[name] = currentTrust
    }
    const currentPrivacy = currentDraft.privacies[name] ?? ''
    if (preserveChanged(currentPrivacy, baselineDraft.privacies[name] ?? '')
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
    savedValue?: string
  ) => {
    if (existingConflicts.has(path)) {
      if (currentValue === incomingValue) return incomingValue
      nextConflicts.add(path)
      return currentValue
    }
    // A matching save snapshot acknowledges the submitted value. Any difference in the
    // current draft was typed after Save and remains a local edit, not an external conflict.
    if (runtimeSaveDraft && incomingValue === savedValue && currentValue !== incomingValue) {
      return currentValue
    }
    if (currentValue === baselineValue) return incomingValue
    if (incomingValue === baselineValue || currentValue === incomingValue) return currentValue
    nextConflicts.add(path)
    return currentValue
  }

  const mergedDraft = createDeviceRuntimeDraft()
  const baselineStateContext = runtimeStateContext(baselineDraft)
  const currentStateContext = runtimeStateContext(currentDraft)
  const incomingStateContext = runtimeStateContext(incomingDraft)
  const savedStateContext = runtimeSaveDraft
    ? runtimeStateContext(runtimeSaveDraft)
    : null
  let mergedStateContext = currentStateContext
  if (existingConflicts.has(RUNTIME_STATE_CONTEXT_CONFLICT)) {
    if (runtimeStateContextsEqual(currentStateContext, incomingStateContext)) {
      mergedStateContext = incomingStateContext
    } else {
      nextConflicts.add(RUNTIME_STATE_CONTEXT_CONFLICT)
    }
  } else if (savedStateContext
    && runtimeStateContextsEqual(incomingStateContext, savedStateContext)
    && !runtimeStateContextsEqual(currentStateContext, incomingStateContext)) {
    mergedStateContext = currentStateContext
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
        runtimeSaveDraft?.[field][name]
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
    if (!saving) runtimeSaveDraft = null
  },
  { flush: 'post' }
)

const saveRuntime = () => {
  const template = currentTemplate.value
  const node = currentNode.value
  if (!template || !node || !props.nodeId) return
  if (hasRuntimeDraftConflict.value) {
    ElMessage.warning(t('app.deviceRuntimeConflictUnresolved'))
    return
  }

  const runtime = buildDeviceRuntimeConfig(template, runtimeDraft.value, {
    includeEmptyCollections: true,
    variableScope: 'local'
  }) || {}
  const validationMessage = validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'local' })
  if (validationMessage) {
    ElMessage.warning(validationMessage)
    return
  }

  runtimeSaveDraft = cloneRuntimeDraft(runtimeDraft.value)
  emit('save-runtime', props.nodeId, runtime)
  void nextTick(() => {
    // The parent can reject the request before entering its saving state (for example when
    // playback locks mutations). Do not leave that non-request fencing later refreshes.
    if (!props.runtimeSaving) runtimeSaveDraft = null
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
      if (iv.Values && iv.Values.length) valDisplay = iv.Values.map(formatDeviceModelToken).join(' / ')
      else if (iv.LowerBound !== undefined && iv.UpperBound !== undefined) valDisplay = `[${iv.LowerBound}, ${iv.UpperBound}]`

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
        const range = definition?.Values?.length
          ? definition.Values.map(formatDeviceModelToken).join(' / ')
          : definition?.LowerBound !== undefined && definition?.UpperBound !== undefined
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
const getDeviceIcon = (deviceName: string) => {
  const name = deviceName.toLowerCase()
  
  // 传感器类
  if (name.includes('sensor') || name.includes('temperature') || name.includes('humidity') || name.includes('gas') || name.includes('smoke') || name.includes('motion') || name.includes('soil') || name.includes('illuminance')) {
    return 'sensors'
  }
  
  // 温度/恒温器
  if (name.includes('thermostat') || name.includes('weather')) {
    return 'thermostat'
  }
  
  // 灯/照明
  if (name.includes('light')) {
    return 'lightbulb'
  }
  
  // 开关
  if (name.includes('switch')) {
    return 'toggle_on'
  }
  
  // 空调
  if (name.includes('air conditioner') || name.includes('ac')) {
    return 'ac_unit'
  }
  
  // 空气净化器/通风
  if (name.includes('air purifier') || name.includes('ventilator') || name.includes('humidifier')) {
    return 'air'
  }
  
  // 窗帘/窗户
  if (name.includes('window shade') || name.includes('shade')) {
    return 'blinds'
  }
  if (name.includes('window')) {
    return 'window'
  }
  
  // 门/车库门
  if (name.includes('garage door')) {
    return 'garage'
  }
  if (name.includes('door')) {
    return 'door_front_door'
  }
  
  // 摄像头
  if (name.includes('camera')) {
    return 'videocam'
  }
  
  // 电视
  if (name.includes('tv') || name.includes('television')) {
    return 'tv'
  }
  
  // 手机
  if (name.includes('phone') || name.includes('mobile')) {
    return 'smartphone'
  }
  
  // 洗衣机/烘干机
  if (name.includes('washer') || name.includes('dryer')) {
    return 'local_laundry_service'
  }
  
  // 冰箱
  if (name.includes('refrigerator') || name.includes('fridge')) {
    return 'kitchen'
  }
  
  // 热水器
  if (name.includes('water heater') || name.includes('water')) {
    return 'hot_tub'
  }
  
  // 炊具/烤箱/咖啡机
  if (name.includes('oven') || name.includes('cooker') || name.includes('cooktop')) {
    return 'microwave'
  }
  if (name.includes('coffee')) {
    return 'coffee'
  }
  
  // 警报器
  if (name.includes('alarm') || name.includes('security')) {
    return 'security'
  }
  
  // 汽车
  if (name.includes('car') || name.includes('vehicle')) {
    return 'directions_car'
  }
  
  // 日历/时钟
  if (name.includes('calendar')) {
    return 'calendar_month'
  }
  if (name.includes('clock')) {
    return 'schedule'
  }
  
  // 社交媒体
  if (name.includes('weibo') || name.includes('twitter') || name.includes('facebook') || name.includes('email')) {
    return 'alternate_email'
  }
  
  // 泳池相关
  if (name.includes('pool') || name.includes('sprinkler')) {
    return 'pool'
  }
  
  // 家庭模式
  if (name.includes('home mode') || name.includes('home')) {
    return 'home'
  }
  
  return 'devices_other'
}

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
        nodes: props.nodes || [],
        deviceTemplates: props.deviceTemplates || []
      })

      return {
        id: spec.id,
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
    <transition name="modal-fade" appear>
      <div
        v-if="isDialogOpen"
        class="device-dialog-overlay"
        @keydown="handleModalKeydown"
      >
        <transition name="modal-scale" appear>
          <div
            :ref="setDialogRef"
            data-testid="device-dialog"
            class="device-dialog-surface bg-white w-full max-w-4xl rounded-2xl shadow-2xl overflow-hidden flex flex-col max-h-[calc(100vh-2rem)]"
            role="dialog"
            aria-modal="true"
            aria-labelledby="device-dialog-title"
            tabindex="-1"
          >

            <!-- Header -->
            <div class="device-dialog-header sticky top-0 z-10 flex items-center justify-between gap-3 border-b border-slate-200 bg-gradient-to-r from-white to-slate-50/50 px-4 py-4 shadow-sm sm:px-8 sm:py-6">
              <div class="flex min-w-0 items-center gap-3 sm:gap-4">
                <div class="flex h-12 w-12 shrink-0 items-center justify-center rounded-xl border-2 border-blue-200 bg-gradient-to-br from-blue-50 to-blue-100 shadow-lg sm:h-14 sm:w-14">
                  <span class="material-icons-round text-3xl text-blue-600">{{ getDeviceIcon(deviceName) }}</span>
                </div>
                <div class="min-w-0">
                  <h1 id="device-dialog-title" class="text-xl font-bold text-slate-900 leading-tight">{{ t('app.deviceInfo') }}</h1>
                  <div class="mt-1 flex min-w-0 items-center gap-2">
                    <p class="truncate text-sm font-medium text-slate-500" :title="label">{{ label }}</p>
                  </div>
                </div>
              </div>
              <button type="button" data-testid="device-dialog-close" @click="close" class="inline-flex min-h-11 min-w-11 shrink-0 items-center justify-center rounded-lg p-2 text-slate-400 transition-all hover:bg-slate-100 hover:text-slate-600" :aria-label="t('app.close')">
                <span class="material-icons-round text-xl" aria-hidden="true">close</span>
              </button>
            </div>

            <!-- Body -->
            <div class="device-dialog-body custom-scrollbar flex-1 space-y-6 overflow-y-auto px-4 py-5 sm:space-y-8 sm:px-8 sm:py-6">
              <div
                v-if="!manifest"
                data-testid="device-template-details-unavailable"
                class="rounded-lg border border-amber-300 bg-amber-50 px-4 py-3 text-sm leading-6 text-amber-900"
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
                <div class="overflow-hidden border border-slate-200 rounded-xl bg-white shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-slate-50 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider w-1/3">{{ t('app.property') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.value') }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100">
                      <!-- Template Name -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.name') }}</td>
                        <td class="px-4 py-3 text-sm font-bold text-slate-800">{{ basicInfo.name || deviceName }}</td>
                      </tr>
                      
                      <!-- Instance Name -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.instanceName') }}</td>
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ basicInfo.instanceName || label }}</td>
                      </tr>

                      <!-- Modes -->
                      <tr v-if="manifest" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.modes') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-1.5">
                            <template v-if="basicInfo.modes && basicInfo.modes.length">
                              <span
                                v-for="mode in basicInfo.modes"
                                :key="mode"
                                class="px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded-md font-medium border border-slate-200"
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
                      <tr v-if="manifest" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.initState') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex items-center gap-2">
                            <span class="w-2 h-2 rounded-full bg-green-500 animate-pulse"></span>
                    <span class="text-sm font-medium text-slate-700" :title="basicInfo.initStateLabel">{{ basicInfo.initStateLabel }}</span>
                  </div>
                        </td>
                      </tr>

                      <!-- Description -->
                      <tr v-if="manifest" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.description') }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 leading-relaxed">{{ basicInfo.description || '-' }}</td>
                      </tr>

                      <!-- Impacted Variables -->
                      <tr v-if="basicInfo.impactedVariables && basicInfo.impactedVariables.length" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.impactedVariables') }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-2">
                      <span v-for="variable in basicInfo.impactedVariables" :key="variable"
                                  class="px-2.5 py-1 bg-blue-50 text-blue-700 text-xs font-medium rounded-md border border-blue-100">
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
                    <code class="break-all rounded bg-white px-2 py-1 text-[11px] text-slate-700">{{ nodeId }}</code>
                  </div>
                </details>
              </section>

              <!-- Instance runtime overrides -->
              <section v-if="hasRuntimeFields" data-testid="device-instance-runtime">
                <div class="flex items-center justify-between gap-3 mb-4">
                  <div class="flex items-center gap-2 min-w-0">
                    <div class="w-1 h-5 bg-purple-500 rounded-full"></div>
                    <div class="min-w-0">
                      <h2 class="text-lg font-semibold text-slate-800">{{ t('app.instanceRuntime') }}</h2>
                      <p class="text-xs text-slate-500 mt-0.5">{{ t('app.instanceRuntimeHint') }}</p>
                    </div>
                  </div>
                  <button
                    type="button"
                    data-testid="device-runtime-save"
                    @click="saveRuntime"
                    :disabled="runtimeSaving || hasRuntimeDraftConflict"
                    class="inline-flex min-h-11 shrink-0 items-center justify-center gap-2 rounded-lg bg-purple-600 px-4 py-2 text-xs font-bold text-white shadow-sm transition-all hover:bg-purple-700 disabled:cursor-not-allowed disabled:bg-purple-300"
                  >
                    <span v-if="runtimeSaving" class="h-3.5 w-3.5 animate-spin rounded-full border-2 border-white/40 border-t-white" aria-hidden="true"></span>
                    <span v-else class="material-symbols-outlined text-sm" aria-hidden="true">save</span>
                    {{ t('app.saveInstanceConfig') }}
                  </button>
                </div>

                <div
                  v-if="hasRuntimeDraftConflict"
                  data-testid="device-runtime-conflict"
                  class="device-runtime-conflict mb-3 rounded-lg border border-amber-300 bg-amber-50 px-3 py-3 text-sm text-amber-950"
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
                      class="device-runtime-adopt-latest min-h-11 rounded-md border border-amber-400 bg-white px-3 py-1.5 text-xs font-semibold text-amber-950 hover:bg-amber-100"
                      @click="adoptLatestRuntimeDraft"
                    >
                      {{ t('app.deviceRuntimeUseLatest') }}
                    </button>
                    <button
                      type="button"
                      data-testid="device-runtime-keep-local"
                      class="min-h-11 rounded-md bg-amber-700 px-3 py-1.5 text-xs font-semibold text-white hover:bg-amber-800"
                      @click="keepLocalRuntimeDraft"
                    >
                      {{ runtimeSchemaConflict
                        ? t('app.deviceRuntimeContinueCompatible')
                        : t('app.deviceRuntimeKeepMine') }}
                    </button>
                  </div>
                </div>

                <div class="device-runtime-panel space-y-3 rounded-xl border border-purple-100 bg-purple-50/40 p-4">
                  <div v-if="runtimeHasModes" class="grid grid-cols-1 gap-3">
                    <label class="min-w-0">
                      <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.initialState') }}</span>
                      <select
                        v-model="runtimeDraft.state"
                        data-testid="device-runtime-state"
                        class="w-full rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700 shadow-sm focus:border-purple-400 focus:ring-2 focus:ring-purple-100/60"
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
                      class="rounded-lg border border-slate-200 bg-white p-3 shadow-sm"
                    >
                      <div class="mb-2 flex min-w-0 items-center justify-between gap-2">
                        <div class="min-w-0">
                          <span class="block truncate text-xs font-bold text-slate-700" :title="formatDeviceModelToken(variable.Name)">{{ formatDeviceModelToken(variable.Name) }}</span>
                          <span class="text-[10px] font-semibold text-slate-400">
                            {{ variable.IsInside !== true ? t('app.environmentVariable') : t('app.internalVariable') }}
                          </span>
                        </div>
                        <span v-if="templateVariableUsesNumericBounds(variable)" class="shrink-0 text-[10px] font-semibold text-slate-400">
                          {{ variableInputPlaceholder(variable) }}
                        </span>
                      </div>

                      <div class="grid grid-cols-1 gap-2">
                        <label class="min-w-0">
                          <span class="mb-1 block text-[10px] font-bold uppercase text-slate-400">{{ t('app.variableValue') }}</span>
                          <select
                            v-if="templateVariableHasEnumValues(variable)"
                            v-model="runtimeDraft.variables[variable.Name]"
                            :data-testid="`device-runtime-variable-${variable.Name}`"
                            class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700"
                          >
                            <option value="">{{ t('app.modelControlled') }}</option>
                            <option v-for="value in variable.Values" :key="value" :value="String(value)">{{ formatDeviceModelToken(value) }}</option>
                          </select>
                          <input
                            v-else
                            v-model="runtimeDraft.variables[variable.Name]"
                            :data-testid="`device-runtime-variable-${variable.Name}`"
                            class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700 placeholder:text-slate-400"
                            :placeholder="variableInputPlaceholder(variable)"
                            type="text"
                          />
                        </label>

                      </div>
                    </div>
                  </div>

                  <details class="device-runtime-security border-t border-purple-100 pt-3" data-testid="device-runtime-advanced-security">
                    <summary class="flex cursor-pointer list-none items-center justify-between gap-3 text-xs font-bold text-purple-700">
                      <span class="inline-flex items-center gap-2">
                        <span class="material-symbols-outlined text-base" aria-hidden="true">tune</span>
                        {{ t('app.advancedTrustPrivacyOverrides') }}
                      </span>
                      <span class="material-symbols-outlined text-base" aria-hidden="true">expand_more</span>
                    </summary>
                    <p class="mt-2 text-[11px] leading-4 text-slate-500">{{ t('app.advancedTrustPrivacyOverridesHint') }}</p>

                    <div v-if="runtimeHasModes" class="mt-3 grid grid-cols-1 gap-3 sm:grid-cols-2">
                      <label class="min-w-0">
                        <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.stateTrust') }}</span>
                        <select
                          v-model="runtimeDraft.currentStateTrust"
                          data-testid="device-runtime-state-trust"
                          class="w-full rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700"
                        >
                          <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${runtimeStateTemplateDefaults.trust}`) }) }}</option>
                          <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                        </select>
                      </label>

                      <label class="min-w-0">
                        <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.statePrivacy') }}</span>
                        <select
                          v-model="runtimeDraft.currentStatePrivacy"
                          data-testid="device-runtime-state-privacy"
                          class="w-full rounded-lg border border-slate-200 bg-white px-3 py-2 text-sm text-slate-700"
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
                          <span class="mb-1 block text-[10px] font-bold uppercase text-slate-400">{{ t('app.variableTrust') }}</span>
                          <select
                            v-model="runtimeDraft.variableTrusts[variable.Name]"
                            :data-testid="`device-runtime-variable-trust-${variable.Name}`"
                            class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-2 text-xs text-slate-700"
                          >
                            <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${variable.Trust}`) }) }}</option>
                            <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                          </select>
                        </label>
                        <label class="min-w-0">
                          <span class="mb-1 block text-[10px] font-bold uppercase text-slate-400">{{ t('app.privacy') }}</span>
                          <select
                            v-model="runtimeDraft.privacies[variable.Name]"
                            :data-testid="`device-runtime-privacy-${variable.Name}`"
                            class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-2 text-xs text-slate-700"
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
                <div class="overflow-x-auto border border-slate-200 rounded-xl shadow-sm">
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
                    <tbody class="divide-y divide-slate-100 bg-white">
                      <tr v-for="(v, idx) in variables" :key="idx" class="hover:bg-blue-50/30 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700" :title="v.displayName">{{ v.displayName }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 font-mono" :title="v.range || '-'">{{ v.range || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="v.trust === 'trusted' ? 'bg-green-100 text-green-700' :
                                    v.trust === 'untrusted' ? 'bg-red-100 text-red-700' :
                                    'bg-slate-100 text-slate-600'">
                            {{ v.trust ? t(`app.${v.trust}`) : '-' }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="v.privacy === 'private' ? 'bg-purple-100 text-purple-700' :
                                    v.privacy === 'public' ? 'bg-blue-100 text-blue-700' :
                                    'bg-slate-100 text-slate-600'">
                            {{ v.privacy ? t(`app.${v.privacy}`) : '-' }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span
                            v-if="v.falsifiableWhenCompromised !== null"
                            class="inline-flex items-center gap-1 rounded px-2 py-0.5 text-xs font-medium"
                            :class="v.falsifiableWhenCompromised ? 'bg-amber-100 text-amber-800' : 'bg-slate-100 text-slate-600'"
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
                            :class="v.isInternal ? 'bg-violet-100 text-violet-700' : 'bg-emerald-100 text-emerald-800'"
                          >
                            {{ v.type }}
                          </span>
                          <span
                            v-if="v.affectsEnvironment"
                            class="inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium bg-blue-100 text-blue-700"
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
                <div class="overflow-x-auto border border-slate-200 rounded-xl shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-gradient-to-r from-slate-50 to-slate-100 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.name') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.description') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.trust') }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.privacy') }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100 bg-white">
                      <tr v-if="states.length === 0">
                        <td class="px-4 py-8 text-center text-slate-400 text-sm italic" colspan="4">
                          {{ t('app.noData') }}
                        </td>
                      </tr>
                      <tr v-for="(s, idx) in states" :key="idx" class="hover:bg-blue-50/30 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700" :title="s.displayName">{{ s.displayName }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">{{ s.description || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="s.trust === 'trusted' ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'">
                            {{ t(`app.${s.trust}`) }}
                          </span>
                        </td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="s.privacy === 'public' ? 'bg-blue-100 text-blue-700' : 
                                    s.privacy === 'private' ? 'bg-purple-100 text-purple-700' : 
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
              <section v-if="apis.length > 0" data-testid="device-dialog-apis">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-emerald-500 rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceApis') }}</h2>
                </div>
                <div class="grid grid-cols-1 md:grid-cols-2 gap-4">
                  <div
                    v-for="(api, idx) in apis"
                    :key="idx"
                    class="bg-white border border-slate-200 rounded-xl p-4 hover:shadow-md transition-all hover:border-emerald-200 group"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex items-center gap-2">
                        <div class="w-8 h-8 bg-emerald-50 rounded-lg flex items-center justify-center group-hover:bg-emerald-100 transition-colors">
                        <span class="material-icons-round text-emerald-600 text-lg">api</span>
                        </div>
                        <span class="text-sm font-bold text-slate-800" :title="api.displayName">{{ api.displayName }}</span>
                      </div>
                      <div class="flex flex-wrap justify-end gap-1">
                        <span v-if="api.signal" class="text-[10px] px-1.5 py-0.5 bg-amber-100 text-amber-700 rounded font-medium border border-amber-200">
                          {{ t('app.signal') }}
                        </span>
                        <span v-if="api.acceptsContent" class="text-[10px] px-1.5 py-0.5 bg-fuchsia-100 text-fuchsia-700 rounded font-medium border border-fuchsia-200">
                          {{ t('app.acceptsContentSensitivity') }}
                        </span>
                      </div>
                    </div>
                    <p v-if="api.description" class="text-xs text-slate-600 mb-4 line-clamp-2">
                      {{ api.description }}
                    </p>
                    <div class="flex items-center gap-2 text-xs bg-slate-50 p-2 rounded-lg border border-slate-100 min-w-0">
                      <div class="flex items-center gap-1 text-slate-500 min-w-0">
                        <span class="material-icons-round text-sm font-bold">play_arrow</span>
                        <span class="font-medium text-slate-700 truncate max-w-[10rem]" :title="api.startStateLabel">{{ api.startStateLabel }}</span>
                      </div>
                      <span class="text-slate-300 shrink-0">→</span>
                      <div class="flex items-center gap-1 text-slate-500 min-w-0">
                        <span class="material-icons-round text-sm font-bold">stop</span>
                        <span class="font-medium text-slate-700 truncate max-w-[12rem]" :title="api.endStateLabel">{{ api.endStateLabel }}</span>
                      </div>
                      <div class="flex-1"></div>
                      <span class="text-[10px] text-slate-400 uppercase font-semibold tracking-wider shrink-0">{{ t('app.trigger') }}: {{ api.trigger }}</span>
                    </div>
                  </div>
                </div>
              </section>

              <!-- Specifications Section -->
              <section v-if="manifest && deviceSpecs.length > 0">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-rose-500 rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.specifications') }}</h2>
                </div>
                  <div v-if="deviceSpecs.length === 0" class="bg-slate-50 border border-slate-200 rounded-xl p-8 text-center">
                  <span class="material-icons-round text-slate-300 text-4xl mb-2 block">verified</span>
                    <p class="text-sm text-slate-500">{{ t('app.noSpecs') }}</p>
                </div>
                <div v-else class="space-y-3">
                  <div
                    v-for="spec in deviceSpecs"
                    :key="spec.id"
                    class="bg-white border border-slate-200 rounded-xl p-4 transition-all hover:shadow-md hover:border-rose-200"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex items-center gap-2 flex-1">
                        <div class="w-8 h-8 bg-rose-50 rounded-lg flex items-center justify-center">
                          <span class="material-icons-round text-rose-500 text-lg">verified</span>
                        </div>
                        <div class="flex-1 min-w-0">
                          <span class="text-sm font-bold block truncate text-slate-800">{{ spec.type }}</span>
                          <span class="text-xs text-slate-500 mt-0.5 block truncate">
                            <span class="font-medium text-slate-400">{{ t('app.target') }}:</span> {{ spec.devices }}
                          </span>
                        </div>
                      </div>
                    </div>
                    <div class="bg-slate-50 rounded-lg p-3 border border-slate-100">
                      <div class="mb-1 flex items-center gap-2">
                        <p class="text-[11px] text-slate-400 uppercase font-bold tracking-wider">{{ t('app.formulaPreview') }}</p>
                        <span class="rounded bg-white px-1.5 py-0.5 text-[10px] font-bold text-slate-600">{{ spec.formulaKind }}</span>
                      </div>
                      <div class="text-xs text-slate-700 leading-relaxed font-mono break-all">
                      {{ spec.formula }}
                      </div>
                      <details class="mt-2 text-[11px] text-slate-500">
                        <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                        <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                          <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                          <code class="break-all rounded bg-white px-2 py-1 text-[11px] text-slate-700">{{ spec.id }}</code>
                        </div>
                      </details>
                    </div>
                  </div>
                </div>
              </section>
            </div>

            <!-- Footer -->
            <div class="device-dialog-footer flex flex-col items-stretch justify-end gap-2 border-t border-slate-200 bg-gradient-to-r from-slate-50 to-white px-4 py-4 sm:flex-row sm:items-center sm:gap-3 sm:px-8 sm:py-5">
              <button
                v-if="nodeId"
                type="button"
                data-testid="device-rename"
                @click="onRename"
                class="flex min-h-11 w-full items-center justify-center gap-2 rounded-lg border border-blue-200 bg-blue-50 px-5 py-2.5 text-sm font-semibold text-blue-800 transition-all hover:bg-blue-100 sm:w-auto"
              >
                <span class="material-icons-round text-lg text-blue-600" aria-hidden="true">edit</span>
                {{ t('app.rename') }}
              </button>
                <button type="button" data-testid="device-dialog-footer-close" @click="close" class="min-h-11 w-full rounded-lg border border-slate-200 bg-white px-6 py-2.5 text-sm font-semibold text-slate-700 shadow-sm transition-all hover:bg-slate-200 hover:text-slate-900 sm:w-auto">
                  {{ t('app.close') }}
                </button>
              <button
                type="button"
                data-testid="device-delete"
                @click="onDelete"
                :disabled="deleteLoading"
                :aria-busy="deleteLoading"
                class="flex min-h-11 w-full items-center justify-center gap-2 rounded-lg border border-rose-200 bg-rose-100 px-5 py-2.5 text-sm font-semibold text-rose-900 transition-all hover:bg-rose-200 disabled:cursor-wait disabled:opacity-60 sm:w-auto"
              >
                <span v-if="deleteLoading" class="h-4 w-4 animate-spin rounded-full border-2 border-rose-400/40 border-t-rose-700" aria-hidden="true"></span>
                <span v-else class="material-icons-round text-lg text-rose-600" aria-hidden="true">delete_outline</span>
                {{ deleteLoading ? t('app.loading') : t('app.deleteDevice') }}
              </button>
            </div>
          </div>
        </transition>
      </div>
    </transition>
  </teleport>
</template>

<style scoped>
.device-dialog-overlay {
  position: fixed;
  inset: 0;
  z-index: 2200;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow-y: auto;
  padding: 1rem;
  background: rgba(15, 23, 42, 0.36);
  backdrop-filter: blur(6px);
}

@media (max-width: 640px) {
  .device-dialog-overlay {
    padding: 0.75rem;
  }
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
  background-color: color-mix(in srgb, #3b82f6 18%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface [class*="hover:bg-emerald-"]:hover),
:global(:root[data-theme='dark'] .device-dialog-surface .group:hover [class*="group-hover:bg-emerald-"]) {
  background-color: color-mix(in srgb, #10b981 18%, var(--surface-elevated)) !important;
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
  border-color: color-mix(in srgb, #8b5cf6 42%, var(--border)) !important;
  background-color: color-mix(in srgb, #8b5cf6 10%, var(--surface-elevated)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-security) {
  border-color: color-mix(in srgb, #8b5cf6 34%, var(--border)) !important;
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
  border-color: color-mix(in srgb, #f59e0b 55%, var(--border)) !important;
  background-color: color-mix(in srgb, #f59e0b 14%, var(--surface-elevated)) !important;
  color: var(--text) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict button) {
  border-color: color-mix(in srgb, #f59e0b 58%, var(--border)) !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest) {
  border-color: #fbbf24 !important;
  background-color: #451a03 !important;
  color: #fef3c7 !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest:hover) {
  background-color: #78350f !important;
  color: #fffbeb !important;
}

:global(:root[data-theme='dark'] .device-dialog-surface .device-runtime-conflict .device-runtime-adopt-latest:focus-visible) {
  outline: 2px solid #fbbf24;
  outline-offset: 2px;
}

/* Modal Transitions */
.modal-fade-enter-active,
.modal-fade-leave-active {
  transition: opacity 0.3s ease;
}

.modal-fade-enter-from,
.modal-fade-leave-to {
  opacity: 0;
}

.modal-scale-enter-active,
.modal-scale-leave-active {
  transition: transform 0.3s ease, opacity 0.3s ease;
}

.modal-scale-enter-from,
.modal-scale-leave-to {
  opacity: 0;
  transform: scale(0.95);
}

@media (prefers-reduced-motion: reduce) {
  .modal-fade-enter-active,
  .modal-fade-leave-active,
  .modal-scale-enter-active,
  .modal-scale-leave-active {
    transition: none;
  }
}

/* Custom Scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 6px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: transparent;
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: #cbd5e1;
  border-radius: 10px;
}

:global(:root[data-theme='dark'] .device-dialog-surface .custom-scrollbar::-webkit-scrollbar-thumb) {
  background: #475569;
}
</style>
