<script setup lang="ts">
import { ref, reactive, computed, onBeforeUnmount, onMounted, useAttrs, watch } from 'vue'
import { ElMessage as ElMessageRaw } from 'element-plus'
import { 
  specTemplateDetails, 
  relationOperators, 
  targetTypes 
} from '@/assets/config/specTemplates.ts'
import type { 
  SpecTemplateId, 
  SpecTemplateType, 
  SpecCondition, 
  SpecSide,
} from '@/types/spec'
import type { DeviceTemplate, InternalVariable } from '@/types/device'
import { useI18n } from 'vue-i18n'
import { getDefaultDeviceIcon } from '@/utils/device'
import {
  PRIVACY_OPTIONS,
  TRUST_OPTIONS,
  buildDeviceRuntimeConfig,
  createDeviceRuntimeDraft,
  findTemplateStatePrivacy,
  findTemplateStateTrust,
  getTemplateEnvironmentVariables,
  getTemplateLocalVariables,
  getTemplateWorkingStates,
  materializeDeviceRuntimeConfig,
  resetDeviceRuntimeDraft,
  templateVariableHasEnumValues,
  templateVariableUsesNumericBounds,
  validateDeviceRuntimeConfig,
  type DeviceRuntimeConfig
} from '@/utils/deviceRuntime'
import { buildSpecFormula } from '@/utils/spec'
import {
  mergeSourcedEnvironmentPatches,
  type EnvironmentPatchConflict
} from '@/utils/deviceImportEnvironment'
import boardApi, {
  BOARD_RESPONSE_INCOMPLETE_CODE,
  type DefaultTemplateResetResult,
  type DeviceTemplateDeletionResult
} from '@/api/board'
import type { ModelEnvironmentVariable } from '@/types/model'
import { deviceLabelKey, reserveUniqueDeviceLabel } from '@/utils/canvas/nodeCreate'
import { localizedErrorMessage } from '@/utils/userMessage'
import { useModalAccessibility } from '@/composables/useModalAccessibility'

defineOptions({ inheritAttrs: false })
const attrs = useAttrs()

// Element-Plus typings vary by version; we use an `any` alias to keep runtime behavior (e.g. `center`) without TS errors.
const ElMessage = ElMessageRaw as any
const { t, locale } = useI18n()

const targetTypeLabelKeys: Record<string, string> = {
  state: 'app.state',
  mode: 'app.modes',
  variable: 'app.variable',
  api: 'app.actionEvent',
  trust: 'app.trust',
  privacy: 'app.privacy'
}

const localizedTargetTypes = computed(() =>
  targetTypes
    .filter(type => specForm.templateId !== '7' || !['trust', 'privacy'].includes(type.value))
    .map(type => ({
    ...type,
    label: targetTypeLabelKeys[type.value]
      ? t(targetTypeLabelKeys[type.value])
      : type.label
  }))
)

// Props
interface Props {
  deviceTemplates?: any[]
  nodes?: any[]
  edges?: any[]
  canvasPan?: { x: number; y: number }
  canvasZoom?: number
  collapsed?: boolean
  width?: number
  activeSection?: string
  templatesLoading?: boolean
  readOnly?: boolean
  readOnlyMessage?: string
  runBoardMutation?: <T>(work: () => Promise<T>) => Promise<T>
}

const props = withDefaults(defineProps<Props>(), {
  deviceTemplates: () => [],
  nodes: () => [],
  edges: () => [],
  canvasPan: () => ({ x: 0, y: 0 }),
  canvasZoom: 1,
  width: 320,
  activeSection: 'templates',
  templatesLoading: false,
  readOnly: false
})

const ensureWritable = (): boolean => {
  if (!props.readOnly) return true
  ElMessage.warning({
    message: props.readOnlyMessage || t('app.playbackReadOnlyCloseFirst'),
    type: 'warning'
  })
  return false
}

const runBoardMutation = <T,>(work: () => Promise<T>): Promise<T> =>
  props.runBoardMutation ? props.runBoardMutation(work) : work()

type ControlCenterSection = 'devices' | 'templates' | 'rules' | 'specs'
type DeviceCreateMode = 'single' | 'batch' | 'import'

type DeviceCreateItem = {
  template: DeviceTemplate
  customName: string
  runtime?: DeviceRuntimeConfig
}

type MutationCompletion = (saved: boolean) => void

type DeviceCreateItemsPayload = {
  items: DeviceCreateItem[]
  environmentVariables?: ModelEnvironmentVariable[]
  complete: MutationCompletion
}

const emit = defineEmits<{
  'create-device': [data: DeviceCreateItem & { complete: MutationCompletion }]
  'create-devices': [data: DeviceCreateItemsPayload]
  'template-drag-start': [templateName: string]
  'template-drag-end': []
  'open-rule-builder': []
  'add-spec': [data: {
    templateId: string,
    templateType: string,
    devices: Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>,
    formula: string,
    aConditions: SpecCondition[],
    ifConditions: SpecCondition[],
    thenConditions: SpecCondition[],
    complete: MutationCompletion
  }]
  'replace-template-catalog': [templates: DeviceTemplate[]]
  'replace-template-state': [data: {
    templates: DeviceTemplate[]
    environmentVariables: ModelEnvironmentVariable[]
  }]
  'verify': []
  'simulate': [data: {
    steps: number
    isAttack: boolean
    attackBudget: number
    enablePrivacy: boolean
  }]
  'update:collapsed': [value: boolean]
  'update:active-section': [value: ControlCenterSection]
}>()

const deviceNodes = computed(() => props.nodes || [])

// Device form data
const deviceForm = reactive({
  name: '',
  type: '',
  id: 'AUTO'
})

const singleDeviceRuntime = reactive(createDeviceRuntimeDraft())
const creatingSingleDevice = ref(false)
const creatingMultipleDevices = ref(false)
const creatingSpecification = ref(false)

const deviceCreateMode = ref<DeviceCreateMode>('single')
const batchDeviceForm = reactive({
  type: '',
  prefix: '',
  count: 3
})
const importDeviceForm = reactive({
  text: ''
})

const MAX_BATCH_DEVICE_COUNT = 50

const normalizeName = (value: unknown) => String(value ?? '').trim()

const existingDeviceLabels = computed(() =>
  new Set(deviceNodes.value.map((node: any) => deviceLabelKey(node.label)).filter(Boolean))
)

const singleDeviceNameConflict = computed(() => {
  const key = deviceLabelKey(deviceForm.name)
  return Boolean(key && existingDeviceLabels.value.has(key))
})

const getUniqueDeviceName = (baseName: string, reserved: Set<string>) => {
  return reserveUniqueDeviceLabel(baseName, reserved)
}

const findTemplateByName = (name: string) => {
  const target = normalizeName(name).toLowerCase()
  if (!target) return null
  return props.deviceTemplates.find((tpl: any) =>
    [tpl.name, tpl.manifest?.Name]
      .some(candidate => normalizeName(candidate).toLowerCase() === target)
  ) ?? null
}

const selectedDeviceTemplate = computed<DeviceTemplate | null>(() =>
  findTemplateByName(deviceForm.type) as DeviceTemplate | null
)

const selectedDeviceManifest = computed(() => selectedDeviceTemplate.value?.manifest ?? null)

const selectedWorkingStates = computed(() => getTemplateWorkingStates(selectedDeviceTemplate.value))
const selectedInternalVariables = computed(() => getTemplateLocalVariables(selectedDeviceTemplate.value))

const selectedTemplateHasModes = computed(() => {
  const manifest = selectedDeviceManifest.value
  return Array.isArray(manifest?.Modes)
    && manifest.Modes.length > 0
    && selectedWorkingStates.value.length > 0
})

const hasSingleDeviceRuntimeFields = computed(() =>
  Boolean(selectedDeviceTemplate.value && (selectedTemplateHasModes.value || selectedInternalVariables.value.length > 0))
)

const resetSingleDeviceRuntime = () => {
  resetDeviceRuntimeDraft(singleDeviceRuntime, selectedDeviceTemplate.value)
}

watch(() => deviceForm.type, resetSingleDeviceRuntime)

watch(() => singleDeviceRuntime.state, () => {
  if (!selectedTemplateHasModes.value) return
  singleDeviceRuntime.currentStateTrust = ''
  singleDeviceRuntime.currentStatePrivacy = ''
})

const variableInputPlaceholder = (variable: InternalVariable) => {
  if (templateVariableUsesNumericBounds(variable)) {
    const lower = variable.LowerBound ?? '-∞'
    const upper = variable.UpperBound ?? '∞'
    return `${lower} - ${upper}`
  }
  return t('app.enterValuePlaceholder')
}

const buildRuntimeConfig = (template: DeviceTemplate, runtime = singleDeviceRuntime): DeviceRuntimeConfig | undefined => {
  return buildDeviceRuntimeConfig(template, runtime, { variableScope: 'local' })
}

type DeviceImportRow = {
  source: string
  templateName: string
  name: string
  customName?: string
  template?: any
  runtime?: DeviceRuntimeConfig
  environmentVariables?: ModelEnvironmentVariable[]
  error?: string
  warning?: string
}

const DEVICE_IMPORT_TEMPLATE_KEYS = new Set(['template', 'templatename', 'type'])
const DEVICE_IMPORT_NAME_KEYS = new Set(['name', 'label', 'devicename'])
const DEVICE_IMPORT_TEMPLATE_ALIASES = ['template', 'templateName', 'type'] as const
const DEVICE_IMPORT_NAME_ALIASES = ['name', 'label', 'deviceName'] as const
const DEVICE_IMPORT_JSON_KEYS = new Set([
  'template', 'templateName', 'type',
  'name', 'label', 'deviceName',
  'state', 'currentStateTrust', 'currentStatePrivacy', 'variables', 'privacies'
])
const DEVICE_IMPORT_VARIABLE_KEYS = new Set(['name', 'value', 'trust'])
const DEVICE_IMPORT_PRIVACY_KEYS = new Set(['name', 'privacy'])

const normalizeImportKey = (value: string) =>
  normalizeName(value).toLowerCase().replace(/[\s_-]/g, '')

const findUnknownImportField = (value: Record<string, unknown>, allowed: Set<string>) =>
  Object.keys(value).find(key => !allowed.has(key))

const makeImportError = (source: string, error: string): DeviceImportRow => ({
  source,
  templateName: '',
  name: '',
  customName: '',
  template: null,
  error
})

const parseJsonImportString = (
  value: unknown,
  source: string,
  field: string
): { value: string; error?: string } => {
  if (value === undefined || value === null) return { value: '' }
  if (typeof value !== 'string') {
    return {
      value: '',
      error: t('app.deviceImportJsonStringRequired', { source, field })
    }
  }
  return { value: value.trim() }
}

const readJsonImportAlias = (
  item: Record<string, unknown>,
  aliases: readonly string[],
  source: string
): { value: string; error?: string } => {
  const supplied = aliases.filter(alias => Object.prototype.hasOwnProperty.call(item, alias))
  if (supplied.length > 1) {
    return {
      value: '',
      error: t('app.deviceImportAliasConflict', { source, fields: supplied.join(', ') })
    }
  }
  const field = supplied[0]
  return field ? parseJsonImportString(item[field], source, field) : { value: '' }
}

const parseRuntimeList = (
  value: unknown,
  source: string,
  kind: 'variables' | 'privacies'
): { items?: any[]; error?: string } => {
  if (value === undefined || value === null) return { items: undefined }
  if (!Array.isArray(value)) {
    return { error: t('app.deviceImportRuntimeListRequired', { source, field: kind }) }
  }
  return { items: value }
}

const parseImportedRuntime = (item: any, source: string): { runtime?: DeviceRuntimeConfig; error?: string } => {
  const runtime: DeviceRuntimeConfig = {}

  if (item.state !== undefined && item.state !== null) {
    const parsed = parseJsonImportString(item.state, source, 'state')
    if (parsed.error) return { error: parsed.error }
    runtime.state = parsed.value
    if (!runtime.state) return { error: t('app.deviceImportRuntimeScalarRequired', { source, field: 'state' }) }
  }
  if (item.currentStateTrust !== undefined && item.currentStateTrust !== null) {
    const parsed = parseJsonImportString(item.currentStateTrust, source, 'currentStateTrust')
    if (parsed.error) return { error: parsed.error }
    runtime.currentStateTrust = parsed.value.toLowerCase()
    if (!runtime.currentStateTrust) {
      return { error: t('app.deviceImportRuntimeScalarRequired', { source, field: 'currentStateTrust' }) }
    }
  }
  if (item.currentStatePrivacy !== undefined && item.currentStatePrivacy !== null) {
    const parsed = parseJsonImportString(item.currentStatePrivacy, source, 'currentStatePrivacy')
    if (parsed.error) return { error: parsed.error }
    runtime.currentStatePrivacy = parsed.value.toLowerCase()
    if (!runtime.currentStatePrivacy) {
      return { error: t('app.deviceImportRuntimeScalarRequired', { source, field: 'currentStatePrivacy' }) }
    }
  }

  const variableList = parseRuntimeList(item.variables, source, 'variables')
  if (variableList.error) return { error: variableList.error }
  if (variableList.items) {
    runtime.variables = []
    for (const [index, variable] of variableList.items.entries()) {
      if (!variable || typeof variable !== 'object' || Array.isArray(variable)) {
        return { error: t('app.deviceImportRuntimeObjectRequired', { source, field: `variables[${index}]` }) }
      }
      const unknownField = findUnknownImportField(variable, DEVICE_IMPORT_VARIABLE_KEYS)
      if (unknownField) {
        return { error: t('app.deviceImportUnknownField', {
          source,
          field: `variables[${index}].${unknownField}`
        }) }
      }
      const parsedName = parseJsonImportString(variable.name, source, `variables[${index}].name`)
      const parsedValue = parseJsonImportString(variable.value, source, `variables[${index}].value`)
      const parsedTrust = parseJsonImportString(variable.trust, source, `variables[${index}].trust`)
      if (parsedName.error || parsedValue.error || parsedTrust.error) {
        return { error: parsedName.error || parsedValue.error || parsedTrust.error }
      }
      const name = parsedName.value
      const value = parsedValue.value
      const trust = parsedTrust.value.toLowerCase()
      if (!name || !value) {
        return { error: t('app.deviceImportRuntimeNameValueRequired', { source, field: `variables[${index}]` }) }
      }
      if (variable.trust !== undefined && variable.trust !== null && !trust) {
        return { error: t('app.deviceImportRuntimeScalarRequired', {
          source,
          field: `variables[${index}].trust`
        }) }
      }
      runtime.variables.push({
        name,
        value,
        ...(trust ? { trust } : {})
      })
    }
  }

  const privacyList = parseRuntimeList(item.privacies, source, 'privacies')
  if (privacyList.error) return { error: privacyList.error }
  if (privacyList.items) {
    runtime.privacies = []
    for (const [index, privacy] of privacyList.items.entries()) {
      if (!privacy || typeof privacy !== 'object' || Array.isArray(privacy)) {
        return { error: t('app.deviceImportRuntimeObjectRequired', { source, field: `privacies[${index}]` }) }
      }
      const unknownField = findUnknownImportField(privacy, DEVICE_IMPORT_PRIVACY_KEYS)
      if (unknownField) {
        return { error: t('app.deviceImportUnknownField', {
          source,
          field: `privacies[${index}].${unknownField}`
        }) }
      }
      const parsedName = parseJsonImportString(privacy.name, source, `privacies[${index}].name`)
      const parsedPrivacy = parseJsonImportString(privacy.privacy, source, `privacies[${index}].privacy`)
      if (parsedName.error || parsedPrivacy.error) {
        return { error: parsedName.error || parsedPrivacy.error }
      }
      const name = parsedName.value
      const value = parsedPrivacy.value.toLowerCase()
      if (!name || !value) {
        return { error: t('app.deviceImportRuntimeNameValueRequired', { source, field: `privacies[${index}]` }) }
      }
      runtime.privacies.push({ name, privacy: value })
    }
  }

  return Object.keys(runtime).length > 0 ? { runtime } : {}
}

const splitImportedRuntime = (
  template: DeviceTemplate,
  runtime?: DeviceRuntimeConfig
): { runtime?: DeviceRuntimeConfig; environmentVariables?: ModelEnvironmentVariable[]; error?: string } => {
  const validationError = validateDeviceRuntimeConfig(template, runtime, t, { variableScope: 'all' })
  if (validationError) return { error: validationError }
  const effectiveNodeRuntime = materializeDeviceRuntimeConfig(
    template,
    runtime,
    { variableScope: 'local' }
  )

  const environmentNames = new Set(getTemplateEnvironmentVariables(template).map(variable => variable.Name))
  const environmentByName = new Map<string, ModelEnvironmentVariable>()

  for (const variable of runtime?.variables || []) {
    if (!environmentNames.has(variable.name)) continue
    environmentByName.set(variable.name, {
      ...(environmentByName.get(variable.name) || { name: variable.name }),
      name: variable.name,
      value: variable.value,
      trust: variable.trust
    })
  }

  for (const privacy of runtime?.privacies || []) {
    if (!environmentNames.has(privacy.name)) continue
    environmentByName.set(privacy.name, {
      ...(environmentByName.get(privacy.name) || { name: privacy.name }),
      name: privacy.name,
      privacy: privacy.privacy
    })
  }

  return {
    runtime: effectiveNodeRuntime,
    environmentVariables: Array.from(environmentByName.values())
  }
}

const parseCsvImportLine = (line: string): { columns: string[]; error?: string } => {
  const columns: string[] = []
  let current = ''
  let quoted = false

  for (let i = 0; i < line.length; i += 1) {
    const char = line[i]
    if (char === '"') {
      if (quoted && line[i + 1] === '"') {
        current += '"'
        i += 1
      } else {
        quoted = !quoted
      }
      continue
    }

    if (!quoted && (char === ',' || char === '\t')) {
      columns.push(current.trim())
      current = ''
      continue
    }

    current += char
  }

  if (quoted) {
    return { columns: [], error: t('app.deviceImportCsvQuoteError') }
  }

  columns.push(current.trim())
  return { columns }
}

const isDeviceImportHeader = (columns: string[]) =>
  columns.length >= 2
  && DEVICE_IMPORT_TEMPLATE_KEYS.has(normalizeImportKey(columns[0]))
  && DEVICE_IMPORT_NAME_KEYS.has(normalizeImportKey(columns[1]))

// Template search and filter
const templateSearchQuery = ref('')
const templateFilterType = ref('all')

// Filtered templates based on search and type
const filteredTemplates = computed(() => {
  let templates = props.deviceTemplates

  // Filter by search query
  if (templateSearchQuery.value.trim()) {
    const query = templateSearchQuery.value.toLowerCase()
    templates = templates.filter((t: any) => {
      const name = t.manifest?.Name || t.name
      const desc = t.manifest?.Description || ''
      return name.toLowerCase().includes(query) || desc.toLowerCase().includes(query)
    })
  }

  // Filter by type (if not 'all')
  if (templateFilterType.value !== 'all') {
    templates = templates.filter((t: any) => {
      const name = t.manifest?.Name || t.name
      return name === templateFilterType.value
    })
  }

  return templates
})

const isDefaultTemplate = (template: any) => template?.defaultTemplate !== false

const defaultTemplates = computed(() =>
  filteredTemplates.value.filter((template: any) => isDefaultTemplate(template))
)

const customTemplates = computed(() =>
  filteredTemplates.value.filter((template: any) => !isDefaultTemplate(template))
)

const templateGroups = computed(() => [
  {
    key: 'default',
    label: t('app.defaultTemplates'),
    templates: defaultTemplates.value
  },
  {
    key: 'custom',
    label: t('app.customTemplates'),
    templates: customTemplates.value
  }
])

const pinnedTemplatePreviewId = ref<string | number | null>(null)
const templatePreviewPoint = reactive({ x: 24, y: 24 })
const templatePreviewViewport = reactive({ width: 1440, height: 900 })

const TEMPLATE_PREVIEW_WIDTH = 320
const TEMPLATE_PREVIEW_MAX_HEIGHT = 460
const TEMPLATE_PREVIEW_OFFSET = 16
const TEMPLATE_PREVIEW_MARGIN = 12

const getTemplateKey = (template: any) =>
  template?.id ?? template?.manifest?.Name ?? template?.name ?? ''

const getTemplateName = (template: any) =>
  template?.manifest?.Name || template?.name || t('app.unknown')

const getTemplateDescription = (template: any) =>
  template?.manifest?.Description || t('app.noDescription')

const getTemplateList = (template: any, field: string, nameField = 'Name') => {
  const value = template?.manifest?.[field]
  if (!Array.isArray(value)) return []
  return value
    .map((item: any) => typeof item === 'string' ? item : item?.[nameField])
    .filter((item: unknown): item is string => typeof item === 'string' && item.trim().length > 0)
}

const previewItems = (items: string[], limit = 5) => items.slice(0, limit)

const getTemplateInitState = (template: any) =>
  template?.manifest?.InitState || t('app.none')

const getTemplateTransitionCount = (template: any) =>
  Array.isArray(template?.manifest?.Transitions) ? template.manifest.Transitions.length : 0

const getTemplatePreviewSections = (template: any) => [
  { key: 'modes', label: t('app.modes'), items: getTemplateList(template, 'Modes') },
  { key: 'states', label: t('app.workingStates'), items: getTemplateList(template, 'WorkingStates') },
  { key: 'variables', label: t('app.variables'), items: getTemplateList(template, 'InternalVariables') },
  { key: 'apis', label: t('app.deviceApis'), items: getTemplateList(template, 'APIs') }
]

const activeTemplatePreview = computed(() => {
  const key = pinnedTemplatePreviewId.value
  if (key === null) return null
  return props.deviceTemplates.find((template: any) => getTemplateKey(template) === key) ?? null
})

const templatePreviewStyle = computed(() => {
  const width = Math.min(TEMPLATE_PREVIEW_WIDTH, Math.max(240, templatePreviewViewport.width - (TEMPLATE_PREVIEW_MARGIN * 2)))
  const maxHeight = Math.min(TEMPLATE_PREVIEW_MAX_HEIGHT, Math.max(220, templatePreviewViewport.height - (TEMPLATE_PREVIEW_MARGIN * 2)))
  const roomOnRight = templatePreviewPoint.x + TEMPLATE_PREVIEW_OFFSET + width <= templatePreviewViewport.width - TEMPLATE_PREVIEW_MARGIN
  const left = roomOnRight
    ? templatePreviewPoint.x + TEMPLATE_PREVIEW_OFFSET
    : Math.max(TEMPLATE_PREVIEW_MARGIN, templatePreviewPoint.x - TEMPLATE_PREVIEW_OFFSET - width)
  const maxTop = Math.max(TEMPLATE_PREVIEW_MARGIN, templatePreviewViewport.height - maxHeight - TEMPLATE_PREVIEW_MARGIN)
  const top = Math.min(Math.max(TEMPLATE_PREVIEW_MARGIN, templatePreviewPoint.y - 10), maxTop)

  return {
    left: `${Math.round(left)}px`,
    top: `${Math.round(top)}px`,
    width: `${Math.round(width)}px`,
    maxHeight: `${Math.round(maxHeight)}px`
  }
})

const syncTemplatePreviewViewport = () => {
  if (typeof window === 'undefined') return
  templatePreviewViewport.width = window.innerWidth
  templatePreviewViewport.height = window.innerHeight
}

const updateTemplatePreviewPosition = (event?: MouseEvent | FocusEvent | KeyboardEvent) => {
  syncTemplatePreviewViewport()

  if (event && 'clientX' in event && event.clientX > 0 && event.clientY > 0) {
    templatePreviewPoint.x = event.clientX
    templatePreviewPoint.y = event.clientY
    return
  }

  const target = event?.currentTarget
  if (target instanceof HTMLElement) {
    const rect = target.getBoundingClientRect()
    templatePreviewPoint.x = rect.right
    templatePreviewPoint.y = rect.top + Math.min(rect.height / 2, 24)
  }
}

const toggleTemplatePreview = (template: any, event?: MouseEvent | KeyboardEvent) => {
  const key = getTemplateKey(template)
  if (pinnedTemplatePreviewId.value === key) {
    pinnedTemplatePreviewId.value = null
    return
  }
  updateTemplatePreviewPosition(event)
  pinnedTemplatePreviewId.value = key
}

const closeTemplatePreview = () => {
  pinnedTemplatePreviewId.value = null
}

const isTemplatePreviewVisible = (template: any) => {
  return pinnedTemplatePreviewId.value === getTemplateKey(template)
}

onMounted(() => {
  syncTemplatePreviewViewport()
  window.addEventListener('resize', syncTemplatePreviewViewport)
})

onBeforeUnmount(() => {
  if (typeof window !== 'undefined') {
    window.removeEventListener('resize', syncTemplatePreviewViewport)
  }
})

// Device types - dynamically loaded from backend device templates
const deviceTypes = computed(() => {
  // Only use templates loaded from backend
  return props.deviceTemplates
    .map((tpl: any) => tpl.manifest?.Name || tpl.name)
    .filter((name: string) => name) // Remove empty names
})

const isTemplateSelectorDisabled = computed(() => props.templatesLoading || deviceTypes.value.length === 0)
const templateSelectorTitle = computed(() => {
  if (props.templatesLoading) return t('app.loadingDeviceTemplates')
  return deviceForm.type || (deviceTypes.value.length === 0 ? t('app.none') : t('app.selectDeviceTemplate'))
})

const batchDeviceCountError = computed(() => {
  const count = Number(batchDeviceForm.count)
  return Number.isInteger(count) && count >= 1 && count <= MAX_BATCH_DEVICE_COUNT
    ? ''
    : t('app.integerBetween', {
        field: t('app.count'),
        min: 1,
        max: MAX_BATCH_DEVICE_COUNT
      })
})

const batchDeviceCount = computed(() => batchDeviceCountError.value
  ? null
  : Number(batchDeviceForm.count))

const batchDevicePreview = computed(() => {
  const template = findTemplateByName(batchDeviceForm.type)
  const prefix = normalizeName(batchDeviceForm.prefix)
  const count = batchDeviceCount.value
  if (!template || !prefix || count === null) return []

  const reserved = new Set(existingDeviceLabels.value)
  return Array.from({ length: count }, (_, index) => ({
    template,
    customName: getUniqueDeviceName(`${prefix}${index + 1}`, reserved)
  }))
})

const parsedImportedDevices = computed<DeviceImportRow[]>(() => {
  const text = importDeviceForm.text.trim()
  if (!text) return []

  try {
    const rows: DeviceImportRow[] = []
    if (text.startsWith('[') || text.startsWith('{')) {
      let parsed: unknown
      try {
        parsed = JSON.parse(text)
      } catch {
        return [makeImportError('#1', t('app.deviceImportInvalidJson'))]
      }

      const items = Array.isArray(parsed) ? parsed : [parsed]
      items.forEach((item: any, index: number) => {
        const source = `#${index + 1}`
        if (!item || typeof item !== 'object' || Array.isArray(item)) {
          rows.push(makeImportError(source, t('app.deviceImportJsonObjectRequired')))
          return
        }
        const unknownField = findUnknownImportField(item, DEVICE_IMPORT_JSON_KEYS)
        if (unknownField) {
          rows.push(makeImportError(source, t('app.deviceImportUnknownField', { source, field: unknownField })))
          return
        }
        const templateResult = readJsonImportAlias(item, DEVICE_IMPORT_TEMPLATE_ALIASES, source)
        if (templateResult.error) {
          rows.push(makeImportError(source, templateResult.error))
          return
        }
        const nameResult = readJsonImportAlias(item, DEVICE_IMPORT_NAME_ALIASES, source)
        if (nameResult.error) {
          rows.push(makeImportError(source, nameResult.error))
          return
        }
        const runtimeResult = parseImportedRuntime(item, source)
        if (runtimeResult.error) {
          rows.push(makeImportError(source, runtimeResult.error))
          return
        }
        rows.push({
          source,
          templateName: templateResult.value,
          name: nameResult.value,
          runtime: runtimeResult.runtime
        })
      })
    } else {
      text.split(/\r?\n/).forEach((line, index) => {
        const trimmed = line.trim()
        if (!trimmed) return
        const parsedLine = parseCsvImportLine(trimmed)
        if (parsedLine.error) {
          rows.push(makeImportError(`#${index + 1}`, parsedLine.error))
          return
        }
        const columns = parsedLine.columns
        if (rows.length === 0 && isDeviceImportHeader(columns)) {
          return
        }
        if (columns.length > 2 && columns.slice(2).some(column => column.trim())) {
          rows.push(makeImportError(`#${index + 1}`, t('app.deviceImportCsvColumnCount')))
          return
        }
        const [templateName, name] = columns
        rows.push({ source: `#${index + 1}`, templateName, name })
      })
    }

    const reserved = new Set(existingDeviceLabels.value)
    return rows.map(row => {
      if (row.error) return row
      const template = findTemplateByName(row.templateName)
      const missingTemplateName = !row.templateName
      const missingName = !row.name
      const missingTemplate = !template
      const runtimeResult = template
        ? splitImportedRuntime(template as DeviceTemplate, row.runtime)
        : {}
      const runtimeError = runtimeResult.error || ''
      const error = missingTemplateName
        ? t('app.deviceImportTemplateNameMissing')
        : missingName
          ? t('app.deviceImportNameMissing')
          : missingTemplate
            ? t('app.deviceImportTemplateMissing', { template: row.templateName })
            : runtimeError
      const customName = error ? row.name : getUniqueDeviceName(row.name, reserved)
      const warning = !error && customName !== row.name
        ? t('app.deviceImportNameAutoRenamed', { from: row.name, to: customName })
        : ''

      return {
        ...row,
        template,
        customName,
        runtime: runtimeResult.runtime,
        environmentVariables: runtimeResult.environmentVariables,
        error,
        warning
      }
    })
  } catch (error: any) {
    return [makeImportError('#1', localizedErrorMessage(error, t('app.invalidJsonFile'), locale.value))]
  }
})

const validImportedDevices = computed(() =>
  parsedImportedDevices.value.filter((item: any) => !item.error && item.template && item.customName)
)

const importedEnvironmentMerge = computed(() => mergeSourcedEnvironmentPatches(
  validImportedDevices.value.map((item: any) => ({
    source: item.source,
    patches: item.environmentVariables || []
  }))
))

const environmentConflictFieldLabel = (field: EnvironmentPatchConflict['field']) => {
  if (field === 'value') return t('app.variableValue')
  if (field === 'trust') return t('app.sourceLabel')
  return t('app.sensitivityLabel')
}

const formatImportedEnvironmentConflict = (conflict: EnvironmentPatchConflict) =>
  t('app.deviceImportEnvironmentConflict', {
    name: conflict.name,
    field: environmentConflictFieldLabel(conflict.field),
    first: conflict.firstSource,
    second: conflict.secondSource
  })

const importedDevicesHaveErrors = computed(() =>
  parsedImportedDevices.value.some((item: any) => item.error)
  || importedEnvironmentMerge.value.conflicts.length > 0
)

const deviceImportPlaceholder = computed(() => {
  const jsonExample = JSON.stringify([{
    template: 'Motion Detector',
    name: 'entry_motion',
    variables: [{ name: 'motion', value: 'active', trust: 'trusted' }],
    privacies: [{ name: 'motion', privacy: 'private' }]
  }])
  return `${jsonExample}\n${t('app.deviceImportCsvExamplePrefix')}\nAir Conditioner,living_ac`
})

// Get template icon SVG
const getTemplateIcon = (template: any): string => {
  const name = template.manifest?.Name || template.name
  const initState = template.manifest?.InitState || 'Working'
  return getDefaultDeviceIcon(name, initState, template.manifest)
}

// Specification form data
const specForm = reactive({
  templateId: '' as SpecTemplateId | '',
  templateType: '' as SpecTemplateType | '',
  selectedDevices: [] as Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>,
  formula: '',
  aConditions: [] as unknown as SpecCondition[],
  ifConditions: [] as unknown as SpecCondition[],
  thenConditions: [] as unknown as SpecCondition[]
})

// Specification dialog state
const showSpecDialog = ref(false)
const editingConditionIndex = ref(-1)
const editingConditionSide = ref<SpecSide>('a')

const closeSpecDialog = () => {
  showSpecDialog.value = false
}

const {
  setDialogRef: setSpecDialogRef,
  handleModalKeydown: handleSpecDialogKeydown
} = useModalAccessibility(showSpecDialog, closeSpecDialog)

// Editing condition data
const editingConditionData = reactive<Partial<SpecCondition>>({
  id: '',
  side: 'a',
  deviceId: '',
  deviceLabel: '',
  targetType: 'state',
  key: '',
  propertyScope: undefined,
  relation: '=',
  value: ''
})

// Dialog states
const showDeleteConfirmDialog = ref(false)
const templateToDelete = ref<any>(null)
const templateDeletePreview = ref<DeviceTemplateDeletionResult | null>(null)
const isLoadingTemplateDeletePreview = ref(false)
const isDeletingTemplate = ref(false)
const showResetDefaultsConfirmDialog = ref(false)
const isResettingDefaultTemplates = ref(false)
const isLoadingDefaultTemplateResetPreview = ref(false)
const defaultTemplateResetPreview = ref<DefaultTemplateResetResult | null>(null)

// Get current template details
const currentTemplateDetail = computed(() => {
  if (!specForm.templateId) return null
  return specTemplateDetails.find(t => t.id === specForm.templateId)
})

const templateMessage = (key: string | undefined, fallback: string) => key ? t(key) : fallback

// Get required sides for current template
const requiredSides = computed(() => {
  return currentTemplateDetail.value?.requiredSides || []
})

// Check if a side is required for current template
const isSideRequired = (side: SpecSide) => {
  return requiredSides.value.includes(side)
}

// Get conditions for a specific side
const getConditionsForSide = (side: SpecSide): SpecCondition[] => {
  switch (side) {
    case 'a': return specForm.aConditions
    case 'if': return specForm.ifConditions
    case 'then': return specForm.thenConditions
    default: return []
  }
}

// Generate unique ID for condition
const generateConditionId = () => {
  return `cond-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`
}

// Open condition dialog for adding/editing
const openConditionDialog = (side: SpecSide, index: number = -1) => {
  editingConditionSide.value = side
  editingConditionIndex.value = index
  
  if (index >= 0) {
    // Edit existing condition
    const conditions = getConditionsForSide(side)
    const condition = conditions[index]
    Object.assign(editingConditionData, { propertyScope: undefined }, condition)
  } else {
    // Add new condition - reset to defaults
    Object.assign(editingConditionData, {
      id: generateConditionId(),
      side,
      deviceId: '',
      deviceLabel: '',
      targetType: 'state',
      key: '',
      propertyScope: undefined,
      relation: '=',
      value: ''
    })
  }
  showSpecDialog.value = true
}

// Save condition from dialog
const saveCondition = () => {
  if (!editingConditionData.deviceId) {
    ElMessage.warning({
      message: t('app.selectDevice'),
      center: true
    })
    return
  }
  if (!editingConditionData.targetType) {
    ElMessage.warning({
      message: t('app.selectType'),
      center: true
    })
    return
  }
  if (editingConditionData.targetType !== 'state' && !editingConditionData.key) {
    ElMessage.warning({
      message: t('app.selectProperty'),
      center: true
    })
    return
  }
  if ((editingConditionData.targetType === 'trust' || editingConditionData.targetType === 'privacy')
    && !['state', 'variable'].includes(editingConditionData.propertyScope || '')) {
    ElMessage.warning({ message: t('app.selectProperty'), center: true })
    return
  }

  // value 不能为空，否则后端验证会失败
  // 但 API 类型只需要检查 API 是否被调用，不需要具体的 value
  if (editingConditionData.targetType !== 'api') {
    if (!editingConditionData.value || !editingConditionData.value.trim()) {
      ElMessage.warning({
        message: t('app.enterValue'),
        center: true
      })
      return
    }
  }

  // key 不能为空，否则后端验证会失败。
  // 对于 full-state 条件，key 固定为 state；mode/variable/api/trust/privacy 都必须选择具体属性。
  const keyValue = editingConditionData.targetType === 'state'
    ? 'state'
    : (editingConditionData.key || '')

  if (!keyValue.trim()) {
    ElMessage.warning({
      message: t('app.selectProperty'),
      center: true
    })
    return
  }

  const device = deviceNodes.value.find(n => n.id === editingConditionData.deviceId)

  // API 类型使用 'TRUE' 作为默认 value（表示 API 被调用）
  // 因为后端 @NotBlank 要求 value 不能为空
  const finalValue = editingConditionData.targetType === 'api'
    ? 'TRUE'
    : (editingConditionData.value || '')

  const condition: SpecCondition = {
    id: editingConditionData.id || generateConditionId(),
    side: editingConditionSide.value,
    deviceId: editingConditionData.deviceId,
    deviceLabel: device?.label || editingConditionData.deviceId,
    targetType: editingConditionData.targetType || 'state',
    key: keyValue,
    ...((editingConditionData.targetType === 'trust' || editingConditionData.targetType === 'privacy')
      ? { propertyScope: editingConditionData.propertyScope as 'state' | 'variable' }
      : {}),
    relation: editingConditionData.relation || '=',
    value: finalValue
  }
  
  switch (editingConditionSide.value) {
    case 'a':
      if (editingConditionIndex.value >= 0) {
        specForm.aConditions[editingConditionIndex.value] = condition
      } else {
        specForm.aConditions.push(condition)
      }
      break
    case 'if':
      if (editingConditionIndex.value >= 0) {
        specForm.ifConditions[editingConditionIndex.value] = condition
      } else {
        specForm.ifConditions.push(condition)
      }
      break
    case 'then':
      if (editingConditionIndex.value >= 0) {
        specForm.thenConditions[editingConditionIndex.value] = condition
      } else {
        specForm.thenConditions.push(condition)
      }
      break
  }
  
  showSpecDialog.value = false
  updateFormula()
}

// Remove condition
const removeCondition = (side: SpecSide, index: number) => {
  switch (side) {
    case 'a':
      specForm.aConditions.splice(index, 1)
      break
    case 'if':
      specForm.ifConditions.splice(index, 1)
      break
    case 'then':
      specForm.thenConditions.splice(index, 1)
      break
  }
  updateFormula()
}

// Get device display name
const getDeviceLabel = (deviceId: string) => {
  const device = deviceNodes.value.find(n => n.id === deviceId)
  return device?.label || t('app.unknownModelItem')
}

// Get device template
const getDeviceTemplate = (deviceId: string) => {
  const device = deviceNodes.value.find(n => n.id === deviceId)
  if (!device) return null

  const target = normalizeName(device.templateName).toLowerCase()
  const template = props.deviceTemplates.find(t =>
    [t.name, t.manifest?.Name]
      .some(candidate => normalizeName(candidate).toLowerCase() === target)
  )

  return template || null
}

const getDeviceManifestForCondition = (deviceId: string) => {
  return getDeviceTemplate(deviceId)?.manifest || null
}

// Get available keys based on target type for a device
const encodePropertySelection = (propertyScope: 'state' | 'variable', key: string) =>
  JSON.stringify([propertyScope, key])

const decodePropertySelection = (value: string): { propertyScope: 'state' | 'variable'; key: string } | null => {
  try {
    const parsed = JSON.parse(value)
    if (Array.isArray(parsed) && ['state', 'variable'].includes(parsed[0]) && typeof parsed[1] === 'string') {
      return { propertyScope: parsed[0], key: parsed[1] }
    }
  } catch {
    // Ordinary condition keys are not encoded.
  }
  return null
}

const conditionKeySelection = computed({
  get: () => {
    if ((editingConditionData.targetType === 'trust' || editingConditionData.targetType === 'privacy')
      && editingConditionData.propertyScope && editingConditionData.key) {
      return encodePropertySelection(editingConditionData.propertyScope, editingConditionData.key)
    }
    return editingConditionData.key || ''
  },
  set: (value: string) => {
    if (editingConditionData.targetType === 'trust' || editingConditionData.targetType === 'privacy') {
      const parsed = decodePropertySelection(value)
      editingConditionData.propertyScope = parsed?.propertyScope
      editingConditionData.key = parsed?.key || ''
      return
    }
    editingConditionData.propertyScope = undefined
    editingConditionData.key = value
  }
})

const getAvailableKeys = (deviceId: string, targetType: string): Array<{label: string, value: string}> => {
  const template = getDeviceTemplate(deviceId)
  if (!template || !template.manifest) return []

  const keys: Array<{label: string, value: string}> = []

  const variableScopeLabel = (variable: any) =>
    variable?.IsInside === true ? t('app.internalVariable') : t('app.environmentVariable')

  // Template InternalVariables includes both device-local and shared environment variables.
  if (targetType === 'variable' && template.manifest.InternalVariables) {
    template.manifest.InternalVariables.forEach((v: any) => {
      keys.push({ label: `${v.Name} (${variableScopeLabel(v)})`, value: v.Name })
    })
  }

  if (targetType === 'state' && template.manifest.WorkingStates) {
    template.manifest.WorkingStates.forEach((s: any) => {
      keys.push({ label: s.Name, value: s.Name })
    })
  }

  if (targetType === 'mode' && template.manifest.Modes) {
    template.manifest.Modes.forEach((mode: string) => {
      keys.push({ label: mode, value: mode })
    })
  }

  if (targetType === 'api' && template.manifest.APIs) {
    template.manifest.APIs
      .filter((api: any) => {
        const isSignal = api.Signal === true || api.signal === true
        if (!isSignal) return false
        if (specForm.templateId !== '7') return true
        return Boolean(String(api.EndState ?? api.endState ?? '').trim())
      })
      .forEach((api: any) => {
      keys.push({ label: api.Name, value: api.Name })
    })
  }

  // Trust/privacy state targets refer to the currently active state in a mode.
  // Generated mode_state names remain an internal NuSMV detail.
  if (targetType === 'trust' || targetType === 'privacy') {
    const seenPropertyKeys = new Set<string>()
    const addPropertyKey = (label: string, propertyScope: 'state' | 'variable', key: string) => {
      const value = encodePropertySelection(propertyScope, key)
      if (!value || seenPropertyKeys.has(value)) return
      seenPropertyKeys.add(value)
      keys.push({ label, value })
    }
    const modes = Array.isArray(template.manifest.Modes) ? template.manifest.Modes : []
    modes.forEach((mode: string) => addPropertyKey(
      modes.length === 1
        ? t('app.currentStateProperty')
        : t('app.currentModeStateProperty', { mode }),
      'state',
      mode
    ))
    if (template.manifest.InternalVariables) {
      template.manifest.InternalVariables.forEach((v: any) => {
        addPropertyKey(`${v.Name} (${variableScopeLabel(v)})`, 'variable', v.Name)
      })
    }
  }

  return keys
}

const formatConditionPropertyLabel = (condition: Pick<SpecCondition, 'deviceId' | 'targetType' | 'key' | 'propertyScope'>) => {
  if ((condition.targetType === 'trust' || condition.targetType === 'privacy')
    && condition.propertyScope === 'state') {
    const modes = getDeviceManifestForCondition(condition.deviceId)?.Modes || []
    return modes.length === 1
      ? t('app.currentStateProperty')
      : t('app.currentModeStateProperty', { mode: condition.key })
  }
  return condition.key || t('app.value')
}

// Computed available keys for current editing condition
const availableKeys = computed(() => {
  if (!editingConditionData.deviceId) return []
  return getAvailableKeys(editingConditionData.deviceId, editingConditionData.targetType || 'state')
})

// Handle target type change to reset related fields
const handleTargetTypeChange = () => {
  editingConditionData.key = ''
  editingConditionData.propertyScope = undefined
  editingConditionData.value = ''
  // Reset relation to default based on new type
  if (editingConditionData.targetType === 'state') {
    editingConditionData.relation = '='
  } else {
    editingConditionData.relation = '='
  }
}

// Check if relation and value fields should be shown
// Show for Variable and State. Hidden for API type.
// Also, ensure it's shown if key is not selected (handled by disabled state), but here we specifically want Value for State.
const showRelationAndValue = computed(() => {
  // Always show relation/value for State type
  if (editingConditionData.targetType === 'state') return true
  // Hide for API type
  return editingConditionData.targetType !== 'api'
})

const enumRelationValues = ['=', '!=', 'in', 'not in']
const isSelectedSpecVariableEnum = () => {
  if (editingConditionData.targetType !== 'variable' || !editingConditionData.deviceId || !editingConditionData.key) {
    return false
  }
  const manifest = getDeviceManifestForCondition(editingConditionData.deviceId)
  const variable = Array.isArray(manifest?.InternalVariables)
    ? manifest.InternalVariables.find((item: any) => item?.Name === editingConditionData.key)
    : null
  return Array.isArray(variable?.Values) && variable.Values.length > 0
}

// Filter relation operators based on target type
const filteredRelationOperators = computed(() => {
  if (specForm.templateId === '7'
    && (editingConditionData.targetType === 'state' || editingConditionData.targetType === 'mode')) {
    return relationOperators.filter(op => op.value === '=')
  }
  if (editingConditionData.targetType === 'state') {
    return relationOperators.filter(op => enumRelationValues.includes(op.value))
  }
  if (editingConditionData.targetType === 'mode') {
    return relationOperators.filter(op => enumRelationValues.includes(op.value))
  }
  if (editingConditionData.targetType === 'variable' && isSelectedSpecVariableEnum()) {
    return relationOperators.filter(op => enumRelationValues.includes(op.value))
  }
  // trust/privacy are enum-valued — only equality / set membership make sense.
  // Ordering comparisons (> >= < <=) would generate meaningless NuSMV conditions.
  if (editingConditionData.targetType === 'trust' || editingConditionData.targetType === 'privacy') {
    return relationOperators.filter(op => enumRelationValues.includes(op.value))
  }
  return relationOperators
})

// Computed available states for the selected device (for equality and set-membership selection)
const availableStates = computed(() => {
  if (!editingConditionData.deviceId) return []
  const manifest = getDeviceManifestForCondition(editingConditionData.deviceId)
  if (!manifest || !manifest.WorkingStates) return []
  return manifest.WorkingStates.map((s: any) => s.Name)
})

const getModeValuesFromManifest = (manifest: any, modeName: string): string[] => {
  if (!manifest || !Array.isArray(manifest.Modes) || !Array.isArray(manifest.WorkingStates)) return []
  const modeIndex = manifest.Modes.findIndex((mode: string) => mode === modeName)
  if (modeIndex < 0) return []

  const values = new Set<string>()
  manifest.WorkingStates.forEach((state: any) => {
    const rawName = state?.Name
    if (typeof rawName !== 'string' || rawName.trim() === '') return
    const parts = rawName.split(';')
    if (manifest.Modes.length === 1) {
      values.add(rawName.trim())
    } else if (parts.length === manifest.Modes.length) {
      const value = parts[modeIndex]?.trim()
      if (value) values.add(value)
    }
  })
  return Array.from(values)
}

const availableModeValues = computed(() => {
  if (!editingConditionData.deviceId || !editingConditionData.key) return []
  const manifest = getDeviceManifestForCondition(editingConditionData.deviceId)
  return getModeValuesFromManifest(manifest, editingConditionData.key)
})

const availableVariableValues = computed(() => {
  if (!editingConditionData.deviceId || !editingConditionData.key) return []
  const template = getDeviceTemplate(editingConditionData.deviceId)
  const variables = template?.manifest?.InternalVariables
  if (!Array.isArray(variables)) return []
  const variable = variables.find((v: any) => v?.Name === editingConditionData.key)
  return Array.isArray(variable?.Values) ? variable.Values.map((value: unknown) => String(value)) : []
})

// Allowed values for trust/privacy conditions — must match the backend enum domains
// (SmvDeviceModuleBuilder: trust ∈ {untrusted, trusted}, privacy ∈ {private, public}).
const trustPrivacyValues = computed<string[]>(() => {
  if (editingConditionData.targetType === 'trust') return ['trusted', 'untrusted']
  if (editingConditionData.targetType === 'privacy') return ['public', 'private']
  return []
})

const conditionValueOptions = computed<string[]>(() => {
  if (editingConditionData.targetType === 'state') return availableStates.value
  if (editingConditionData.targetType === 'mode') return availableModeValues.value
  if (editingConditionData.targetType === 'variable') return availableVariableValues.value
  return trustPrivacyValues.value
})

const isSpecSetRelation = computed(() =>
  editingConditionData.relation === 'in' || editingConditionData.relation === 'not in'
)

const splitConditionValueList = (value: unknown): string[] => {
  if (value === null || value === undefined || value === '') return []
  const delimiter = editingConditionData.targetType === 'state' ? /[,|]/ : /[,;|]/
  return String(value)
    .split(delimiter)
    .map(part => part.trim())
    .filter(Boolean)
}

const editingConditionValueList = computed<string[]>({
  get: () => splitConditionValueList(editingConditionData.value),
  set: values => {
    editingConditionData.value = Array.from(new Set(values)).join(', ')
  }
})

watch(filteredRelationOperators, options => {
  if (!options.some(option => option.value === editingConditionData.relation)) {
    editingConditionData.relation = options[0]?.value || '='
    editingConditionData.value = ''
  }
})

watch(() => editingConditionData.relation, () => {
  if (!isSpecSetRelation.value && splitConditionValueList(editingConditionData.value).length > 1) {
    editingConditionData.value = splitConditionValueList(editingConditionData.value)[0] || ''
  }
})

// Get relation label (accepts string for flexibility)
const getRelationLabel = (relation: string) => {
  return relationOperators.find(r => r.value === relation)?.label || relation
}

const hasConditionValue = (value: unknown) =>
  value !== null && value !== undefined && value !== ''

const formatConditionValue = (value: unknown) =>
  hasConditionValue(value) ? String(value) : '*'

const specFormulaKind = computed(() => {
  const formula = specForm.formula.trim().toUpperCase()
  if (formula.startsWith('CTLSPEC')) return 'CTL'
  if (formula.startsWith('LTLSPEC')) return 'LTL'
  return t('app.modelFormulaKind')
})

// Update model formula preview based on conditions
const updateFormula = () => {
  if (!currentTemplateDetail.value) {
    specForm.formula = ''
    return
  }

  specForm.formula = buildSpecFormula({
    templateId: specForm.templateId as SpecTemplateId,
    templateLabel: currentTemplateDetail.value.label,
    aConditions: specForm.aConditions,
    ifConditions: specForm.ifConditions,
    thenConditions: specForm.thenConditions
  }, {
    nodes: props.nodes,
    deviceTemplates: props.deviceTemplates
  })
}

// Generate natural language specification description
const naturalLanguageRule = computed(() => {
  if (!currentTemplateDetail.value || specForm.templateType === '') {
    return t('app.specPreviewConfigureConditions')
  }

  const template = currentTemplateDetail.value
  const type = template.type

  const conditionSubject = (condition: SpecCondition): string => {
    const deviceName = condition.deviceLabel || condition.deviceId || t('app.device')
    const keyName = formatConditionPropertyLabel(condition)
    switch (condition.targetType) {
      case 'variable':
        return t('app.specPreviewVariableSubject', { key: keyName, device: deviceName })
      case 'mode':
        return t('app.specPreviewModeSubject', { key: keyName, device: deviceName })
      case 'state':
        return t('app.specPreviewStateSubject', { device: deviceName })
      case 'api':
        return t('app.specPreviewApiSubject', { key: keyName, device: deviceName })
      case 'trust':
        return t('app.specPreviewTrustSubject', { key: keyName, device: deviceName })
      case 'privacy':
        return t('app.specPreviewPrivacySubject', { key: keyName, device: deviceName })
      default:
        return t('app.specPreviewPropertySubject', { key: keyName, device: deviceName })
    }
  }

  // Helper to format conditions in natural language
  const formatConditions = (conditions: SpecCondition[]): string => {
    if (conditions.length === 0) return ''

    return conditions.map(c => {
      const relationText = getRelationLabel(c.relation || '=')
      const valueText = hasConditionValue(c.value) ? ` ${relationText} "${c.value}"` : ''
      return `${conditionSubject(c)}${valueText}`
    }).join(` ${t('app.specPreviewAnd')} `)
  }

  const aConditions = formatConditions(specForm.aConditions)
  const ifConditions = formatConditions(specForm.ifConditions)
  const thenConditions = formatConditions(specForm.thenConditions)

  // Generate natural language based on template type
  switch (type) {
    case 'always':
      if (aConditions) {
        return t('app.specPreviewAlways', { conditions: aConditions })
      }
      return t('app.specPreviewConfigureACondition')

    case 'eventually':
      if (aConditions) {
        return t('app.specPreviewEventually', { conditions: aConditions })
      }
      return t('app.specPreviewConfigureACondition')

    case 'never':
      if (aConditions) {
        return t('app.specPreviewNever', { conditions: aConditions })
      }
      return t('app.specPreviewConfigureACondition')

    case 'immediate':
      if (ifConditions && thenConditions) {
        return t('app.specPreviewImmediate', { ifConditions, thenConditions })
      } else if (ifConditions) {
        return t('app.specPreviewImmediatePartial', { ifConditions })
      }
      return t('app.specPreviewConfigureIfThen')

    case 'response':
      if (ifConditions && thenConditions) {
        return t('app.specPreviewResponse', { ifConditions, thenConditions })
      } else if (ifConditions) {
        return t('app.specPreviewResponsePartial', { ifConditions })
      }
      return t('app.specPreviewConfigureIfThen')

    case 'persistence':
      if (ifConditions && thenConditions) {
        return t('app.specPreviewPersistence', { ifConditions, thenConditions })
      } else if (ifConditions) {
        return t('app.specPreviewPersistencePartial', { ifConditions })
      }
      return t('app.specPreviewConfigureIfThen')

    case 'safety':
      if (aConditions) {
        return t('app.specPreviewSafety', { conditions: aConditions })
      }
      return t('app.specPreviewConfigureACondition')

    default:
      return t('app.specPreviewConfigureConditions')
  }
})

// Handle template selection
const handleTemplateChange = () => {
  const template = currentTemplateDetail.value
  if (template) {
    specForm.templateType = template.type
    // Clear conditions when template changes
    specForm.aConditions = []
    specForm.ifConditions = []
    specForm.thenConditions = []
    updateFormula()
  }
}

// Validate specification before creation
const validateSpecification = () => {
  if (!specForm.templateId) {
    ElMessage.warning({
      message: t('app.selectSpecTemplate'),
      center: true
    })
    return false
  }
  
  const template = currentTemplateDetail.value
  if (!template) return false
  
  // Check required conditions
  for (const side of template.requiredSides) {
    const conditions = getConditionsForSide(side)
    if (conditions.length === 0) {
      ElMessage.warning({
        message: t('app.addConditionForSide', { side: side.toUpperCase() }),
        center: true
      })
      return false
    }
  }
  
  return true
}

// Create specification
const createSpecification = async () => {
  if (!ensureWritable()) return
  if (creatingSpecification.value || !validateSpecification()) return

  creatingSpecification.value = true
  const saved = await new Promise<boolean>(resolve => {
    emit('add-spec', {
      templateId: specForm.templateId,
      templateType: specForm.templateType,
      devices: specForm.selectedDevices,
      formula: specForm.formula,
      aConditions: specForm.aConditions,
      ifConditions: specForm.ifConditions,
      thenConditions: specForm.thenConditions,
      complete: resolve
    })
  })
  creatingSpecification.value = false
  if (saved) resetSpecForm()
}

// Reset specification form
const resetSpecForm = () => {
  specForm.templateId = ''
  specForm.templateType = ''
  specForm.selectedDevices = []
  specForm.formula = ''
  specForm.aConditions = []
  specForm.ifConditions = []
  specForm.thenConditions = []
}

const handleCreateDevice = async () => {
  if (!ensureWritable()) return
  if (creatingSingleDevice.value) return
  if (!deviceForm.name.trim()) {
    ElMessage({
      message: t('app.enterDeviceName'),
      type: 'warning',
      center: true
    })
    return
  }
  if (singleDeviceNameConflict.value) {
    ElMessage({ message: t('app.deviceNameAlreadyExists'), type: 'warning', center: true })
    return
  }

  if (!deviceForm.type) {
    ElMessage({
      message: t('app.selectDeviceTemplate'),
      type: 'warning',
      center: true
    })
    return
  }

  // Find the selected template from backend templates
  let template = props.deviceTemplates.find((tpl: any) => 
    (tpl.manifest?.Name || tpl.name) === deviceForm.type
  )
  
  if (!template) {
    // Try lowercase match
    template = props.deviceTemplates.find((tpl: any) => 
      (tpl.manifest?.Name || tpl.name)?.toLowerCase() === deviceForm.type.toLowerCase()
    )
  }

  if (!template) {
    ElMessage({
      message: props.templatesLoading
        ? t('app.loadingDeviceTemplates')
        : t('app.templateNotFoundWithName', { name: deviceForm.type || t('app.unknown') }),
      type: 'error',
      center: true
    })
    return
  }

  // Emit device creation event with template.
  // 成功提示由父组件在保存成功后弹出：emit 不会 await 父组件的异步保存，
  // 若在此提前报成功，父组件保存失败并回滚时会同时出现「Device added」和保存失败提示。
  creatingSingleDevice.value = true
  const saved = await new Promise<boolean>(resolve => {
    emit('create-device', {
      template,
      customName: deviceForm.name,
      runtime: buildRuntimeConfig(template as DeviceTemplate),
      complete: resolve
    })
  })
  creatingSingleDevice.value = false
  if (saved) {
    deviceForm.name = ''
    resetSingleDeviceRuntime()
  }
}

const handleCreateBatchDevices = async () => {
  if (!ensureWritable()) return
  if (creatingMultipleDevices.value) return
  if (batchDeviceCountError.value) {
    ElMessage({ message: batchDeviceCountError.value, type: 'warning', center: true })
    return
  }
  if (!batchDeviceForm.type) {
    ElMessage({ message: t('app.selectDeviceTemplate'), type: 'warning', center: true })
    return
  }
  if (!normalizeName(batchDeviceForm.prefix)) {
    ElMessage({ message: t('app.enterDeviceNamePrefix'), type: 'warning', center: true })
    return
  }

  const items = batchDevicePreview.value
  if (items.length === 0) {
    ElMessage({ message: t('app.noDevicesToCreate'), type: 'warning', center: true })
    return
  }

  creatingMultipleDevices.value = true
  await new Promise<boolean>(resolve => emit('create-devices', { items, complete: resolve }))
  creatingMultipleDevices.value = false
}

const handleCreateImportedDevices = async () => {
  if (!ensureWritable()) return
  if (creatingMultipleDevices.value) return
  if (!importDeviceForm.text.trim()) {
    ElMessage({ message: t('app.pasteDeviceImportList'), type: 'warning', center: true })
    return
  }
  if (importedEnvironmentMerge.value.conflicts.length > 0) {
    ElMessage({
      message: formatImportedEnvironmentConflict(importedEnvironmentMerge.value.conflicts[0]),
      type: 'warning',
      center: true
    })
    return
  }
  if (importedDevicesHaveErrors.value) {
    ElMessage({ message: t('app.fixDeviceImportErrors'), type: 'warning', center: true })
    return
  }
  if (validImportedDevices.value.length === 0) {
    ElMessage({ message: t('app.noDevicesToCreate'), type: 'warning', center: true })
    return
  }

  creatingMultipleDevices.value = true
  await new Promise<boolean>(resolve => {
    emit('create-devices', {
      items: validImportedDevices.value.map((item: any) => ({
        template: item.template,
        customName: item.customName,
        runtime: item.runtime
      })),
      environmentVariables: importedEnvironmentMerge.value.merged,
      complete: resolve
    })
  })
  creatingMultipleDevices.value = false
}

const handleDeviceImportFile = async (event: Event) => {
  const target = event.target as HTMLInputElement
  const file = target.files?.[0]
  if (!file) return
  try {
    importDeviceForm.text = await file.text()
  } catch (error) {
    console.error('Failed to read device import file:', error)
    ElMessage.error({ message: t('app.invalidJsonFile'), type: 'error' })
  } finally {
    target.value = ''
  }
}

const handleTemplateDragStart = (template: any, event: DragEvent) => {
  if (!ensureWritable()) {
    event.preventDefault()
    return
  }
  const templateName = getTemplateName(template)
  if (!templateName) return
  closeTemplatePreview()
  event.dataTransfer?.setData('application/x-iot-template', templateName)
  event.dataTransfer?.setData('text/plain', templateName)
  if (event.dataTransfer) {
    event.dataTransfer.effectAllowed = 'copy'
  }
  emit('template-drag-start', templateName)
}

const handleTemplateDragEnd = () => {
  emit('template-drag-end')
}

// Panel state
const localCollapsed = ref(typeof window !== 'undefined' && window.innerWidth < 768)
const localActiveSection = ref<ControlCenterSection>('templates')

const isControlCenterSection = (value: string | undefined): value is ControlCenterSection =>
  value === 'devices' || value === 'templates' || value === 'rules' || value === 'specs'

const isCollapsed = computed({
  get: () => props.collapsed ?? localCollapsed.value,
  set: (value: boolean) => {
    localCollapsed.value = value
    emit('update:collapsed', value)
  }
})

const activeSection = computed<ControlCenterSection>({
  get: () => isControlCenterSection(props.activeSection) ? props.activeSection : localActiveSection.value,
  set: (value: ControlCenterSection) => {
    localActiveSection.value = value
    emit('update:active-section', value)
  }
})

const panelWidth = computed(() => {
  const width = Number.isFinite(props.width) ? props.width : 320
  return `${Math.min(520, Math.max(240, width))}px`
})

// Toggle panel collapse
const togglePanel = () => {
  isCollapsed.value = !isCollapsed.value
}

// Component mounted


const createDevice = () => {
  handleCreateDevice()
}

const isDefinitiveTemplateMutationRejection = (error: any): boolean => {
  const status = Number(error?.response?.status || 0)
  return status >= 400 && status < 500
}

const templateMutationErrorMessage = (error: any, fallback: string): string => {
  if (error?.code === BOARD_RESPONSE_INCOMPLETE_CODE) {
    return t('app.boardMutationResponseIncomplete')
  }
  return localizedErrorMessage(error, fallback, locale.value)
}

const refreshTemplateCatalogForReconciliation = async (): Promise<DeviceTemplate[] | null> => {
  try {
    const current = await boardApi.getDeviceTemplates()
    emit('replace-template-catalog', current)
    return current
  } catch (error) {
    console.error('Failed to reconcile device type catalog:', error)
    return null
  }
}

const handleImportTemplate = async (event: Event) => {
  const target = event.target as HTMLInputElement
  if (!ensureWritable()) {
    target.value = ''
    return
  }
  const file = target.files?.[0]
  if (!file) return

  let manifest: DeviceTemplate['manifest']
  let requestedName: string
  try {
    const text = await file.text()
    manifest = JSON.parse(text)
    requestedName = String(manifest?.Name || '').trim()
  } catch (error: any) {
    const message = templateMutationErrorMessage(error, t('app.invalidJsonFile'))
    ElMessage.error({ message, type: 'error' })
    target.value = ''
    return
  }

  await runBoardMutation(async () => {
    try {
      await boardApi.addDeviceTemplate({ name: requestedName, manifest })
      const current = await boardApi.getDeviceTemplates()
      emit('replace-template-catalog', current)
      ElMessage.success({ message: t('app.templateImportedSuccessfully'), type: 'success' })
    } catch (error: any) {
      if (!isDefinitiveTemplateMutationRejection(error)) {
        const current = await refreshTemplateCatalogForReconciliation()
        if (!current) {
          ElMessage.warning({ message: t('app.templateMutationOutcomeUnknownRefreshFailed'), type: 'warning' })
        } else if (current.some(template =>
          String(template.name || template.manifest?.Name || '').trim().toLocaleLowerCase()
            === requestedName.toLocaleLowerCase())) {
          ElMessage.warning({
            message: t('app.templateImportOutcomeRefreshed', { name: requestedName }),
            type: 'warning'
          })
        } else {
          ElMessage.warning({ message: t('app.templateImportOutcomeUnconfirmedAfterRefresh'), type: 'warning' })
        }
      } else {
        const message = templateMutationErrorMessage(error, t('app.invalidJsonFile'))
        ElMessage.error({ message, type: 'error' })
      }
    }
  })

  // 清空 input 以便重新选择同一文件
  target.value = ''
}

const downloadTemplateSchema = async () => {
  try {
    const schema = await boardApi.getDeviceTemplateSchema()
    const blob = new Blob([JSON.stringify(schema, null, 2)], { type: 'application/json' })
    const url = URL.createObjectURL(blob)
    const linkElement = document.createElement('a')
    linkElement.href = url
    linkElement.download = 'device-template-schema.json'
    linkElement.click()
    URL.revokeObjectURL(url)
  } catch (error) {
    console.error('Failed to download template schema:', error)
    ElMessage.error({ message: t('app.downloadSchemaFailed'), type: 'error' })
  }
}

const openRuleBuilder = () => {
  if (!ensureWritable()) return
  emit('open-rule-builder')
}

const closeTemplateDeleteConfirm = (force = false) => {
  if (isDeletingTemplate.value && !force) return
  showDeleteConfirmDialog.value = false
  templateToDelete.value = null
  templateDeletePreview.value = null
}

const openDeleteConfirm = async (template: any) => {
  if (!ensureWritable()) return
  if (isLoadingTemplateDeletePreview.value) return
  closeTemplatePreview()
  const templateId = Number(template?.id)
  if (!Number.isSafeInteger(templateId) || templateId <= 0) {
    ElMessage.error(t('app.invalidTemplateId'))
    return
  }
  isLoadingTemplateDeletePreview.value = true
  try {
    const preview = await boardApi.previewDeviceTemplateDeletion(templateId)
    templateToDelete.value = preview.template
    templateDeletePreview.value = preview
    showDeleteConfirmDialog.value = true
  } catch (error: any) {
    console.error('Failed to preview template deletion:', error)
    ElMessage.error({
      message: templateMutationErrorMessage(error, t('app.templateDeletePreviewFailed')),
      type: 'error'
    })
  } finally {
    isLoadingTemplateDeletePreview.value = false
  }
}

const closeResetDefaultsConfirm = (force = false) => {
  if (isResettingDefaultTemplates.value && !force) return
  showResetDefaultsConfirmDialog.value = false
  defaultTemplateResetPreview.value = null
}

const openResetDefaultsConfirm = async () => {
  if (!ensureWritable()) return
  if (isLoadingDefaultTemplateResetPreview.value) return
  closeTemplatePreview()
  isLoadingDefaultTemplateResetPreview.value = true
  try {
    defaultTemplateResetPreview.value = await boardApi.previewDefaultTemplateReset()
    showResetDefaultsConfirmDialog.value = true
  } catch (error: any) {
    console.error('Failed to preview default template reset:', error)
    ElMessage.error({
      message: templateMutationErrorMessage(error, t('app.defaultTemplateResetPreviewFailed')),
      type: 'error'
    })
  } finally {
    isLoadingDefaultTemplateResetPreview.value = false
  }
}

const confirmResetDefaultTemplates = async () => {
  if (!ensureWritable()) return
  if (isResettingDefaultTemplates.value) return
  const preview = defaultTemplateResetPreview.value
  if (!preview?.impactToken || !preview.canApply) return
  isResettingDefaultTemplates.value = true
  try {
    await runBoardMutation(async () => {
      try {
        const result = await boardApi.resetDefaultTemplates(preview.impactToken)
        emit('replace-template-state', {
          templates: result.currentTemplates,
          environmentVariables: result.environmentVariables
        })
        ElMessage.success({
          message: t('app.defaultTemplatesResetSuccess', {
            types: result.templateChanges.length,
            devices: result.affectedDevices.length,
            variables: result.environmentChanges.length
          }),
          center: true
        })
        closeResetDefaultsConfirm(true)
      } catch (error: any) {
        console.error('Failed to reset default templates:', error)
        if (!isDefinitiveTemplateMutationRejection(error)) {
          try {
            const [templates, environmentVariables] = await Promise.all([
              boardApi.getDeviceTemplates(),
              boardApi.getEnvironment()
            ])
            emit('replace-template-state', { templates, environmentVariables })
            ElMessage.warning({ message: t('app.templateResetOutcomeRefreshed'), center: true })
            closeResetDefaultsConfirm(true)
          } catch (refreshError) {
            console.error('Failed to reconcile default template reset:', refreshError)
            ElMessage.warning({ message: t('app.templateMutationOutcomeUnknownRefreshFailed'), center: true })
          }
        } else if (Number(error?.response?.status) === 409) {
          try {
            defaultTemplateResetPreview.value = await boardApi.previewDefaultTemplateReset()
            ElMessage.warning({ message: t('app.defaultTemplateResetPreviewChanged'), center: true })
          } catch (previewError) {
            console.error('Failed to refresh default template reset preview:', previewError)
            ElMessage.error({ message: t('app.defaultTemplateResetPreviewFailed'), center: true })
          }
        } else {
          const errorMessage = templateMutationErrorMessage(error, t('app.unknownError'))
          ElMessage.error({
            message: t('app.resetDefaultTemplatesFailedWithReason', { reason: errorMessage }),
            center: true
          })
        }
      }
    })
  } finally {
    isResettingDefaultTemplates.value = false
  }
}

const defaultTemplateResetChangeLabel = (changeType: string): string => {
  const keyByType: Record<string, string> = {
    RESTORE_MISSING: 'app.defaultTemplateChangeRestoreMissing',
    REFRESH_DEFAULT: 'app.defaultTemplateChangeRefresh',
    REPLACE_CUSTOM_NAME_COLLISION: 'app.defaultTemplateChangeReplaceCustom',
    REMOVE_OBSOLETE_DEFAULT: 'app.defaultTemplateChangeRemoveObsolete'
  }
  return t(keyByType[changeType] || 'app.defaultTemplateChangeRefresh')
}

const defaultTemplateResetBlockerReason = (reasonCode: string): string => {
  const keyByCode: Record<string, string> = {
    DEVICE_INSTANCE_INCOMPATIBLE: 'app.defaultTemplateBlockerDevice',
    AUTOMATION_RULE_INCOMPATIBLE: 'app.defaultTemplateBlockerRule',
    SPECIFICATION_INCOMPATIBLE: 'app.defaultTemplateBlockerSpecification',
    ENVIRONMENT_POOL_INCOMPATIBLE: 'app.defaultTemplateBlockerEnvironment',
    BOARD_MODEL_INCOMPATIBLE: 'app.defaultTemplateBlockerBoard'
  }
  return t(keyByCode[reasonCode] || 'app.defaultTemplateBlockerBoard')
}

const confirmDeleteTemplate = async () => {
  if (!ensureWritable()) return
  if (!templateToDelete.value || !templateDeletePreview.value || isDeletingTemplate.value) return

  const templateId = Number(templateToDelete.value.id)
  const templateName = String(templateToDelete.value.name || templateToDelete.value.manifest?.Name || '').trim()
  if (!Number.isSafeInteger(templateId) || templateId <= 0) {
    ElMessage.error(t('app.invalidTemplateId'))
    return
  }

  if (!templateDeletePreview.value.canDelete) {
    ElMessage.warning(t('app.templateDeleteBlocked'))
    return
  }

  isDeletingTemplate.value = true
  try {
    await runBoardMutation(async () => {
    try {
      const result = await boardApi.deleteDeviceTemplate(
        templateId,
        templateDeletePreview.value!.impactToken
      )
      emit('replace-template-catalog', result.currentTemplates)
      ElMessage({
        message: t('app.templateDeleted', { name: result.deletedTemplate?.name || templateName }),
        type: 'success',
        center: true
      })
      closeTemplateDeleteConfirm(true)
    } catch (error: any) {
      console.error('Failed to delete template:', error)
      const conflictPreview = error?.response?.data?.data?.currentPreview
      if (conflictPreview) {
        templateDeletePreview.value = conflictPreview
        templateToDelete.value = conflictPreview.template
        ElMessage.warning({ message: t('app.templateDeletePreviewChanged'), center: true })
        return
      }
      if (!isDefinitiveTemplateMutationRejection(error)) {
        const current = await refreshTemplateCatalogForReconciliation()
        if (!current) {
          ElMessage.warning({ message: t('app.templateMutationOutcomeUnknownRefreshFailed'), center: true })
        } else if (!current.some(template => Number(template.id) === templateId)) {
          ElMessage.warning({
            message: t('app.templateDeleteOutcomeRefreshed', { name: templateName }),
            center: true
          })
          closeTemplateDeleteConfirm(true)
        } else {
          ElMessage.warning({ message: t('app.templateDeleteOutcomeUnconfirmedAfterRefresh'), center: true })
        }
      } else {
        const errorMessage = templateMutationErrorMessage(error, t('app.unknownError'))
        ElMessage({
          message: t('app.deleteFailedWithReason', { reason: errorMessage }),
          type: 'error',
          center: true
        })
      }
    }
    })
  } finally {
    isDeletingTemplate.value = false
  }
}

// Enhanced error handling utility with concise messages
const exportTemplate = (template: any) => {
  try {
    closeTemplatePreview()
    const dataStr = JSON.stringify(template.manifest, null, 2)
    const dataUri = 'data:application/json;charset=utf-8,'+ encodeURIComponent(dataStr)

    const exportFileDefaultName = `${template.manifest.Name}_template.json`

    const linkElement = document.createElement('a')
    linkElement.setAttribute('href', dataUri)
    linkElement.setAttribute('download', exportFileDefaultName)
    linkElement.click()

    ElMessage.success({
      message: t('app.templateDownloadStarted'),
      center: true
    })
  } catch (error) {
    console.error('Failed to export template:', error)
    ElMessage.error({
      message: t('app.exportFailed'),
      center: true
    })
  }
}

</script>

<template>
  <aside
    v-bind="attrs"
    data-testid="control-center"
    class="absolute left-0 top-0 bottom-0 modern-panel board-side-panel z-40 flex flex-col overflow-hidden border-r border-white/20 shadow-xl transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'is-collapsed' : 'is-expanded'"
    :style="{ width: isCollapsed ? '4rem' : panelWidth }"
  >
    <!-- 顶部标题区域 -->
    <div
      class="board-panel-header relative overflow-hidden border-b"
      :class="isCollapsed ? 'p-2.5' : 'p-4'"
    >
      <div v-if="!isCollapsed" class="relative flex items-center justify-between">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-slate-100 rounded-xl flex items-center justify-center">
            <span class="material-symbols-outlined text-slate-600 text-xl">dashboard</span>
          </div>
          <div>
            <h2 class="board-panel-title text-sm font-bold tracking-wide">{{ t('app.controlCenter') }}</h2>
            <p class="board-panel-subtitle text-xs">{{ t('app.deviceManagement') }}</p>
          </div>
        </div>
        <button
          type="button"
          @click="togglePanel"
          class="h-11 w-11 shrink-0 bg-slate-100 hover:bg-slate-200 rounded-lg flex items-center justify-center transition-all hover:scale-105"
          :title="t('app.collapse')"
          :aria-label="t('app.collapse')"
        >
          <span class="material-symbols-outlined text-slate-600 text-base transition-transform duration-200" aria-hidden="true">dock_to_left</span>
        </button>
      </div>
      <div v-else class="flex items-center justify-center">
        <button
          type="button"
          @click="togglePanel"
          class="h-11 w-11 shrink-0 bg-slate-100 hover:bg-slate-200 rounded-xl flex items-center justify-center transition-all hover:scale-105"
          :title="t('app.expand')"
          :aria-label="t('app.expand')"
        >
          <span class="material-symbols-outlined text-slate-600 text-base" aria-hidden="true">dock_to_right</span>
        </button>
      </div>
    </div>

    <!-- Section tabs (only when expanded) -->
    <div v-if="!isCollapsed" class="board-panel-tabs px-4 py-3 border-b">
      <div class="board-segmented grid grid-cols-4 gap-2 p-1 rounded-xl border shadow-sm">
        <button
          @click="activeSection = 'templates'"
          data-testid="control-tab-templates"
          :class="[
            'min-w-0 py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'templates'
              ? 'bg-orange-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
          :title="t('app.templates')"
        >
          <span class="material-symbols-outlined text-sm">inventory_2</span>
          <span class="w-full truncate px-0.5 text-center text-[10px]">{{ t('app.templates') }}</span>
        </button>
        <button
          @click="activeSection = 'devices'"
          data-testid="control-tab-devices"
          :class="[
            'min-w-0 py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'devices'
              ? 'bg-purple-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
          :title="t('app.devices')"
        >
          <span class="material-symbols-outlined text-sm">devices</span>
          <span class="w-full truncate px-0.5 text-center text-[10px]">{{ t('app.devices') }}</span>
        </button>
        <button
          @click="activeSection = 'rules'"
          data-testid="control-tab-rules"
          :class="[
            'min-w-0 py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'rules'
              ? 'bg-blue-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
          :title="t('app.rules')"
        >
          <span class="material-symbols-outlined text-sm">rule</span>
          <span class="w-full truncate px-0.5 text-center text-[10px]">{{ t('app.rules') }}</span>
        </button>
        <button
          @click="activeSection = 'specs'"
          data-testid="control-tab-specs"
          :class="[
            'min-w-0 py-2.5 rounded-lg text-xs font-semibold uppercase tracking-wider transition-all duration-200 flex flex-col items-center gap-1',
            activeSection === 'specs'
              ? 'bg-red-500 text-white shadow-md'
              : 'text-slate-500 hover:bg-slate-200 hover:text-slate-700'
          ]"
          :title="t('app.specifications')"
        >
          <span class="material-symbols-outlined text-sm">verified</span>
          <span class="w-full truncate px-0.5 text-center text-[10px]">{{ t('app.specifications') }}</span>
        </button>
      </div>
    </div>

    <div
      v-if="!isCollapsed"
      class="board-panel-body flex-1 overflow-y-auto custom-scrollbar transition-all duration-300 max-h-[calc(100vh-140px)] p-2"
    >
      <!-- Devices -->
      <details v-if="activeSection === 'devices'" data-testid="control-section-devices" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-purple-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-purple-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">add_circle</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">{{ t('app.deviceManager') }}</span>
              <p class="text-xs text-slate-500">{{ t('app.addAndManageDevices') }}</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 space-y-3 bg-slate-50/50 pt-2">
          <div class="control-mode-tabs">
            <button
              type="button"
              data-testid="device-create-mode-single"
              :class="{ active: deviceCreateMode === 'single' }"
              @click="deviceCreateMode = 'single'"
            >
              {{ t('app.singleDevice') }}
            </button>
            <button
              type="button"
              data-testid="device-create-mode-batch"
              :class="{ active: deviceCreateMode === 'batch' }"
              @click="deviceCreateMode = 'batch'"
            >
              {{ t('app.batchDevices') }}
            </button>
            <button
              type="button"
              data-testid="device-create-mode-import"
              :class="{ active: deviceCreateMode === 'import' }"
              @click="deviceCreateMode = 'import'"
            >
              {{ t('app.importDevices') }}
            </button>
          </div>

          <div v-if="deviceCreateMode === 'single'" class="space-y-3">
            <div class="relative">
              <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">{{ t('app.type') }}</label>
              <div class="relative">
                <span class="absolute left-2.5 top-1/2 -translate-y-1/2 material-symbols-outlined text-slate-400 text-xs">devices</span>
                <select
                  v-model="deviceForm.type"
                  data-testid="single-device-template"
                  class="w-full bg-white border-2 border-slate-200 rounded-lg px-8 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 transition-all appearance-none shadow-sm"
                  :class="isTemplateSelectorDisabled ? 'cursor-not-allowed opacity-70' : 'cursor-pointer'"
                  :disabled="isTemplateSelectorDisabled"
                  :title="templateSelectorTitle"
                >
                  <option v-if="props.templatesLoading" value="">{{ t('app.loadingDeviceTemplates') }}</option>
                  <option v-else-if="deviceTypes.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectDeviceTemplate') }}</option>
                  <option v-for="type in deviceTypes" :key="type" :value="type">{{ type }}</option>
                </select>
              </div>
            </div>

            <div class="relative">
              <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">{{ t('app.deviceName') }}</label>
              <div class="relative">
                <span class="absolute left-2.5 top-1/2 -translate-y-1/2 material-symbols-outlined text-slate-400 text-xs">badge</span>
                <input
                  v-model="deviceForm.name"
                  data-testid="single-device-name"
                  class="w-full bg-white border-2 rounded-lg px-8 py-2 text-xs text-slate-700 focus:ring-2 placeholder:text-slate-400 transition-all shadow-sm"
                  :class="singleDeviceNameConflict
                    ? 'border-red-300 focus:border-red-400 focus:ring-red-100/50'
                    : 'border-slate-200 focus:border-purple-400 focus:ring-purple-100/50'"
                  :placeholder="t('app.deviceNamePlaceholder')"
                  :title="deviceForm.name || t('app.deviceNamePlaceholder')"
                  type="text"
                />
              </div>
              <p v-if="singleDeviceNameConflict" class="mt-1 text-[10px] font-semibold text-red-600" data-testid="single-device-name-conflict">
                {{ t('app.deviceNameAlreadyExists') }}
              </p>
            </div>

            <details
              v-if="hasSingleDeviceRuntimeFields"
              data-testid="single-device-runtime"
              class="device-runtime-box rounded-xl border border-purple-100 bg-white/80 p-3 shadow-sm"
            >
              <summary
                data-testid="single-device-runtime-toggle"
                class="flex cursor-pointer select-none items-center justify-between gap-2 text-[11px] font-bold text-slate-600"
              >
                <span class="inline-flex items-center gap-1.5">
                  <span class="material-symbols-outlined text-sm text-purple-500" aria-hidden="true">tune</span>
                  {{ t('app.advancedInitialValuesOverrides') }}
                </span>
                <span class="material-symbols-outlined text-sm text-slate-400 transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
              </summary>
              <p class="mt-2 text-[10px] leading-relaxed text-slate-500">
                {{ t('app.initialValuesHint') }}
              </p>

              <div v-if="selectedTemplateHasModes" class="mt-3 grid grid-cols-1 gap-2 sm:grid-cols-3">
                <label class="min-w-0">
                  <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.initialState') }}</span>
                  <select
                    v-model="singleDeviceRuntime.state"
                    data-testid="single-device-state"
                    class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition-all focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50"
                  >
                    <option v-for="state in selectedWorkingStates" :key="state.Name" :value="state.Name">{{ state.Name }}</option>
                  </select>
                </label>

                <label class="min-w-0">
                  <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.stateTrust') }}</span>
                  <select
                    v-model="singleDeviceRuntime.currentStateTrust"
                    data-testid="single-device-state-trust"
                    class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition-all focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50"
                  >
                    <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${findTemplateStateTrust(selectedDeviceTemplate, singleDeviceRuntime.state) || 'trusted'}`) }) }}</option>
                    <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                  </select>
                </label>

                <label class="min-w-0">
                  <span class="mb-1 block text-[10px] font-bold uppercase tracking-wide text-slate-500">{{ t('app.statePrivacy') }}</span>
                  <select
                    v-model="singleDeviceRuntime.currentStatePrivacy"
                    data-testid="single-device-state-privacy"
                    class="w-full rounded-lg border-2 border-slate-200 bg-white px-2 py-2 text-xs text-slate-700 shadow-sm transition-all focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50"
                  >
                    <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${findTemplateStatePrivacy(selectedDeviceTemplate, singleDeviceRuntime.state) || 'public'}`) }) }}</option>
                    <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
                  </select>
                </label>
              </div>

              <div v-if="selectedInternalVariables.length > 0" class="mt-3 space-y-2">
                <div
                  v-for="variable in selectedInternalVariables"
                  :key="variable.Name"
                  class="rounded-lg border border-slate-200 bg-slate-50/80 p-2"
                >
                  <div class="mb-2 flex items-center justify-between gap-2">
                    <span class="truncate text-[11px] font-bold text-slate-700" :title="variable.Name">{{ variable.Name }}</span>
                    <span v-if="templateVariableUsesNumericBounds(variable)" class="text-[10px] font-semibold text-slate-400">
                      {{ variableInputPlaceholder(variable) }}
                    </span>
                  </div>

                  <div class="grid grid-cols-[minmax(0,1fr)_5.8rem_5.8rem] gap-2">
                    <label class="min-w-0">
                      <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400">{{ t('app.variableValue') }}</span>
                      <select
                        v-if="templateVariableHasEnumValues(variable)"
                        v-model="singleDeviceRuntime.variables[variable.Name]"
                        :data-testid="`single-device-variable-${variable.Name}`"
                        class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700"
                      >
                        <option value="">{{ t('app.useTemplateDefault') }}</option>
                        <option v-for="value in variable.Values" :key="value" :value="String(value)">{{ value }}</option>
                      </select>
                      <input
                        v-else
                        v-model="singleDeviceRuntime.variables[variable.Name]"
                        :data-testid="`single-device-variable-${variable.Name}`"
                        class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-2 py-1.5 text-xs text-slate-700 placeholder:text-slate-400"
                        :placeholder="variableInputPlaceholder(variable)"
                        type="text"
                      />
                    </label>

                    <label class="min-w-0">
                      <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400">{{ t('app.variableTrust') }}</span>
                      <select
                        v-model="singleDeviceRuntime.variableTrusts[variable.Name]"
                        :data-testid="`single-device-variable-trust-${variable.Name}`"
                        class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-1.5 py-1.5 text-[11px] text-slate-700"
                      >
                        <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${variable.Trust || 'trusted'}`) }) }}</option>
                        <option v-for="trust in TRUST_OPTIONS" :key="trust" :value="trust">{{ t(`app.${trust}`) }}</option>
                      </select>
                    </label>

                    <label class="min-w-0">
                      <span class="mb-1 block text-[9px] font-bold uppercase text-slate-400">{{ t('app.privacy') }}</span>
                      <select
                        v-model="singleDeviceRuntime.privacies[variable.Name]"
                        :data-testid="`single-device-privacy-${variable.Name}`"
                        class="w-full min-w-0 rounded-lg border border-slate-200 bg-white px-1.5 py-1.5 text-[11px] text-slate-700"
                      >
                        <option value="">{{ t('app.useTemplateDefaultWithValue', { value: t(`app.${variable.Privacy || 'public'}`) }) }}</option>
                        <option v-for="privacy in PRIVACY_OPTIONS" :key="privacy" :value="privacy">{{ t(`app.${privacy}`) }}</option>
                      </select>
                    </label>
                  </div>
                </div>
              </div>
            </details>

            <button
              @click="createDevice()"
              data-testid="single-device-create"
              :disabled="isTemplateSelectorDisabled || creatingSingleDevice || !deviceForm.name.trim() || singleDeviceNameConflict"
              class="w-full py-2.5 bg-purple-500 hover:bg-purple-600 disabled:bg-purple-300 disabled:cursor-not-allowed disabled:hover:scale-100 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-1.5"
            >
              <span class="material-symbols-outlined text-sm">add_location</span>
              {{ creatingSingleDevice ? t('app.saving') : `${t('app.add')} ${t('app.dropNode')}` }}
            </button>
          </div>

          <div v-else-if="deviceCreateMode === 'batch'" class="space-y-3">
            <div class="relative">
              <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">{{ t('app.type') }}</label>
              <select
                v-model="batchDeviceForm.type"
                data-testid="batch-device-template"
                class="w-full bg-white border-2 border-slate-200 rounded-lg px-3 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 transition-all appearance-none shadow-sm"
                :disabled="isTemplateSelectorDisabled"
              >
                <option v-if="props.templatesLoading" value="">{{ t('app.loadingDeviceTemplates') }}</option>
                <option v-else-if="deviceTypes.length === 0" value="">{{ t('app.none') }}</option>
                <option v-else value="" disabled hidden>{{ t('app.selectDeviceTemplate') }}</option>
                <option v-for="type in deviceTypes" :key="type" :value="type">{{ type }}</option>
              </select>
            </div>

            <div class="grid grid-cols-[minmax(0,1fr)_5.5rem] gap-2">
              <div>
                <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">{{ t('app.deviceNamePrefix') }}</label>
                <input
                  v-model="batchDeviceForm.prefix"
                  data-testid="batch-device-prefix"
                  class="w-full bg-white border-2 border-slate-200 rounded-lg px-3 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 placeholder:text-slate-400 transition-all shadow-sm"
                  :placeholder="t('app.devicePrefixPlaceholder')"
                  type="text"
                />
              </div>
              <div>
                <label class="block text-[10px] font-bold text-slate-500 mb-1 uppercase tracking-wide">{{ t('app.count') }}</label>
                <input
                  v-model.number="batchDeviceForm.count"
                  data-testid="batch-device-count"
                  class="w-full bg-white border-2 border-slate-200 rounded-lg px-2 py-2 text-xs text-slate-700 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50 transition-all shadow-sm"
                  type="number"
                  min="1"
                  :max="MAX_BATCH_DEVICE_COUNT"
                />
                <p v-if="batchDeviceCountError" class="mt-1 text-[10px] font-semibold leading-4 text-red-600">
                  {{ batchDeviceCountError }}
                </p>
              </div>
            </div>

            <div class="device-preview-box">
              <div class="device-preview-box__header">
                <span>{{ t('app.deviceBatchPreview') }}</span>
                <strong>{{ batchDevicePreview.length }}</strong>
              </div>
              <div v-if="batchDevicePreview.length > 0" class="device-preview-list">
                <div v-for="item in batchDevicePreview.slice(0, 8)" :key="item.customName" class="device-preview-row">
                  <span class="truncate">{{ item.customName }}</span>
                  <small class="truncate">{{ getTemplateName(item.template) }}</small>
                </div>
                <p v-if="batchDevicePreview.length > 8" class="device-preview-more">
                  +{{ batchDevicePreview.length - 8 }}
                </p>
              </div>
              <p v-else class="device-preview-empty">{{ t('app.configureBatchDevicesFirst') }}</p>
            </div>

            <button
              @click="handleCreateBatchDevices"
              data-testid="batch-device-create"
              :disabled="Boolean(batchDeviceCountError) || batchDevicePreview.length === 0 || creatingMultipleDevices"
              class="w-full py-2.5 bg-purple-500 hover:bg-purple-600 disabled:bg-purple-300 disabled:cursor-not-allowed disabled:hover:scale-100 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-1.5"
            >
              <span class="material-symbols-outlined text-sm">playlist_add</span>
              {{ creatingMultipleDevices ? t('app.saving') : t('app.createDevicesWithCount', { count: batchDevicePreview.length }) }}
            </button>
          </div>

          <div v-else class="space-y-3">
            <div class="device-import-help">
              <span class="material-symbols-outlined text-sm" aria-hidden="true">info</span>
              <span class="min-w-0 flex-1 truncate" :title="t('app.deviceImportShortHint')">
                {{ t('app.deviceImportShortHint') }}
              </span>
              <button
                type="button"
                class="device-import-help__trigger"
                :aria-label="t('app.deviceImportHelpTitle')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">help</span>
                <span class="device-import-help__tooltip" role="tooltip">
                  {{ t('app.deviceImportHint') }}
                </span>
              </button>
            </div>
            <div class="flex items-center justify-between gap-2">
              <label class="inline-flex cursor-pointer items-center gap-1.5 rounded-md border border-purple-200 bg-white px-2.5 py-1.5 text-[10px] font-bold text-purple-700 transition-colors hover:bg-purple-50">
                <input data-testid="device-import-file" type="file" accept=".json,.csv,.txt" class="hidden" @change="handleDeviceImportFile">
                <span class="material-symbols-outlined text-xs">upload_file</span>
                {{ t('app.chooseFile') }}
              </label>
              <span class="text-[10px] font-semibold text-slate-400">{{ t('app.jsonOrCsv') }}</span>
            </div>
            <textarea
              v-model="importDeviceForm.text"
              data-testid="device-import-text"
              class="min-h-32 w-full resize-y rounded-lg border-2 border-slate-200 bg-white px-3 py-2 font-mono text-[11px] leading-relaxed text-slate-700 shadow-sm transition-all placeholder:text-slate-400 focus:border-purple-400 focus:ring-2 focus:ring-purple-100/50"
              :placeholder="deviceImportPlaceholder"
            ></textarea>

            <div v-if="parsedImportedDevices.length > 0" class="device-preview-box">
              <div class="device-preview-box__header">
                <span>{{ t('app.parsedDevices') }}</span>
                <strong>{{ validImportedDevices.length }}/{{ parsedImportedDevices.length }}</strong>
              </div>
              <div class="device-preview-list device-preview-list--scroll">
                <div
                  v-for="item in parsedImportedDevices"
                  :key="`${item.source}-${item.templateName}-${item.name}`"
                  class="device-preview-row"
                  :class="{ 'has-error': item.error, 'has-warning': item.warning && !item.error }"
                >
                  <span class="truncate">{{ item.customName || item.name || t('app.unnamed') }}</span>
                  <small class="truncate" :title="item.error || item.warning || item.templateName">
                    {{ item.error || item.warning || item.templateName }}
                  </small>
                </div>
              </div>
            </div>

            <div
              v-if="importedEnvironmentMerge.conflicts.length > 0"
              data-testid="device-import-environment-conflicts"
              class="space-y-1 rounded-lg border border-red-200 bg-red-50 px-3 py-2 text-[10px] font-semibold leading-4 text-red-700"
            >
              <div v-for="(conflict, index) in importedEnvironmentMerge.conflicts" :key="`${conflict.name}-${conflict.field}-${index}`">
                {{ formatImportedEnvironmentConflict(conflict) }}
              </div>
            </div>

            <button
              @click="handleCreateImportedDevices"
              data-testid="device-import-create"
              :disabled="validImportedDevices.length === 0 || importedDevicesHaveErrors || creatingMultipleDevices"
              class="w-full py-2.5 bg-purple-500 hover:bg-purple-600 disabled:bg-purple-300 disabled:cursor-not-allowed disabled:hover:scale-100 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] flex items-center justify-center gap-1.5"
            >
              <span class="material-symbols-outlined text-sm">library_add</span>
              {{ creatingMultipleDevices ? t('app.saving') : t('app.createDevicesWithCount', { count: validImportedDevices.length }) }}
            </button>
          </div>
        </div>
      </details>

      <!-- Templates -->
      <div v-if="activeSection === 'templates'" data-testid="control-section-templates" class="space-y-3">
        <details data-testid="control-template-create" class="group rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
          <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-orange-50 transition-all list-none select-none">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 bg-orange-500 rounded-xl flex items-center justify-center">
                <span class="material-symbols-outlined text-white text-lg">add_box</span>
              </div>
              <div>
                <span class="text-sm font-bold text-slate-800">{{ t('app.createTemplate') }}</span>
                <p class="text-xs text-slate-500">{{ t('app.createTemplateSubtitleShort') }}</p>
              </div>
            </div>
            <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
          </summary>

          <div class="px-3 pb-4 bg-slate-50/50 pt-2 space-y-3">
            <div class="relative overflow-hidden rounded-lg border-2 border-dashed border-orange-300 bg-orange-50 transition-all hover:border-orange-500 hover:shadow-md">
              <label class="group cursor-pointer block">
                <input type="file" accept=".json" class="hidden" @change="handleImportTemplate">
                <div class="p-3 flex items-center gap-3">
                  <div class="w-9 h-9 bg-orange-400 rounded-lg flex items-center justify-center flex-shrink-0 group-hover:bg-orange-500 transition-colors">
                    <span class="material-symbols-outlined text-white text-base">upload_file</span>
                  </div>
                  <div class="min-w-0 flex-1">
                    <div class="text-xs font-bold text-orange-700">{{ t('app.importJsonTemplate') }}</div>
                    <p class="text-[10px] text-orange-600 truncate" :title="t('app.deviceTemplateSchemaHint')">
                      {{ t('app.deviceTemplateSchemaHint') }}
                    </p>
                  </div>
                </div>
              </label>
              <button
                type="button"
                class="mx-3 mb-3 inline-flex items-center gap-1.5 rounded-md border border-orange-200 bg-white/80 px-2 py-1 text-[10px] font-bold text-orange-700 transition-colors hover:bg-orange-100"
                :title="t('app.downloadTemplateSchema')"
                @click="downloadTemplateSchema"
              >
                <span class="material-symbols-outlined text-xs">download</span>
                {{ t('app.downloadTemplateSchema') }}
              </button>
            </div>
          </div>
        </details>

        <details data-testid="control-template-repository" class="group rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
          <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-orange-50 transition-all list-none select-none">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 bg-orange-500 rounded-xl flex items-center justify-center">
                <span class="material-symbols-outlined text-white text-lg">inventory_2</span>
              </div>
              <div>
                <span class="text-sm font-bold text-slate-800">{{ t('app.templateRepository') }}</span>
                <p class="text-xs text-slate-500">{{ t('app.templateRepositoryHint') }}</p>
              </div>
            </div>
            <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
          </summary>

          <div class="px-3 pb-4 bg-slate-50/50 pt-2 space-y-3">
            <div class="rounded-lg border border-orange-200 bg-orange-50/70 px-3 py-2 text-[10px] font-semibold leading-relaxed text-orange-700">
              {{ t('app.dragTemplateToCanvasHint') }}
            </div>

            <div class="relative">
              <span class="absolute left-2.5 top-1/2 -translate-y-1/2 material-symbols-outlined text-slate-400 text-xs">search</span>
              <input
                v-model="templateSearchQuery"
                class="w-full bg-white border-2 border-slate-200 rounded-lg px-8 py-2 text-xs text-slate-700 focus:border-orange-400 focus:ring-2 focus:ring-orange-100/50 placeholder:text-slate-400 transition-all shadow-sm"
                :placeholder="t('app.searchTemplates')"
                type="text"
              />
              <button
                v-if="templateSearchQuery"
                @click="templateSearchQuery = ''"
                class="absolute right-2 top-1/2 -translate-y-1/2 text-slate-400 hover:text-slate-600 transition-colors"
              >
                <span class="material-symbols-outlined text-xs">close</span>
              </button>
            </div>

            <div class="flex items-center justify-between px-1">
              <div class="flex items-center gap-1.5">
                <span class="material-symbols-outlined text-slate-400 text-xs">folder_open</span>
                <span class="text-[10px] font-bold text-slate-500 uppercase tracking-wide">{{ t('app.templates') }}</span>
              </div>
              <div class="flex items-center gap-1.5">
                <button
                  type="button"
                  data-testid="reset-default-templates"
                  class="inline-flex items-center gap-1 rounded-full border border-orange-200 bg-white px-2 py-0.5 text-[10px] font-bold text-orange-700 transition-colors hover:bg-orange-50 disabled:cursor-not-allowed disabled:opacity-60"
                  :disabled="props.templatesLoading || isLoadingDefaultTemplateResetPreview"
                  :title="t('app.resetDefaultTemplates')"
                  @click="openResetDefaultsConfirm"
                >
                  <span
                    v-if="isLoadingDefaultTemplateResetPreview"
                    class="template-reset-dialog__spinner"
                    aria-hidden="true"
                  ></span>
                  <span v-else class="material-symbols-outlined text-xs" aria-hidden="true">restart_alt</span>
                  <span class="truncate">{{ t('app.resetDefaultTemplatesShort') }}</span>
                </button>
                <span class="text-[10px] font-bold text-orange-600 bg-orange-50 px-2 py-0.5 rounded-full">
                  {{ filteredTemplates.length }}
                </span>
              </div>
            </div>

            <div
              v-if="props.templatesLoading"
              class="rounded-xl border border-dashed border-orange-200 bg-orange-50/60 px-3 py-6 text-center text-xs text-orange-700"
            >
              <span class="material-symbols-outlined mb-2 block animate-spin text-2xl">sync</span>
              <p class="font-semibold">{{ t('app.loadingDeviceTemplates') }}</p>
              <p class="mt-1 text-[10px] text-orange-500">{{ t('app.preparingDefaultTemplates') }}</p>
            </div>

            <div v-else-if="filteredTemplates.length > 0" class="space-y-2.5">
              <details
                v-for="group in templateGroups"
                :key="group.key"
                class="template-group rounded-lg border shadow-sm"
                :data-testid="`template-group-${group.key}`"
                open
              >
                <summary class="template-group__summary flex cursor-pointer select-none items-center justify-between gap-2 px-2.5 py-2 transition-colors">
                  <div class="flex min-w-0 items-center gap-2">
                    <span class="template-group__chevron material-symbols-outlined text-sm transition-transform">expand_more</span>
                    <span class="template-group__label truncate text-[10px] font-bold uppercase tracking-wide" :title="group.label">{{ group.label }}</span>
                  </div>
                  <span class="template-group__count rounded-full px-2 py-0.5 text-[10px] font-bold">{{ group.templates.length }}</span>
                </summary>

                <div v-if="group.templates.length > 0" class="template-group__grid grid grid-cols-2 gap-2 px-2.5 pb-2.5">
                  <div
                    v-for="template in group.templates"
                    :key="template.id"
                    class="template-card relative rounded-lg p-2 border transition-all duration-200"
                    :class="{ 'template-card--active': isTemplatePreviewVisible(template) }"
                    role="button"
                    tabindex="0"
                    draggable="true"
                    :aria-label="`${t('app.viewTemplateDetails')}: ${getTemplateName(template)}`"
                    :title="getTemplateName(template)"
                    @click.stop="toggleTemplatePreview(template, $event)"
                    @keydown.enter.prevent="toggleTemplatePreview(template, $event)"
                    @keydown.space.prevent="toggleTemplatePreview(template, $event)"
                    @dragstart.stop="handleTemplateDragStart(template, $event)"
                    @dragend="handleTemplateDragEnd"
                  >
                    <div class="relative">
                      <div class="flex items-start gap-2">
                        <div class="template-card__icon w-7 h-7 rounded flex items-center justify-center transition-all shadow-sm overflow-hidden flex-shrink-0" v-html="getTemplateIcon(template)"></div>
                        <div class="min-w-0 flex-1">
                          <div class="flex min-w-0 items-start gap-1">
                            <h4 class="template-card__title min-w-0 flex-1 text-xs font-bold transition-colors truncate" :title="getTemplateName(template)">
                              {{ getTemplateName(template) }}
                            </h4>
                            <span class="template-card__drag-cue material-symbols-outlined" :title="t('app.dragTemplateToCanvas')">drag_indicator</span>
                          </div>
                          <div class="template-card__stats text-[9px] mt-0.5 flex items-center gap-1.5">
                            <span class="template-card__pill px-1.5 py-0.5 rounded">{{ template.manifest.InternalVariables?.length || 0 }} {{ t('app.varsShort') }}</span>
                            <span class="template-card__pill px-1.5 py-0.5 rounded">{{ template.manifest.APIs?.length || 0 }} {{ t('app.apisShort') }}</span>
                          </div>
                        </div>
                      </div>

                      <div class="template-card__actions mt-0.5 pt-0.5 border-t flex justify-end gap-1">
                        <button
                          @click.stop="exportTemplate(template)"
                          @dragstart.stop.prevent
                          class="template-card__action cursor-pointer p-1 rounded transition-colors"
                          :title="t('app.export')"
                        >
                          <span class="material-symbols-outlined text-xs">download</span>
                        </button>
                        <button
                          @click.stop="openDeleteConfirm(template)"
                          @dragstart.stop.prevent
                          class="template-card__action template-card__action--danger cursor-pointer p-1 rounded transition-colors"
                          :title="t('app.delete')"
                        >
                          <span class="material-symbols-outlined text-xs">delete</span>
                        </button>
                      </div>
                    </div>
                  </div>
                </div>

                <div v-else class="template-group__empty mx-2.5 mb-2.5 rounded-lg border border-dashed px-3 py-2 text-center text-[10px]">
                  {{ group.key === 'default' ? t('app.noDefaultTemplates') : t('app.noCustomTemplates') }}
                </div>
              </details>
            </div>

            <div v-else class="relative overflow-hidden text-center py-8 border-2 border-dashed border-slate-200 rounded-xl bg-slate-50/50">
              <div class="absolute top-0 left-0 w-full h-1 bg-gradient-to-r from-orange-300 via-orange-400 to-orange-300"></div>
              <div class="relative">
                <div class="w-14 h-14 mx-auto bg-orange-100 rounded-full flex items-center justify-center mb-3 shadow-inner">
                  <span class="material-symbols-outlined text-orange-400 text-2xl">inventory_2</span>
                </div>
                <p class="text-xs text-slate-600 mb-1 font-semibold">
                  {{ templateSearchQuery ? t('app.noMatchingTemplates') : t('app.noTemplatesYet') }}
                </p>
                <p class="text-[10px] text-slate-400">
                  {{ templateSearchQuery ? t('app.tryDifferentSearchTerm') : t('app.importJsonTemplateHint') }}
                </p>
                <button
                  v-if="templateSearchQuery"
                  @click="templateSearchQuery = ''"
                  class="mt-3 px-4 py-1.5 text-[10px] font-semibold text-orange-600 bg-orange-50 hover:bg-orange-100 rounded-lg transition-colors"
                >
                  {{ t('app.clearSearch') }}
                </button>
              </div>
            </div>
          </div>
        </details>
      </div>

      <!-- Rules -->
      <details v-if="activeSection === 'rules'" data-testid="control-section-rules" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-blue-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-blue-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">function</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">{{ t('app.iftttRule') }}</span>
              <p class="text-xs text-slate-500">{{ t('app.createConditionalLogic') }}</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 bg-slate-50/50 pt-2 grid grid-cols-1 gap-3">
          <!-- Rule Creation Block -->
          <button
            type="button"
            data-testid="open-rule-builder"
            class="relative w-full overflow-hidden border-0 text-left group cursor-pointer rounded-xl bg-blue-500 hover:bg-blue-600 transition-all hover:shadow-lg hover:-translate-y-0.5 focus-visible:outline focus-visible:outline-3 focus-visible:outline-offset-2 focus-visible:outline-blue-300"
            @click="openRuleBuilder"
          >
            <div class="relative p-3 flex items-center gap-3">
              <div class="w-10 h-10 bg-blue-400 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-black text-lg">add_circle</span>
              </div>
              <div class="flex-1">
                <span class="text-sm font-bold text-white block">{{ t('app.createRule') }}</span>
                <span class="text-xs text-blue-100">{{ t('app.ifThenLogic') }}</span>
              </div>
              <div class="w-7 h-7 bg-blue-400 rounded-lg flex items-center justify-center">
                <span class="material-symbols-outlined text-white text-sm">arrow_forward</span>
              </div>
            </div>
          </button>
        </div>
      </details>

      <!-- Specs -->
      <details v-if="activeSection === 'specs'" data-testid="control-section-specs" class="group mb-3 rounded-xl bg-white shadow-sm border border-slate-200 overflow-hidden" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-red-50 transition-all list-none select-none">
          <div class="flex items-center gap-3">
            <div class="w-10 h-10 bg-red-500 rounded-xl flex items-center justify-center">
              <span class="material-symbols-outlined text-white text-lg">verified</span>
            </div>
            <div>
              <span class="text-sm font-bold text-slate-800">{{ t('app.specifications') }}</span>
              <p class="text-xs text-slate-500">{{ t('app.ltlVerificationRules') }}</p>
            </div>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-lg">expand_more</span>
        </summary>

        <div class="px-3 pb-4 bg-slate-50/50 pt-2 space-y-3">
          <!-- Specification Creation -->
          <div class="space-y-3">
            <!-- Step 1: Select Template -->
            <div>
              <label class="block text-[10px] font-bold text-slate-600 uppercase tracking-wide mb-2">{{ t('app.selectTemplate') }}</label>
              <select
                v-model="specForm.templateId"
                data-testid="spec-template-select"
                @change="handleTemplateChange"
                class="w-full bg-white border-2 border-slate-200 rounded-lg px-3 py-2 text-xs text-slate-700 focus:border-red-400 focus:ring-2 focus:ring-red-100/50 transition-all shadow-sm appearance-none cursor-pointer"
              >
                <option value="" disabled hidden>{{ t('app.selectSpecificationTemplate') }}</option>
                <option
                  v-for="template in specTemplateDetails"
                  :key="template.id"
                  :value="template.id"
                  class="truncate"
                >
                  {{ templateMessage(template.labelKey, template.label) }}
                </option>
              </select>
              <p v-if="currentTemplateDetail" class="text-[10px] text-slate-500 mt-1.5 px-1">
                <span class="line-clamp-2">
                  {{ templateMessage(currentTemplateDetail.descriptionKey, currentTemplateDetail.description) }}
                </span>
              </p>
            </div>

            <!-- Step 2: Add Conditions based on template requirements -->
            <div v-if="specForm.templateId" class="space-y-2">
              <label class="block text-[10px] font-bold text-slate-600 uppercase tracking-wide">{{ t('app.configureConditions') }}</label>

              <!-- A Conditions (Always/Forall) -->
              <div v-if="isSideRequired('a')" class="relative overflow-hidden rounded-lg bg-red-50 border border-red-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-red-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="currentColor" viewBox="0 0 24 24">
                        <path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-2 15l-5-5 1.41-1.41L10 14.17l7.59-7.59L19 8l-9 9z"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-red-700 uppercase tracking-wide">{{ t('app.aConditions') }}</span>
                  </div>
                  <button
                    @click="openConditionDialog('a')"
                    data-testid="spec-add-condition-a"
                    class="px-2.5 py-1 bg-red-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-red-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    {{ t('app.add') }}
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.aConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-red-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0" :title="getDeviceLabel(condition.deviceId)">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-red-600 font-medium truncate flex-shrink-0" :title="formatConditionPropertyLabel(condition)">{{ formatConditionPropertyLabel(condition) }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-red-50 text-red-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-red-200 flex-shrink-0" :title="formatConditionValue(condition.value)">
                          {{ formatConditionValue(condition.value) }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('a', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" :title="t('app.edit')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('a', index)" class="p-1 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded transition-colors" :title="t('app.delete')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.aConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-red-200">
                    {{ t('app.noConditionsAdded') }}
                  </div>
                </div>
              </div>

              <!-- IF Conditions (Antecedent) -->
              <div v-if="isSideRequired('if')" class="relative overflow-hidden rounded-lg bg-red-50 border border-red-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-red-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-red-700 uppercase tracking-wide">{{ t('app.ifConditions') }}</span>
                  </div>
                  <button
                    @click="openConditionDialog('if')"
                    data-testid="spec-add-condition-if"
                    class="px-2.5 py-1 bg-red-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-red-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    {{ t('app.add') }}
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.ifConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-red-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0" :title="getDeviceLabel(condition.deviceId)">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-red-600 font-medium truncate flex-shrink-0" :title="formatConditionPropertyLabel(condition)">{{ formatConditionPropertyLabel(condition) }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-red-50 text-red-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-red-200 flex-shrink-0" :title="formatConditionValue(condition.value)">
                          {{ formatConditionValue(condition.value) }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('if', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" :title="t('app.edit')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('if', index)" class="p-1 text-slate-400 hover:text-red-500 hover:bg-red-50 rounded transition-colors" :title="t('app.delete')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.ifConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-red-200">
                    {{ t('app.noConditionsAdded') }}
                  </div>
                </div>
              </div>

              <!-- THEN Conditions (Consequent) -->
              <div v-if="isSideRequired('then')" class="relative overflow-hidden rounded-lg bg-yellow-50 border border-yellow-200 p-2.5">
                <div class="relative flex items-center justify-between mb-2">
                  <div class="flex items-center gap-2">
                    <span class="w-6 h-6 bg-yellow-500 rounded-md flex items-center justify-center">
                      <svg class="w-4 h-4 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M17 8l4 4m0 0l-4 4m4-4H3"/>
                      </svg>
                    </span>
                    <span class="text-[10px] font-bold text-yellow-700 uppercase tracking-wide">{{ t('app.thenConditions') }}</span>
                  </div>
                  <button
                    @click="openConditionDialog('then')"
                    data-testid="spec-add-condition-then"
                    class="px-2.5 py-1 bg-yellow-500 text-white rounded-md text-[10px] font-bold uppercase tracking-wide hover:bg-yellow-600 transition-all shadow-sm flex items-center gap-1"
                  >
                    <svg class="w-3 h-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4v16m8-8H4"/>
                    </svg>
                    {{ t('app.add') }}
                  </button>
                </div>
                <div class="space-y-1.5 max-h-36 overflow-y-auto pr-1 custom-scrollbar">
                  <div
                    v-for="(condition, index) in specForm.thenConditions"
                    :key="condition.id"
                    class="flex items-center justify-between bg-white rounded-md px-2.5 py-1.5 border border-yellow-100 shadow-sm hover:shadow-md transition-all"
                  >
                    <div class="flex items-center gap-2 overflow-hidden flex-1">
                      <div class="w-6 h-6 bg-yellow-100 rounded-md flex items-center justify-center flex-shrink-0">
                        <svg class="w-3.5 h-3.5 text-yellow-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 3v2m6-2v2M9 19v2m6-2v2M5 9H3m2 6H3m18-6h-2m2 6h-2M7 19h10a2 2 0 002-2V7a2 2 0 00-2-2H7a2 2 0 00-2 2v10a2 2 0 002 2zM9 9h6v6H9V9z"/>
                        </svg>
                      </div>
                      <div class="flex items-center gap-1 overflow-hidden flex-1 min-w-0">
                        <span class="text-[10px] text-slate-700 font-medium truncate min-w-0" :title="getDeviceLabel(condition.deviceId)">
                          {{ getDeviceLabel(condition.deviceId) }}
                        </span>
                        <span class="text-slate-300 flex-shrink-0">·</span>
                        <span class="text-[10px] text-yellow-600 font-medium truncate flex-shrink-0" :title="formatConditionPropertyLabel(condition)">{{ formatConditionPropertyLabel(condition) }}</span>
                        <span class="text-[10px] text-slate-400 bg-slate-100 px-1 py-0.5 rounded flex-shrink-0">
                          {{ getRelationLabel(condition.relation || '=') }}
                        </span>
                        <span class="text-[10px] bg-yellow-50 text-yellow-600 px-1 py-0.5 rounded truncate max-w-[60px] border border-yellow-200 flex-shrink-0" :title="formatConditionValue(condition.value)">
                          {{ formatConditionValue(condition.value) }}
                        </span>
                      </div>
                    </div>
                    <div class="flex gap-1 ml-2 flex-shrink-0">
                      <button @click="openConditionDialog('then', index)" class="p-1 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded transition-colors" :title="t('app.edit')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
                        </svg>
                      </button>
                      <button @click="removeCondition('then', index)" class="p-1 text-slate-400 hover:text-yellow-500 hover:bg-yellow-50 rounded transition-colors" :title="t('app.delete')">
                        <svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                          <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 7l-.867 12.142A2 2 0 0116.138 21H7.862a2 2 0 01-1.995-1.858L5 7m5 4v6m4-6v6m1-10V4a1 1 0 00-1-1h-4a1 1 0 00-1 1v3M4 7h16"/>
                        </svg>
                      </button>
                    </div>
                  </div>
                  <div v-if="specForm.thenConditions.length === 0" class="text-center py-2 text-[10px] text-slate-400 italic bg-white/50 rounded border border-dashed border-yellow-200">
                    {{ t('app.noConditionsAdded') }}
                  </div>
                </div>
              </div>
            </div>

            <!-- Step 3: Generated Specification Description -->
            <div v-if="specForm.templateId" class="relative overflow-hidden rounded-lg bg-white border border-red-200 p-3 shadow-sm">
              <div class="relative">
                <div class="flex items-center gap-2 mb-2">
                  <span class="w-6 h-6 bg-red-100 rounded-md flex items-center justify-center">
                    <svg class="w-4 h-4 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M3 5h12M9 3v2m1.048 9.5A18.022 18.022 0 016.412 9m6.088 9h7M11 21l5-10 5 10M12.751 5C11.783 10.77 8.07 15.61 3 18.129"/>
                    </svg>
                  </span>
                  <span class="text-[10px] font-bold text-red-600 uppercase tracking-wide">{{ t('app.specificationDescription') }}</span>
                </div>
                <div class="text-xs text-slate-700 leading-relaxed pl-8">
                  {{ naturalLanguageRule }}
                </div>
                <div class="mt-2 pt-2 border-t border-slate-200 flex items-center gap-2">
                  <span class="text-[10px] font-bold text-slate-500 uppercase tracking-wide">{{ t('app.formulaPreview') }}</span>
                  <span class="px-1.5 py-0.5 bg-slate-100 rounded text-[10px] font-bold text-slate-600 uppercase">{{ specFormulaKind }}</span>
                  <code class="flex-1 text-[10px] bg-slate-100 text-slate-700 px-2 py-1 rounded font-mono overflow-x-auto">
                    {{ specForm.formula }}
                  </code>
                </div>
              </div>
            </div>

            <!-- Create Button -->
            <button
              @click="createSpecification"
              data-testid="spec-create"
              :disabled="!specForm.templateId || creatingSpecification"
              class="w-full py-2.5 bg-red-500 hover:bg-red-600 disabled:bg-slate-300 text-white rounded-lg text-xs font-bold uppercase tracking-wider transition-all shadow-md hover:shadow-lg hover:scale-[1.02] active:scale-[0.98] disabled:hover:scale-100 flex items-center justify-center gap-1.5 disabled:cursor-not-allowed"
            >
              <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z"/>
              </svg>
              {{ creatingSpecification ? t('app.saving') : t('app.createSpecification') }}
            </button>
          </div>
        </div>
      </details>


    </div>

  </aside>

  <!-- Specification Condition Dialog -->
  <div
    v-if="showSpecDialog"
    data-testid="spec-condition-dialog"
    class="fixed inset-0 bg-slate-900/60 backdrop-blur-sm flex items-center justify-center z-50"
    @click="closeSpecDialog"
    @keydown="handleSpecDialogKeydown"
  >
    <div
      :ref="setSpecDialogRef"
      class="bg-white rounded-2xl w-full max-w-md shadow-2xl transform transition-all overflow-hidden"
      role="dialog"
      aria-modal="true"
      aria-labelledby="spec-condition-dialog-title"
      tabindex="-1"
      @click.stop
    >
      <!-- Header with light background -->
      <div class="relative bg-slate-100 border-b border-slate-200 p-6">
        <div class="absolute top-0 right-0 w-32 h-32 bg-slate-200/50 rounded-full -translate-y-1/2 translate-x-1/2"></div>
        <div class="absolute bottom-0 left-0 w-24 h-24 bg-slate-200/50 rounded-full translate-y-1/2 -translate-x-1/2"></div>
        
        <div class="relative flex items-center justify-between">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 bg-white shadow-sm rounded-xl flex items-center justify-center">
              <svg class="w-6 h-6 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z"/>
              </svg>
            </div>
            <div>
              <h3 id="spec-condition-dialog-title" class="text-xl font-bold text-black">
                {{ editingConditionIndex >= 0 ? t('app.editCondition') : t('app.addConditionTitle') }}
              </h3>
              <p class="text-sm text-slate-600">{{ t('app.configureSpecification') }}</p>
            </div>
          </div>
          <button
            type="button"
            :aria-label="t('app.close')"
            @click="closeSpecDialog"
            class="w-10 h-10 bg-white hover:bg-slate-50 rounded-lg flex items-center justify-center transition-all hover:rotate-90 shadow-sm"
          >
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12"/>
            </svg>
          </button>
        </div>
      </div>

      <!-- Content Body -->
      <div class="p-6 space-y-6">
        <!-- Device Selection -->
        <div class="space-y-2">
          <div class="flex items-center gap-2">
            <span class="text-sm font-bold text-black">{{ t('app.deviceSelection') }}</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="editingConditionData.deviceId"
              data-testid="spec-condition-device"
              @change="editingConditionData.key = ''"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              :class="deviceNodes.length === 0 ? 'cursor-not-allowed opacity-70' : 'cursor-pointer'"
              :disabled="deviceNodes.length === 0"
            >
              <option v-if="deviceNodes.length === 0" value="">{{ t('app.none') }}</option>
              <option v-else value="" hidden>{{ t('app.selectDevicePlaceholder') }}</option>
              <option
                v-for="device in deviceNodes"
                :key="device.id"
                :value="device.id"
              >
                {{ device.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Type -->
        <div class="space-y-2" v-if="editingConditionData.deviceId">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M7 7h.01M7 3h5c.512 0 1.024.195 1.414.586l7 7a2 2 0 010 2.828l-7 7a2 2 0 01-2.828 0l-7-7A2 2 0 013 12V7a4 4 0 014-4z"/>
            </svg>
            <span class="text-sm font-bold text-black">{{ t('app.type') }}</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="editingConditionData.targetType"
              data-testid="spec-condition-type"
              @change="handleTargetTypeChange"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
            >
              <option v-if="localizedTargetTypes.length === 0" value="">{{ t('app.none') }}</option>
              <option v-else value="" hidden>{{ t('app.type') }}</option>
              <option v-for="type in localizedTargetTypes" :key="type.value" :value="type.value">
                {{ type.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Property -->
        <div class="space-y-2" v-if="editingConditionData.targetType !== 'state' && editingConditionData.deviceId">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 7a2 2 0 012 2m4 0a6 6 0 01-7.743 5.743L11 17H9v2H7v2H4a1 1 0 01-1-1v-2.586a1 1 0 01.293-.707l5.964-5.964A6 6 0 1121 9z"/>
            </svg>
            <span class="text-sm font-bold text-black">{{ t('app.property') }}</span>
          </div>
          <div class="relative w-full">
            <select
              v-model="conditionKeySelection"
              data-testid="spec-condition-key"
              class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              :class="availableKeys.length === 0 ? 'cursor-not-allowed opacity-70' : 'cursor-pointer'"
              :disabled="availableKeys.length === 0"
            >
              <option v-if="availableKeys.length === 0" value="">{{ t('app.none') }}</option>
              <option v-else value="" hidden>{{ t('app.property') }}</option>
              <option
                v-for="key in availableKeys"
                :key="key.value"
                :value="key.value"
              >
                {{ key.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Condition Details -->
        <div class="space-y-2" v-if="showRelationAndValue">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 6V4m0 2a2 2 0 100 4m0-4a2 2 0 110 4m-6 8a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4m6 6v10m6-2a2 2 0 100-4m0 4a2 2 0 110-4m0 4v2m0-6V4"/>
            </svg>
            <span class="text-sm font-bold text-black">{{ t('app.conditionDetails') }}</span>
          </div>
          <div class="flex gap-2 w-full">
            <!-- Operator -->
            <div class="relative w-1/4">
              <select
                v-model="editingConditionData.relation"
                data-testid="spec-condition-relation"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-2 py-2.5 text-sm text-center font-bold text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              >
                <option v-for="op in filteredRelationOperators" :key="op.value" :value="op.value">
                  {{ op.label }}
                </option>
              </select>
            </div>
            <!-- Value -->
            <div class="relative w-3/4">
              <select
                v-if="conditionValueOptions.length > 0 && isSpecSetRelation"
                v-model="editingConditionValueList"
                data-testid="spec-condition-value"
                multiple
                size="4"
                class="w-full min-h-[7.5rem] bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none cursor-pointer"
              >
                <option v-for="val in conditionValueOptions" :key="val" :value="val">
                  {{ val }}
                </option>
              </select>
              <select
                v-else-if="conditionValueOptions.length > 0"
                v-model="editingConditionData.value"
                data-testid="spec-condition-value"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black focus:border-red-400 focus:outline-none appearance-none cursor-pointer"
              >
                <option value="" hidden>{{ t('app.value') }}</option>
                <option v-for="val in conditionValueOptions" :key="val" :value="val">
                  {{ val }}
                </option>
              </select>
              <input
                v-else
                v-model="editingConditionData.value"
                data-testid="spec-condition-value"
                class="w-full bg-white border-2 border-slate-300 rounded-lg px-3 py-2.5 text-sm text-black placeholder:text-slate-400 focus:border-red-400 focus:outline-none"
                :placeholder="t('app.enterValuePlaceholder')"
              />
            </div>
          </div>
        </div>

        <!-- Preview -->
        <div class="space-y-2">
          <div class="flex items-center gap-2">
            <svg class="w-5 h-5 text-black" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 12a3 3 0 11-6 0 3 3 0 016 0z"/>
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M2.458 12C3.732 7.943 7.523 5 12 5c4.478 0 8.268 2.943 9.542 7-1.274 4.057-5.064 7-9.542 7-4.477 0-8.268-2.943-9.542-7z"/>
            </svg>
            <span class="text-xs font-bold uppercase text-black tracking-wider">{{ t('app.preview') }}</span>
          </div>
          <div class="font-mono text-xs bg-slate-100 rounded-lg px-3 py-2.5 border border-slate-300 text-black break-all w-full">
            <span class="text-red-600 font-bold">{{ getDeviceLabel(editingConditionData.deviceId || t('app.device')) }}</span>
            <template v-if="editingConditionData.targetType !== 'state' && editingConditionData.key">
              <span class="text-slate-400">.</span>
              <span class="text-red-600 font-bold">{{ editingConditionData.key }}</span>
            </template>
            <template v-if="showRelationAndValue">
              <span class="text-slate-500 mx-1">{{ getRelationLabel(editingConditionData.relation || '=') }}</span>
              <span class="text-black">"{{ editingConditionData.value || t('app.value') }}"</span>
            </template>
          </div>
        </div>
      </div>

      <!-- Footer Actions -->
      <div class="bg-slate-100 px-6 py-4 flex justify-end gap-3 border-t border-slate-200">
        <button
          @click="closeSpecDialog"
          class="px-5 py-2.5 text-sm font-bold text-black bg-white border-2 border-slate-300 rounded-lg hover:bg-slate-50 hover:border-slate-400 transition-all"
        >
          {{ t('app.cancel') }}
        </button>
        <button
          @click="saveCondition"
          data-testid="spec-condition-save"
          class="px-5 py-2.5 text-sm font-bold text-black bg-gradient-to-r from-red-500 to-red-600 rounded-lg hover:from-red-600 hover:to-red-700 transition-all shadow-md flex items-center gap-2 disabled:opacity-50 disabled:cursor-not-allowed"
          :disabled="!editingConditionData.deviceId || !editingConditionData.targetType || (editingConditionData.targetType !== 'state' && !editingConditionData.key)"
        >
          <svg class="w-4 h-4" :fill="editingConditionIndex >= 0 ? 'currentColor' : 'none'" stroke="currentColor" viewBox="0 0 24 24">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" :d="editingConditionIndex >= 0 ? 'M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z' : 'M12 4v16m8-8H4'"/>
          </svg>
          {{ editingConditionIndex >= 0 ? t('app.update') : t('app.add') }}
        </button>
      </div>
    </div>
  </div>

  <Teleport to="body">
    <div
      v-if="activeTemplatePreview"
      class="template-preview"
      :style="templatePreviewStyle"
      :data-testid="`template-preview-${getTemplateKey(activeTemplatePreview)}`"
      @click.stop
    >
      <div class="template-preview__header">
        <div class="min-w-0">
          <p class="template-preview__eyebrow">{{ t('app.templateDetails') }}</p>
          <h5 class="template-preview__title truncate" :title="getTemplateName(activeTemplatePreview)">{{ getTemplateName(activeTemplatePreview) }}</h5>
        </div>
        <button
          type="button"
          class="template-preview__close"
          :aria-label="t('app.close')"
          :title="t('app.close')"
          @click.stop="closeTemplatePreview"
        >
          <span class="material-symbols-outlined text-sm">close</span>
        </button>
      </div>

      <p class="template-preview__description" :title="getTemplateDescription(activeTemplatePreview)">
        {{ getTemplateDescription(activeTemplatePreview) }}
      </p>

      <div class="template-preview__meta">
        <div>
          <span>{{ t('app.initState') }}</span>
          <strong :title="getTemplateInitState(activeTemplatePreview)">{{ getTemplateInitState(activeTemplatePreview) }}</strong>
        </div>
        <div>
          <span>{{ t('app.transition') }}</span>
          <strong>{{ getTemplateTransitionCount(activeTemplatePreview) }}</strong>
        </div>
      </div>

      <div class="template-preview__sections">
        <div
          v-for="section in getTemplatePreviewSections(activeTemplatePreview)"
          :key="section.key"
          class="template-preview__section"
        >
          <span class="template-preview__section-label">{{ section.label }}</span>
          <div class="template-preview__chips">
            <span v-if="section.items.length === 0" class="template-preview__empty">{{ t('app.none') }}</span>
            <template v-else>
              <span
                v-for="item in previewItems(section.items)"
                :key="`${section.key}-${item}`"
                class="template-preview__chip"
                :title="item"
              >
                {{ item }}
              </span>
              <span v-if="section.items.length > previewItems(section.items).length" class="template-preview__chip">
                +{{ section.items.length - previewItems(section.items).length }}
              </span>
            </template>
          </div>
        </div>
      </div>
    </div>
  </Teleport>

  <!-- Delete Confirmation Dialog -->
  <div v-if="showDeleteConfirmDialog" class="fixed inset-0 bg-slate-900/50 backdrop-blur-sm flex items-center justify-center z-50" @click="closeTemplateDeleteConfirm()">
    <div class="bg-white rounded-lg p-6 w-full max-w-md shadow-2xl border border-slate-200 transform transition-all" @click.stop>
      <!-- 警告头部 -->
      <div class="relative -mx-6 -top-6 mb-6 bg-red-600 rounded-t-2xl p-6 text-center">
        <div class="relative">
          <div class="w-16 h-16 mx-auto bg-white/20 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-white text-3xl">warning</span>
          </div>
          <p class="text-base text-white/90">{{ t('app.youAreAboutToDelete') }}</p>
        </div>
      </div>

      <div v-if="templateToDelete" class="text-center mb-6">
        <div class="inline-flex items-center gap-3 px-6 py-3 bg-red-50 rounded-xl border-2 border-red-200">
          <span class="material-symbols-outlined text-red-500 text-xl">inventory_2</span>
          <p class="text-lg font-bold text-red-600">{{ templateToDelete.manifest.Name }}</p>
        </div>
        <p class="text-xs text-slate-400 mt-3">{{ t('app.actionCannotBeUndone') }}</p>
      </div>

      <div
        v-if="templateDeletePreview && !templateDeletePreview.canDelete"
        class="mb-5 rounded-lg border border-amber-300 bg-amber-50 p-3 text-left"
      >
        <p class="text-sm font-bold text-amber-800">{{ t('app.templateDeleteBlocked') }}</p>
        <p class="mt-1 text-xs leading-5 text-amber-700">{{ t('app.templateDeleteBlockedDetail') }}</p>
        <ul class="mt-2 space-y-1.5">
          <li
            v-for="blocker in templateDeletePreview.blockers"
            :key="blocker.itemId"
            class="flex items-center gap-2 rounded border border-amber-200 bg-white px-2 py-1.5 text-xs text-slate-700"
          >
            <span class="material-symbols-outlined text-sm text-amber-600" aria-hidden="true">devices</span>
            <span class="min-w-0 truncate" :title="blocker.itemLabel">{{ blocker.itemLabel }}</span>
          </li>
        </ul>
      </div>

      <p v-else-if="templateDeletePreview" class="mb-5 text-center text-xs leading-5 text-slate-600">
        {{ t('app.templateDeleteNoReferences') }}
      </p>

      <div class="flex justify-center gap-3">
        <button
          :disabled="isDeletingTemplate"
          @click="closeTemplateDeleteConfirm()"
          class="px-6 py-2.5 text-sm font-semibold text-slate-600 bg-white border-2 border-slate-200 rounded-xl hover:bg-slate-50 hover:border-slate-300 transition-all"
        >
          {{ t('app.cancel') }}
        </button>
        <button
          @click="confirmDeleteTemplate"
          :disabled="isDeletingTemplate || !templateDeletePreview?.canDelete"
          class="px-6 py-2.5 text-sm font-semibold text-white bg-red-600 rounded-lg hover:bg-red-500 transition-all shadow-md flex items-center gap-2 disabled:cursor-not-allowed disabled:bg-slate-300 disabled:shadow-none"
        >
          <span class="material-symbols-outlined text-sm">delete</span>
          {{ isDeletingTemplate ? t('app.deleting') : t('app.deleteTemplate') }}
        </button>
      </div>
    </div>
  </div>

  <!-- Reset Default Templates Confirmation Dialog -->
  <div
    v-if="showResetDefaultsConfirmDialog"
    class="fixed inset-0 z-50 flex items-center justify-center bg-slate-900/50 p-4 backdrop-blur-sm"
    @click="closeResetDefaultsConfirm()"
  >
    <div
      class="template-reset-dialog w-full max-w-md rounded-2xl border p-5 shadow-2xl"
      role="dialog"
      aria-modal="true"
      aria-labelledby="reset-default-templates-title"
      @click.stop
    >
      <div class="mb-4 flex items-start gap-3">
        <div class="template-reset-dialog__icon">
          <span class="material-symbols-outlined" aria-hidden="true">restart_alt</span>
        </div>
        <div class="min-w-0">
          <h3 id="reset-default-templates-title" class="text-base font-extrabold">
            {{ t('app.resetDefaultTemplatesTitle') }}
          </h3>
          <p class="mt-1 text-xs leading-relaxed">
            {{ t('app.resetDefaultTemplatesMessage') }}
          </p>
        </div>
      </div>

      <template v-if="defaultTemplateResetPreview">
        <div class="template-reset-dialog__notice rounded-lg border px-3 py-2 text-xs leading-relaxed">
          {{ t('app.resetDefaultTemplatesImpactSummary', {
            types: defaultTemplateResetPreview.templateChanges.length,
            devices: defaultTemplateResetPreview.affectedDevices.length,
            variables: defaultTemplateResetPreview.environmentChanges.length
          }) }}
        </div>

        <div class="mt-3 max-h-44 overflow-y-auto border-y border-slate-200 py-1 dark:border-slate-700">
          <div
            v-for="change in defaultTemplateResetPreview.templateChanges"
            :key="`${change.changeType}:${change.templateName}`"
            class="flex items-start justify-between gap-3 py-1.5 text-xs"
          >
            <span class="min-w-0 break-words font-semibold">{{ change.templateName }}</span>
            <span class="shrink-0 text-right text-slate-500 dark:text-slate-400">
              {{ defaultTemplateResetChangeLabel(change.changeType) }}
              <span v-if="change.semanticsChanged"> · {{ t('app.templateSemanticsChanged') }}</span>
            </span>
          </div>
        </div>

        <div v-if="defaultTemplateResetPreview.affectedDevices.length" class="mt-3 text-xs">
          <div class="font-bold">{{ t('app.devicesUsingChangedTemplates') }}</div>
          <div class="mt-1 max-h-20 overflow-y-auto text-slate-600 dark:text-slate-300">
            <div
              v-for="device in defaultTemplateResetPreview.affectedDevices"
              :key="device.deviceId"
              class="break-words py-0.5"
            >
              {{ device.deviceLabel }} · {{ device.templateName }}
            </div>
          </div>
        </div>

        <div v-if="defaultTemplateResetPreview.environmentChanges.length" class="mt-3 text-xs">
          <span class="font-bold">{{ t('app.environmentVariablesWillChange', {
            count: defaultTemplateResetPreview.environmentChanges.length
          }) }}</span>
          <span class="ml-1 break-words text-slate-600 dark:text-slate-300">
            {{ defaultTemplateResetPreview.environmentChanges.map(change => change.name).join(', ') }}
          </span>
        </div>

        <div
          v-if="defaultTemplateResetPreview.blockers.length"
          class="mt-3 border-l-2 border-red-500 pl-3 text-xs text-red-700 dark:text-red-300"
          role="alert"
        >
          <div class="font-bold">{{ t('app.defaultTemplateResetBlocked') }}</div>
          <div
            v-for="(blocker, index) in defaultTemplateResetPreview.blockers"
            :key="`${blocker.itemLabel}:${index}`"
            class="mt-1 break-words"
          >
            <div>
              <strong>{{ blocker.itemLabel }}</strong>: {{ defaultTemplateResetBlockerReason(blocker.reasonCode) }}
            </div>
            <details class="mt-1 text-[11px] text-red-700/80 dark:text-red-300/80">
              <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
              <code class="mt-1 block whitespace-pre-wrap break-words rounded bg-red-100/70 px-2 py-1 dark:bg-red-950/50">{{ blocker.reason }}</code>
            </details>
          </div>
        </div>

        <p class="mt-3 text-xs leading-relaxed text-slate-600 dark:text-slate-300">
          {{ t('app.resetDefaultTemplatesNotice') }}
        </p>
      </template>

      <div class="mt-5 flex justify-end gap-3">
        <button
          type="button"
          class="template-reset-dialog__btn secondary"
          :disabled="isResettingDefaultTemplates"
          @click="closeResetDefaultsConfirm()"
        >
          {{ t('app.cancel') }}
        </button>
        <button
          type="button"
          class="template-reset-dialog__btn primary"
          :disabled="isResettingDefaultTemplates || !defaultTemplateResetPreview?.canApply"
          @click="confirmResetDefaultTemplates"
        >
          <span v-if="isResettingDefaultTemplates" class="template-reset-dialog__spinner" aria-hidden="true"></span>
          <span v-else class="material-symbols-outlined text-sm" aria-hidden="true">restart_alt</span>
          {{ isResettingDefaultTemplates ? t('app.resetting') : t('app.resetDefaultTemplates') }}
        </button>
      </div>
    </div>
  </div>
</template>

<style scoped>
/* Modern panel effect */
.modern-panel {
  background: var(--board-panel-bg, linear-gradient(180deg, rgba(255, 255, 255, 0.95) 0%, rgba(248, 250, 252, 0.95) 100%));
  backdrop-filter: blur(20px);
  border: 1px solid var(--board-border, rgba(255, 255, 255, 0.3));
}

/* Glass panel effect */
.glass-panel {
  background: var(--board-panel-bg, rgba(255, 255, 255, 0.7));
  backdrop-filter: blur(16px);
  border: 1px solid var(--board-border, rgba(226, 232, 240, 0.8));
}

/* Custom scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 6px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: rgba(0, 0, 0, 0.02);
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: #cbd5e1;
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb:hover {
  background: #94a3b8;
}

/* Utility classes */
.text-primary {
  color: #8B5CF6;
}

.text-secondary {
  color: #C026D3;
}

.bg-online {
  background-color: #10B981;
}

.bg-offline {
  background-color: #EF4444;
}

/* Material Symbols font */
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
  font-variation-settings: 'FILL' 0, 'wght' 400, 'GRAD' 0, 'opsz' 24;
}

/* Details/Summary styling */
details > summary {
  list-style: none;
}

details > summary::-webkit-details-marker {
  display: none;
}

.control-mode-tabs {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 0.35rem;
  border: 1px solid var(--board-border, #e2e8f0);
  border-radius: 0.75rem;
  background: var(--board-control-bg, #f1f5f9);
  padding: 0.25rem;
}

.control-mode-tabs button {
  min-width: 0;
  border: 0;
  border-radius: 0.55rem;
  padding: 0.45rem 0.35rem;
  color: var(--board-text-muted, #64748b);
  font-size: 0.62rem;
  font-weight: 800;
  line-height: 1.1;
  transition: background 0.18s ease, color 0.18s ease, box-shadow 0.18s ease;
}

.control-mode-tabs button.active {
  background: #a855f7;
  color: #ffffff;
  box-shadow: 0 8px 18px rgba(168, 85, 247, 0.22);
}

.device-preview-box {
  border: 1px solid var(--board-border, #e2e8f0);
  border-radius: 0.75rem;
  background: color-mix(in srgb, var(--board-card-bg, #ffffff) 88%, transparent);
  padding: 0.65rem;
}

.device-import-help {
  position: relative;
  display: flex;
  min-width: 0;
  align-items: center;
  gap: 0.45rem;
  border: 1px solid color-mix(in srgb, var(--iot-color-accent, #8b5cf6) 24%, var(--board-border, #e2e8f0));
  border-radius: 0.65rem;
  background: color-mix(in srgb, var(--board-control-bg, #f8fafc) 86%, var(--iot-color-accent, #8b5cf6) 8%);
  color: var(--board-text-muted, #64748b);
  padding: 0.55rem 0.65rem;
  font-size: 0.68rem;
  font-weight: 700;
  line-height: 1.2;
}

.device-import-help__trigger {
  position: relative;
  display: inline-flex;
  width: 1.45rem;
  height: 1.45rem;
  flex: 0 0 auto;
  align-items: center;
  justify-content: center;
  border: 1px solid color-mix(in srgb, var(--iot-color-accent, #8b5cf6) 28%, var(--board-border, #e2e8f0));
  border-radius: 999px;
  background: var(--board-card-bg, #ffffff);
  color: var(--iot-color-accent, #7c3aed);
  transition: background 0.15s ease, border-color 0.15s ease, color 0.15s ease;
}

.device-import-help__trigger:hover,
.device-import-help__trigger:focus-visible {
  border-color: var(--iot-color-accent, #7c3aed);
  background: color-mix(in srgb, var(--board-card-bg, #ffffff) 86%, var(--iot-color-accent, #7c3aed) 14%);
  outline: none;
}

.device-import-help__tooltip {
  position: absolute;
  right: 0;
  top: calc(100% + 0.5rem);
  z-index: 40;
  width: min(18rem, calc(100vw - 2rem));
  max-width: min(18rem, calc(var(--control-panel-width, 20rem) - 2.5rem));
  border: 1px solid var(--board-border, #e2e8f0);
  border-radius: 0.65rem;
  background: var(--board-card-bg, #ffffff);
  box-shadow: var(--shadow-elevated, 0 16px 40px rgba(15, 23, 42, 0.18));
  color: var(--board-text, #0f172a);
  font-size: 0.7rem;
  font-weight: 650;
  line-height: 1.45;
  opacity: 0;
  padding: 0.7rem 0.8rem;
  pointer-events: none;
  text-align: left;
  transform: translateY(-0.2rem);
  transition: opacity 0.15s ease, transform 0.15s ease;
  white-space: normal;
}

.device-import-help__trigger:hover .device-import-help__tooltip,
.device-import-help__trigger:focus-visible .device-import-help__tooltip {
  opacity: 1;
  transform: translateY(0);
}

.device-preview-box__header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 0.5rem;
  color: var(--board-text-muted, #64748b);
  font-size: 0.62rem;
  font-weight: 800;
  letter-spacing: 0.03em;
  text-transform: uppercase;
}

.device-preview-box__header strong {
  border-radius: 999px;
  background: color-mix(in srgb, #a855f7 14%, var(--board-control-bg, #f1f5f9));
  color: var(--board-text, #0f172a);
  padding: 0.1rem 0.45rem;
}

.device-preview-list {
  display: grid;
  gap: 0.35rem;
  margin-top: 0.5rem;
}

.device-preview-list--scroll {
  max-height: 18rem;
  overflow-y: auto;
  padding-right: 0.15rem;
}

.device-preview-row {
  display: grid;
  grid-template-columns: minmax(0, 1fr) minmax(0, 0.9fr);
  gap: 0.45rem;
  align-items: center;
  border: 1px solid color-mix(in srgb, var(--board-border, #e2e8f0) 70%, transparent);
  border-radius: 0.55rem;
  background: var(--board-control-bg, #f8fafc);
  padding: 0.4rem 0.5rem;
}

.device-preview-row span {
  min-width: 0;
  color: var(--board-text, #0f172a);
  font-size: 0.7rem;
  font-weight: 800;
}

.device-preview-row small {
  min-width: 0;
  color: var(--board-text-muted, #64748b);
  font-size: 0.62rem;
  font-weight: 700;
  text-align: right;
}

.device-preview-row.has-error {
  border-color: color-mix(in srgb, #ef4444 38%, var(--board-border, #e2e8f0));
  background: color-mix(in srgb, #ef4444 9%, var(--board-card-bg, #ffffff));
}

.device-preview-row.has-error small {
  color: #dc2626;
}

.device-preview-row.has-warning {
  border-color: color-mix(in srgb, #f59e0b 42%, var(--board-border, #e2e8f0));
  background: color-mix(in srgb, #f59e0b 11%, var(--board-card-bg, #ffffff));
}

.device-preview-row.has-warning small {
  color: color-mix(in srgb, #d97706 88%, var(--board-text, #0f172a));
}

.device-preview-more,
.device-preview-empty {
  margin-top: 0.45rem;
  color: var(--board-text-muted, #64748b);
  font-size: 0.65rem;
  font-weight: 700;
  text-align: center;
}

.device-runtime-box {
  background: color-mix(in srgb, var(--board-card-bg, #ffffff) 88%, transparent);
  border-color: color-mix(in srgb, #a855f7 26%, var(--board-border, #e2e8f0));
  color: var(--board-text, #0f172a);
}

.device-runtime-box summary,
.device-runtime-box p,
.device-runtime-box span {
  color: inherit;
}

.device-runtime-box input,
.device-runtime-box select {
  background: var(--board-card-bg, #ffffff);
  border-color: var(--board-border, #e2e8f0);
  color: var(--board-text, #0f172a);
}

.device-runtime-box input::placeholder {
  color: var(--board-text-muted, #94a3b8);
}

.device-runtime-box .text-slate-400,
.device-runtime-box .text-slate-500,
.device-runtime-box .text-slate-600 {
  color: var(--board-text-muted, #64748b);
}

.template-group[open] .template-group__chevron {
  transform: rotate(180deg);
}

.template-group {
  position: relative;
  overflow: visible;
  background: color-mix(in srgb, var(--board-card-bg, #ffffff) 84%, transparent);
  border-color: var(--board-border, #e2e8f0);
}

.template-group__summary {
  color: var(--board-text, #0f172a);
  border-radius: 0.5rem;
}

.template-group__summary:hover {
  background: color-mix(in srgb, #f59e0b 13%, var(--board-card-bg, #ffffff));
}

.template-group__label,
.template-group__chevron {
  color: var(--board-text-muted, #64748b);
}

.template-group__count {
  background: color-mix(in srgb, #f59e0b 16%, var(--board-control-bg, #f1f5f9));
  color: var(--board-text, #0f172a);
}

.template-group__grid {
  overflow: visible;
}

.template-group__empty {
  color: var(--board-text-muted, #64748b);
  background: color-mix(in srgb, var(--board-card-bg, #ffffff) 78%, transparent);
  border-color: var(--board-border, #e2e8f0);
}

.template-reset-dialog {
  background: var(--board-panel-bg, #ffffff);
  border-color: var(--board-border, rgba(226, 232, 240, 0.9));
  color: var(--board-text, #0f172a);
}

.template-reset-dialog__icon {
  display: grid;
  width: 2.75rem;
  height: 2.75rem;
  flex: 0 0 auto;
  place-items: center;
  border-radius: 0.9rem;
  background: color-mix(in srgb, #f97316 16%, var(--board-panel-bg, #ffffff));
  color: #ea580c;
}

.template-reset-dialog p {
  color: var(--board-text-muted, #64748b);
}

.template-reset-dialog__notice {
  background: color-mix(in srgb, #f97316 8%, var(--board-panel-bg, #ffffff));
  border-color: color-mix(in srgb, #f97316 28%, var(--board-border, #e2e8f0));
  color: var(--board-text, #334155);
}

.template-reset-dialog__btn {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 0.35rem;
  min-height: 2.35rem;
  padding: 0 0.95rem;
  border-radius: 0.75rem;
  font-size: 0.8rem;
  font-weight: 800;
  transition: opacity 0.18s ease, transform 0.18s ease, background 0.18s ease;
}

.template-reset-dialog__btn:not(:disabled):active {
  transform: scale(0.98);
}

.template-reset-dialog__btn.secondary {
  border: 1px solid var(--board-border, #cbd5e1);
  background: var(--board-control-bg, #f8fafc);
  color: var(--board-text-muted, #475569);
}

.template-reset-dialog__btn.primary {
  border: 1px solid transparent;
  background: #f97316;
  color: #ffffff;
  box-shadow: 0 10px 20px rgba(249, 115, 22, 0.22);
}

.template-reset-dialog__btn:disabled {
  cursor: not-allowed;
  opacity: 0.6;
}

.template-reset-dialog__spinner {
  width: 0.9rem;
  height: 0.9rem;
  border: 2px solid rgba(255, 255, 255, 0.38);
  border-top-color: #ffffff;
  border-radius: 999px;
  animation: template-reset-spin 0.8s linear infinite;
}

@keyframes template-reset-spin {
  to { transform: rotate(360deg); }
}

.template-card {
  z-index: 0;
  min-height: 5.15rem;
  background: var(--board-card-bg, #ffffff);
  border-color: var(--board-border, #e2e8f0);
  color: var(--board-text, #0f172a);
  cursor: pointer;
}

.template-card[draggable="true"] {
  user-select: none;
}

.template-card[draggable="true"]:active {
  cursor: grabbing;
}

.template-card:hover,
.template-card:focus-visible,
.template-card--active {
  z-index: 30;
  border-color: color-mix(in srgb, #f59e0b 58%, var(--board-border, #e2e8f0));
  box-shadow: 0 12px 28px rgba(15, 23, 42, 0.16);
  outline: none;
}

.template-card__icon {
  background: color-mix(in srgb, #f59e0b 13%, var(--board-control-bg, #f1f5f9));
}

.template-card:hover .template-card__icon,
.template-card--active .template-card__icon {
  background: color-mix(in srgb, #f59e0b 22%, var(--board-control-bg, #f1f5f9));
}

.template-card__title {
  color: var(--board-text, #0f172a);
}

.template-card:hover .template-card__title,
.template-card--active .template-card__title {
  color: color-mix(in srgb, #f59e0b 78%, var(--board-text, #0f172a));
}

.template-card__stats {
  color: var(--board-text-muted, #64748b);
}

.template-card__drag-cue {
  flex: 0 0 auto;
  color: var(--board-text-muted, #64748b);
  font-size: 0.9rem;
  line-height: 1;
  opacity: 0.72;
}

.template-card:hover .template-card__drag-cue,
.template-card--active .template-card__drag-cue {
  color: color-mix(in srgb, #f59e0b 85%, var(--board-text, #0f172a));
  opacity: 1;
}

.template-card__pill {
  background: var(--board-control-bg, #f1f5f9);
  color: var(--board-text-muted, #64748b);
}

.template-card__actions {
  border-color: var(--board-border, #e2e8f0);
}

.template-card__action {
  color: var(--board-text-muted, #64748b);
}

.template-card__action:hover {
  color: color-mix(in srgb, #f59e0b 82%, var(--board-text, #0f172a));
  background: color-mix(in srgb, #f59e0b 15%, var(--board-control-bg, #f1f5f9));
}

.template-card__action--danger:hover {
  color: #ef4444;
  background: color-mix(in srgb, #ef4444 14%, var(--board-control-bg, #f1f5f9));
}

.template-preview {
  --template-preview-card-bg: var(--board-card-bg, var(--surface-elevated, #ffffff));
  --template-preview-control-bg: var(--board-control-bg, var(--surface-control, #f1f5f9));
  --template-preview-border: var(--board-border, var(--border, #e2e8f0));
  --template-preview-text: var(--board-text, var(--text, #0f172a));
  --template-preview-muted: var(--board-text-muted, var(--text-muted, #64748b));

  position: fixed;
  z-index: 45;
  box-sizing: border-box;
  overflow-y: auto;
  overscroll-behavior: contain;
  padding: 0.75rem;
  border: 1px solid var(--template-preview-border);
  border-radius: 0.75rem;
  background: color-mix(in srgb, var(--template-preview-card-bg) 96%, transparent);
  color: var(--template-preview-text);
  backdrop-filter: blur(16px);
  box-shadow: 0 22px 55px rgba(15, 23, 42, 0.24);
}

.template-preview__header {
  display: flex;
  align-items: flex-start;
  justify-content: space-between;
  gap: 0.75rem;
}

.template-preview__eyebrow {
  margin: 0;
  color: var(--template-preview-muted);
  font-size: 0.62rem;
  font-weight: 800;
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

.template-preview__title {
  margin: 0.1rem 0 0;
  color: var(--template-preview-text);
  font-size: 0.82rem;
  font-weight: 800;
}

.template-preview__close {
  display: inline-flex;
  width: 1.55rem;
  height: 1.55rem;
  flex: 0 0 auto;
  align-items: center;
  justify-content: center;
  border: 1px solid var(--template-preview-border);
  border-radius: 0.45rem;
  background: var(--template-preview-control-bg);
  color: var(--template-preview-muted);
}

.template-preview__close:hover {
  color: var(--template-preview-text);
}

.template-preview__description {
  display: -webkit-box;
  margin: 0.55rem 0 0;
  overflow: hidden;
  color: var(--template-preview-muted);
  font-size: 0.7rem;
  line-height: 1.45;
  -webkit-box-orient: vertical;
  -webkit-line-clamp: 3;
}

.template-preview__meta {
  display: grid;
  grid-template-columns: minmax(0, 1fr) minmax(0, 0.75fr);
  gap: 0.45rem;
  margin-top: 0.65rem;
}

.template-preview__meta > div {
  min-width: 0;
  border: 1px solid var(--template-preview-border);
  border-radius: 0.55rem;
  background: var(--template-preview-control-bg);
  padding: 0.45rem;
}

.template-preview__meta span,
.template-preview__section-label {
  display: block;
  color: var(--template-preview-muted);
  font-size: 0.58rem;
  font-weight: 800;
  letter-spacing: 0.04em;
  text-transform: uppercase;
}

.template-preview__meta strong {
  display: block;
  min-width: 0;
  margin-top: 0.15rem;
  overflow: hidden;
  color: var(--template-preview-text);
  font-size: 0.72rem;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.template-preview__sections {
  display: grid;
  gap: 0.5rem;
  margin-top: 0.65rem;
}

.template-preview__chips {
  display: flex;
  flex-wrap: wrap;
  gap: 0.3rem;
  margin-top: 0.25rem;
}

.template-preview__chip,
.template-preview__empty {
  max-width: 100%;
  overflow: hidden;
  border-radius: 999px;
  padding: 0.18rem 0.45rem;
  background: var(--template-preview-control-bg);
  color: var(--template-preview-text);
  font-size: 0.65rem;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.template-preview__empty {
  color: var(--template-preview-muted);
}

/* Animation utilities */
@keyframes pulse-glow {
  0%, 100% {
    box-shadow: 0 0 0 0 rgba(100, 116, 139, 0.4);
  }
  50% {
    box-shadow: 0 0 0 8px rgba(100, 116, 139, 0);
  }
}

.animate-pulse-glow {
  animation: pulse-glow 2s infinite;
}

/* Text color */
.text-primary {
  color: #334155;
}

.text-secondary {
  color: #475569;
}

/* Input focus animation */
input:focus,
select:focus {
  animation: focus-ring 0.3s ease-out;
}

@keyframes focus-ring {
  0% {
    box-shadow: 0 0 0 0 rgba(100, 116, 139, 0.4);
  }
  100% {
    box-shadow: 0 0 0 4px rgba(100, 116, 139, 0.1);
  }
}

/* Button hover effects */
button:not(:disabled):hover {
  transform: translateY(-1px);
}

button:not(:disabled):active {
  transform: translateY(0);
}

/* Card hover effects */
.group:hover .group-hover\:scale-105 {
  transform: scale(1.05);
}

/* Fade in animation */
@keyframes fadeIn {
  from {
    opacity: 0;
    transform: translateY(10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.fade-in {
  animation: fadeIn 0.3s ease-out;
}

/* Backdrop blur support */
@supports (-webkit-backdrop-filter: blur(20px)) {
  .backdrop-blur-sm {
    -webkit-backdrop-filter: blur(20px);
    backdrop-filter: blur(20px);
  }
}
</style>
