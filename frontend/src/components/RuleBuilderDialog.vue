<script setup lang="ts">
import { reactive, computed, watch, ref } from 'vue'
import { useI18n } from 'vue-i18n'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import type { DeviceNode } from '../types/node'
import type { DeviceManifest, DeviceTemplate } from '../types/device'
import type { RuleForm, RuleSourceItemType } from '../types/rule'
import boardApi from '../api/board'
import { duplicateRuleReasonKey, ruleSimilarityReasonKey } from '@/utils/rule'
import { REQUEST_LIMITS } from '@/constants/requestLimits'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'
import { deviceIconFor } from '@/utils/deviceIcon'
import {
  acknowledge,
  confirmChoice,
  dismissOpenConfirmation,
  notifyBlocked,
  notifySuccess
} from '@/utils/feedback'

const { t } = useI18n()

// Props
interface Props {
  modelValue: boolean
  nodes: DeviceNode[]
  deviceTemplates: any[]
}

const props = withDefaults(defineProps<Props>(), {
  modelValue: false,
  nodes: () => [],
  deviceTemplates: () => []
})

const deviceNodes = computed(() => props.nodes || [])

const resolveDeviceNode = (ref?: string | null): DeviceNode | undefined => {
  if (!ref) return undefined
  return deviceNodes.value.find((node: DeviceNode) => node.id === ref)
}

// Emits
const emit = defineEmits<{
  'update:modelValue': [value: boolean]
  'save-rule': [request: { rule: RuleForm; complete: (saved: boolean) => void }]
}>()

// Rule data
const ruleData = reactive<RuleForm>({
  id: '',
  name: '',
  sources: [],
  toId: '',
  toApi: '',
  contentDevice: '',
  content: ''
})

// Current source being added
const currentSource = reactive({
  fromId: '',  // Source board device id
  itemType: '' as '' | RuleSourceItemType,
  fromApi: '',  // API name, variable name, mode name; full-state conditions use state
  relation: '=',
  value: ''
})

interface SourceOption {
  name: string
  label?: string
  type: RuleSourceItemType
  values?: string[]
  lowerBound?: number
  upperBound?: number
}

interface ContentOption {
  name: string
  privacy: 'public' | 'private'
}

const VALUE_BASED_SOURCE_TYPES = new Set<RuleSourceItemType>(['variable', 'mode', 'state'])
const isValueBasedSourceType = (type?: RuleSourceItemType | ''): type is RuleSourceItemType =>
  Boolean(type && VALUE_BASED_SOURCE_TYPES.has(type))

// 条件选项 - 使用 NuSMV 兼容的关系运算符（label 走 i18n，符号语言无关）
const relationOptions = computed(() => [
  { label: `${t('app.relationEquals')} (=)`, value: '=' },
  { label: `${t('app.relationNotEquals')} (≠)`, value: '!=' },
  { label: `${t('app.relationGreater')} (>)`, value: '>' },
  { label: `${t('app.relationLess')} (<)`, value: '<' },
  { label: `${t('app.relationGreaterEqual')} (≥)`, value: '>=' },
  { label: `${t('app.relationLessEqual')} (≤)`, value: '<=' },
  { label: `${t('app.relationIn')} (in)`, value: 'in' },
  { label: `${t('app.relationNotIn')} (not in)`, value: 'not in' }
])

const conditionRelationOptions = computed(() => {
  const enumRelations = new Set(['=', '!=', 'in', 'not in'])
  const numericRelations = new Set(['=', '!=', '>', '<', '>=', '<=', 'in', 'not in'])

  if (currentSource.itemType === 'mode' || currentSource.itemType === 'state') {
    return relationOptions.value.filter(option => enumRelations.has(option.value))
  }
  if (currentSource.itemType === 'variable' && selectedSourceOption.value?.values?.length) {
    return relationOptions.value.filter(option => enumRelations.has(option.value))
  }
  if (currentSource.itemType === 'variable') {
    return relationOptions.value.filter(option => numericRelations.has(option.value))
  }
  return relationOptions.value
})

const resolveDeviceTemplate = (templateName: string): DeviceTemplate | undefined => {
  if (!templateName) return undefined

  const normalizedName = templateName.toLowerCase().trim()

  return props.deviceTemplates.find((t: DeviceTemplate) => {
    const tplName = t.manifest?.Name || t.name || ''
    return tplName.toLowerCase().trim() === normalizedName
  })
}

const formatTemplateModelToken = (templateName: string, value: unknown) => {
  const raw = value === null || value === undefined ? '' : String(value)
  const template = resolveDeviceTemplate(templateName)
  return template?.defaultTemplate === true
    ? formatBuiltInModelToken(raw, t)
    : raw
}

const formatCurrentSourceModelToken = (value: unknown) =>
  formatTemplateModelToken(currentSourceNode.value?.templateName || '', value)

const formatRuleSourceModelToken = (source: RuleForm['sources'][number], value: unknown) =>
  formatTemplateModelToken(resolveDeviceNode(source.fromId)?.templateName || '', value)

const formatRuleSourceName = (source: RuleForm['sources'][number]) =>
  source.itemType === 'state' ? t('app.state') : formatRuleSourceModelToken(source, source.fromApi)

const formatTargetModelToken = (value: unknown) =>
  formatTemplateModelToken(resolveDeviceNode(ruleData.toId)?.templateName || '', value)

const formatContentModelToken = (value: unknown) =>
  formatTemplateModelToken(resolveDeviceNode(ruleData.contentDevice)?.templateName || '', value)

const splitStateTuple = (stateName: string) =>
  String(stateName || '').split(';').map(part => part.trim()).filter(Boolean)

const uniqueStrings = (values: string[]) =>
  Array.from(new Set(values.filter(value => value !== '')))

const getModeValues = (manifest: DeviceManifest, modeName: string): string[] => {
  const modeIndex = (manifest.Modes || []).findIndex(mode => mode === modeName)
  if (modeIndex < 0) return []

  const values = (manifest.WorkingStates || [])
    .map(state => splitStateTuple(state.Name)[modeIndex])
    .filter(Boolean)

  return uniqueStrings(values)
}

const getDeviceApis = (templateName: string, signalOnly = false): SourceOption[] => {
  const template = resolveDeviceTemplate(templateName)

  if (template && template.manifest?.APIs) {
    return template.manifest.APIs
      .filter((api: any) => !signalOnly || api.Signal === true || api.signal === true)
      .map((api: any) => ({
        name: api.Name || api.name || '',
        type: 'api' as const
      }))
  }

  // 如果没有找到模板，返回空数组
  return []
}

// Rule variable conditions use template InternalVariables, which include both device-local variables
// and shared environment variables the device reads.
//
// An affect-only shared declaration (Reads=false) is deliberately excluded: the generator emits no
// `device.name := a_name` mirror for it, so a rule condition on it would reference a value the device
// never observes. Offering it let a user build a rule whose condition silently had no model behind it.
const getDeviceVariables = (templateName: string): SourceOption[] => {
  const template = resolveDeviceTemplate(templateName)
  const variables: SourceOption[] = []

  if (template && template.manifest?.InternalVariables) {
    template.manifest.InternalVariables.forEach((v: any) => {
      if (v.IsInside !== true && v.Reads === false) return
      if (v.Name || v.name) {
        const name = v.Name || v.name || ''
        const scope = v.IsInside === true ? t('app.internalVariable') : t('app.environmentVariable')
        variables.push({
          name,
          label: `${formatTemplateModelToken(templateName, name)} (${scope})`,
          type: 'variable' as const,
          values: Array.isArray(v.Values) ? v.Values.map((value: unknown) => String(value)) : undefined,
          lowerBound: typeof v.LowerBound === 'number' ? v.LowerBound : undefined,
          upperBound: typeof v.UpperBound === 'number' ? v.UpperBound : undefined
        })
      }
    })
  }

  // 如果没有找到模板，返回空数组
  return variables
}

const getDeviceModes = (templateName: string): SourceOption[] => {
  const manifest = resolveDeviceTemplate(templateName)?.manifest
  if (!manifest?.Modes?.length) return []

  return manifest.Modes.map(mode => ({
    name: mode,
    type: 'mode' as const,
    values: getModeValues(manifest, mode)
  }))
}

const getDeviceStates = (templateName: string): SourceOption[] => {
  const manifest = resolveDeviceTemplate(templateName)?.manifest
  if (!manifest?.WorkingStates?.length) return []

  return manifest.WorkingStates.map(state => ({
    name: state.Name,
    type: 'state' as const
  }))
}

const getDeviceContents = (templateName: string): ContentOption[] => {
  const manifest = resolveDeviceTemplate(templateName)?.manifest
  if (!manifest?.Contents?.length) return []

  return manifest.Contents
    .filter(content => Boolean(content?.Name))
    .map(content => ({
      name: content.Name,
      privacy: String(content.Privacy).toLowerCase() === 'private' ? 'private' : 'public'
    }))
}

const contentCapableNodes = computed(() =>
  deviceNodes.value.filter(node => getDeviceContents(node.templateName).length > 0)
)

const availableContentItems = computed(() => {
  const node = resolveDeviceNode(ruleData.contentDevice)
  return node ? getDeviceContents(node.templateName) : []
})

const availableTargetApis = computed(() => {
  if (!ruleData.toId) return []
  const targetNode = resolveDeviceNode(ruleData.toId)
  if (!targetNode) return []

  // 只返回 API 名称（字符串数组）
  const apis = getDeviceApis(targetNode.templateName)
  return apis.map((a: any) => a.name)
})

const selectedTargetAcceptsContent = computed(() => {
  const targetNode = resolveDeviceNode(ruleData.toId)
  const manifest = targetNode ? resolveDeviceTemplate(targetNode.templateName)?.manifest : null
  const api = manifest?.APIs?.find(candidate => candidate.Name === ruleData.toApi)
  return api?.AcceptsContent === true
})

const currentSourceNode = computed(() =>
  currentSource.fromId ? resolveDeviceNode(currentSource.fromId) : undefined
)

const sourceItemTypeOptions = computed(() => {
  const templateName = currentSourceNode.value?.templateName || ''
  return [
    { value: 'api' as RuleSourceItemType, label: t('app.actionEvent'), count: getDeviceApis(templateName, true).length },
    { value: 'variable' as RuleSourceItemType, label: t('app.variable'), count: getDeviceVariables(templateName).length },
    { value: 'mode' as RuleSourceItemType, label: t('app.modes'), count: getDeviceModes(templateName).length },
    { value: 'state' as RuleSourceItemType, label: t('app.state'), count: getDeviceStates(templateName).length }
  ].filter(option => option.count > 0)
})

const availableSourceItems = computed<SourceOption[]>(() => {
  if (!currentSource.fromId) return []
  const sourceNode = currentSourceNode.value
  if (!sourceNode) return []

  if (currentSource.itemType === 'api') return getDeviceApis(sourceNode.templateName, true)
  if (currentSource.itemType === 'variable') return getDeviceVariables(sourceNode.templateName)
  if (currentSource.itemType === 'mode') return getDeviceModes(sourceNode.templateName)
  if (currentSource.itemType === 'state') return getDeviceStates(sourceNode.templateName)
  return []
})

// 根据选择的类型过滤显示的项
const filteredSourceItems = computed(() => {
  if (!currentSource.itemType) return []
  return availableSourceItems.value.filter((item: SourceOption) => item.type === currentSource.itemType)
})

const selectedSourceOption = computed(() =>
  filteredSourceItems.value.find((item: SourceOption) => item.name === currentSource.fromApi)
)

const currentValueOptions = computed(() => {
  if (currentSource.itemType === 'state') {
    return filteredSourceItems.value.map((item: SourceOption) => item.name)
  }
  return selectedSourceOption.value?.values || []
})

const isSetRelation = computed(() =>
  currentSource.relation === 'in' || currentSource.relation === 'not in'
)

const splitRuleValueList = (value: unknown): string[] => {
  if (!hasSourceValue(value)) return []
  const delimiter = currentSource.itemType === 'state' ? /[,|]/ : /[,;|]/
  return String(value)
    .split(delimiter)
    .map(part => part.trim())
    .filter(Boolean)
}

const currentSourceValueList = computed<string[]>({
  get: () => splitRuleValueList(currentSource.value),
  set: values => {
    currentSource.value = uniqueStrings(values).join(', ')
  }
})

const currentValuePlaceholder = computed(() => {
  if (currentSource.itemType === 'mode' || currentSource.itemType === 'state') {
    return t('app.selectPlaceholder')
  }
  const bounds = selectedSourceOption.value
  if (bounds?.lowerBound !== undefined || bounds?.upperBound !== undefined) {
    const min = bounds.lowerBound ?? '-∞'
    const max = bounds.upperBound ?? '∞'
    return `${t('app.enterValuePlaceholder')} (${min} - ${max})`
  }
  return t('app.enterValuePlaceholder')
})

// 判断是否可以添加源（根据选择的项目类型决定是否需要条件/值）
const canAddSource = computed(() => {
  if (!currentSource.fromId || !currentSource.itemType) {
    return false
  }
  if (currentSource.itemType !== 'state' && !currentSource.fromApi) {
    return false
  }

  if (isValueBasedSourceType(currentSource.itemType)) {
    return Boolean(currentSource.relation && currentSource.value)
  }

  return true
})

const missingSourceDeviceIds = computed(() => Array.from(new Set(
  ruleData.sources
    .map(source => source.fromId)
    .filter(sourceId => sourceId && !resolveDeviceNode(sourceId))
)))

const ruleDraftIncompleteReasonKey = computed(() => {
  if (ruleData.sources.length === 0) {
    return canAddSource.value
      ? 'app.addConfiguredRuleSourceBeforeSubmit'
      : 'app.configureRuleSourceBeforeSubmit'
  }
  if (missingSourceDeviceIds.value.length > 0) {
    return 'app.ruleSourceDeviceMissing'
  }
  if (ruleData.toId && !resolveDeviceNode(ruleData.toId)) {
    return 'app.ruleTargetDeviceMissing'
  }
  if (ruleData.contentDevice && !resolveDeviceNode(ruleData.contentDevice)) {
    return 'app.ruleContentDeviceMissing'
  }
  if (!ruleData.toId || !ruleData.toApi) {
    return 'app.selectRuleTargetBeforeSubmit'
  }
  if (Boolean(ruleData.contentDevice) !== Boolean(ruleData.content)) {
    return 'app.completeContentPayloadFields'
  }
  return ''
})

const ruleDraftIncompleteReason = computed(() =>
  ruleDraftIncompleteReasonKey.value ? t(ruleDraftIncompleteReasonKey.value) : ''
)

const isRuleDraftComplete = computed(() => !ruleDraftIncompleteReasonKey.value)

const hasSourceValue = (value: unknown) =>
  value !== null && value !== undefined && value !== ''

const formatSourceValue = (value: unknown, fallback: string, templateName = '') =>
  hasSourceValue(value) ? formatTemplateModelToken(templateName, value) : fallback

watch(() => currentSource.fromId, () => {
  currentSource.itemType = ''
  currentSource.fromApi = ''
  currentSource.relation = '='
  currentSource.value = ''
  if (sourceItemTypeOptions.value.length === 1) {
    currentSource.itemType = sourceItemTypeOptions.value[0].value
  }
})

watch(deviceNodes, nodes => {
  if (currentSource.fromId && !nodes.some(node => node.id === currentSource.fromId)) {
    currentSource.fromId = ''
  }
})

watch(sourceItemTypeOptions, options => {
  if (!currentSource.fromId) return
  if (currentSource.itemType && options.some(option => option.value === currentSource.itemType)) return
  currentSource.itemType = options.length === 1 ? options[0].value : ''
})

watch(() => currentSource.itemType, (newType) => {
  currentSource.fromApi = newType === 'state' ? 'state' : ''
  currentSource.relation = '='
  currentSource.value = ''
})

watch(() => currentSource.fromApi, () => {
  if (currentSource.itemType !== 'api') {
    currentSource.value = ''
  }
})

watch(conditionRelationOptions, options => {
  if (!options.some(option => option.value === currentSource.relation)) {
    currentSource.relation = options[0]?.value || '='
    currentSource.value = ''
  }
})

watch(() => currentSource.relation, () => {
  if (!isSetRelation.value && splitRuleValueList(currentSource.value).length > 1) {
    currentSource.value = splitRuleValueList(currentSource.value)[0] || ''
  }
})

watch(() => ruleData.contentDevice, () => {
  if (!availableContentItems.value.some(item => item.name === ruleData.content)) {
    ruleData.content = ''
  }
})

watch(() => [ruleData.toId, ruleData.toApi, ...availableTargetApis.value], () => {
  if (ruleData.toApi && !availableTargetApis.value.includes(ruleData.toApi)) {
    ruleData.toApi = ''
  }
  if (!selectedTargetAcceptsContent.value) {
    ruleData.contentDevice = ''
    ruleData.content = ''
  }
})

// Rule preview
const rulePreview = computed(() => {
  if (!ruleData.toId || ruleData.sources.length === 0) {
    return null
  }

  const targetNode = resolveDeviceNode(ruleData.toId)
  const sourceNodes = ruleData.sources.map(s => resolveDeviceNode(s.fromId)).filter(Boolean)

  return {
    sources: sourceNodes,
    sourceConditions: ruleData.sources,
    target: targetNode,
    action: ruleData.toApi,
    contentDevice: resolveDeviceNode(ruleData.contentDevice),
    content: ruleData.content
  }
})

// Methods
const addSource = () => {
  // 添加源设备及其条件
  if (canAddSource.value && currentSource.itemType) {
    if (ruleData.sources.length >= REQUEST_LIMITS.ruleConditions) {
      notifyBlocked(t('app.itemLimitReached', {
        resource: t('app.ruleConditions'),
        limit: REQUEST_LIMITS.ruleConditions
      }))
      return
    }
    ruleData.sources.push({
      fromId: currentSource.fromId,
      fromApi: currentSource.itemType === 'state' ? 'state' : currentSource.fromApi,
      itemType: currentSource.itemType,
      relation: currentSource.relation,
      value: currentSource.value
    })
    
    // 重置当前源选择
    currentSource.fromId = ''
    currentSource.itemType = ''
    currentSource.fromApi = ''
    currentSource.relation = '='
    currentSource.value = ''
  }
}

const removeSource = (index: number) => {
  ruleData.sources.splice(index, 1)
}

// No toast here: `ruleDraftIncompleteReason` is already rendered inline, linked by aria-describedby,
// and disables both submit buttons, so a toast would repeat text the user can see. The one path that
// can reach this with a stale draft (validateAfterAsyncCheck) raises its own distinct message.
const validateRuleDraft = () => isRuleDraftComplete.value

const buildRuleDraft = (id = ruleData.id): RuleForm => ({
  ...ruleData,
  id,
  sources: ruleData.sources.map(source => ({ ...source })),
  contentDevice: ruleData.contentDevice || undefined,
  content: ruleData.content || undefined
})

const ruleDraftFingerprint = () => JSON.stringify({
  draft: buildRuleDraft(),
  deviceIds: deviceNodes.value.map(node => `${node.id}:${node.templateName}`).sort()
})

const validateAfterAsyncCheck = (fingerprint: string) => {
  if (fingerprint !== ruleDraftFingerprint()) {
    notifyBlocked(t('app.ruleChangedDuringCheck'))
    return false
  }
  return validateRuleDraft()
}

const savingRule = ref(false)

const emitRuleSave = async () => {
  if (savingRule.value) return
  savingRule.value = true
  const rule: RuleForm = {
    ...ruleData,
    id: 'rule_' + Date.now(),
    name: ruleData.name || buildReadableRuleName(),
    sources: ruleData.sources.map(source => ({ ...source })),
    contentDevice: ruleData.contentDevice || undefined,
    content: ruleData.content || undefined
  }
  const saved = await new Promise<boolean>(resolve => {
    emit('save-rule', { rule, complete: resolve })
  })
  savingRule.value = false
  if (saved) {
    resetAndClose()
  }
}

const checkingDuplicate = ref(false)
const checkingSimilarity = ref(false)
const ruleActionBusy = computed(() =>
  checkingDuplicate.value || checkingSimilarity.value || savingRule.value
)
let ruleActionEpoch = 0

const beginRuleAction = (): number => ++ruleActionEpoch
const isRuleActionCurrent = (actionEpoch: number): boolean =>
  actionEpoch === ruleActionEpoch && props.modelValue

/**
 * Offers "save anyway" and re-checks the action epoch before honouring the answer.
 *
 * The re-check is the race guard: the dialog can be closed, reset, or re-opened for another rule
 * while the confirmation is on screen, and a stale "yes" must not save into the new draft. All four
 * check outcomes (duplicate-check failure, overlap, similarity-check failure, similarity) need
 * exactly this, so it lives in one place — four copies meant a fix to the guard had to be applied
 * four times.
 */
const confirmSaveAnyway = async (
  title: string,
  message: string,
  actionEpoch: number
): Promise<'save-anyway' | 'cancel'> => {
  const saveAnyway = await confirmChoice({
    title,
    message,
    confirmText: t('app.saveAnyway')
  })
  return saveAnyway && isRuleActionCurrent(actionEpoch) ? 'save-anyway' : 'cancel'
}

const invalidatePendingRuleAction = () => {
  const hadPendingCheck = checkingDuplicate.value || checkingSimilarity.value
  ruleActionEpoch += 1
  checkingDuplicate.value = false
  checkingSimilarity.value = false
  if (hadPendingCheck) dismissOpenConfirmation()
}

watch(
  () => props.modelValue,
  isOpen => {
    if (!isOpen) invalidatePendingRuleAction()
  },
  { flush: 'sync' }
)

const runDuplicateCheck = async (
  actionEpoch: number
): Promise<'clear' | 'save-anyway' | 'cancel'> => {
  checkingDuplicate.value = true
  try {
    let result
    try {
      result = await boardApi.checkDuplicateRule(buildRuleDraft())
    } catch (error: any) {
      if (!isRuleActionCurrent(actionEpoch)) return 'cancel'
      console.error('Duplicate check failed:', error)
      return confirmSaveAnyway(
        t('app.checkDuplicate'), t('app.duplicateCheckFailedCanStillSave'), actionEpoch)
    }

    if (!isRuleActionCurrent(actionEpoch)) return 'cancel'

    if (result.isDuplicate) {
      const reason = t(duplicateRuleReasonKey(result.reasonCode))
      const message = result.matchedRule
        ? t('app.identicalRuleNotSavedWithMatch', {
            rule: result.matchedRule,
            reason
          })
        : t('app.identicalRuleNotSaved')

      await acknowledge({ title: t('app.identicalRuleDetected'), message })
      return 'cancel'
    }

    if (result.requiresReview) {
      const reason = t(duplicateRuleReasonKey(result.reasonCode))
      const message = result.matchedRule
        ? t('app.overlappingRuleMayExistWithMatch', {
            rule: result.matchedRule,
            reason
          })
        : t('app.overlappingRuleMayExist', { reason })

      return confirmSaveAnyway(t('app.overlappingRuleDetected'), message, actionEpoch)
    }

    return 'clear'
  } finally {
    if (actionEpoch === ruleActionEpoch) checkingDuplicate.value = false
  }
}

const runSimilarityCheck = async (
  actionEpoch: number
): Promise<'clear' | 'save-anyway' | 'cancel'> => {
  checkingSimilarity.value = true
  try {
    let result
    try {
      result = await boardApi.checkRuleSimilarity(buildRuleDraft())
    } catch (error: any) {
      if (!isRuleActionCurrent(actionEpoch)) return 'cancel'
      console.error('AI similarity check failed:', error)
      return confirmSaveAnyway(
        t('app.aiRuleSimilarityDetected'), t('app.aiSimilarityCheckFailedCanStillSave'), actionEpoch)
    }

    if (!isRuleActionCurrent(actionEpoch)) return 'cancel'

    if (result.requiresReview) {
      const reason = t(ruleSimilarityReasonKey(result.reasonCode))
      const message = result.matchedRule
        ? t('app.aiSimilarRuleMayExistWithMatch', {
            rule: result.matchedRule,
            reason
          })
        : t('app.aiSimilarRuleMayExist', { reason })

      return confirmSaveAnyway(t('app.aiRuleSimilarityDetected'), message, actionEpoch)
    }

    return 'clear'
  } finally {
    if (actionEpoch === ruleActionEpoch) checkingSimilarity.value = false
  }
}

const handleSave = async () => {
  if (ruleActionBusy.value || !validateRuleDraft()) return

  const actionEpoch = beginRuleAction()
  const fingerprint = ruleDraftFingerprint()
  const duplicateResult = await runDuplicateCheck(actionEpoch)
  if (duplicateResult === 'cancel' || !isRuleActionCurrent(actionEpoch)) return
  if (!validateAfterAsyncCheck(fingerprint)) return

  await emitRuleSave()
}

const handleCheckSimilarity = async () => {
  if (ruleActionBusy.value || !validateRuleDraft()) return

  const actionEpoch = beginRuleAction()
  const fingerprint = ruleDraftFingerprint()
  const similarityResult = await runSimilarityCheck(actionEpoch)
  if (similarityResult === 'cancel' || !isRuleActionCurrent(actionEpoch)) return
  if (!validateAfterAsyncCheck(fingerprint)) return
  if (similarityResult === 'save-anyway') {
    await emitRuleSave()
  } else {
    notifySuccess(t('app.noSimilarRulesFound'))
  }
}

const resetAndClose = () => {
  invalidatePendingRuleAction()
  // Reset form
  ruleData.id = ''
  ruleData.name = ''
  ruleData.sources = []
  ruleData.toId = ''
  ruleData.toApi = ''
  ruleData.contentDevice = ''
  ruleData.content = ''
  currentSource.fromId = ''
  currentSource.itemType = ''
  currentSource.fromApi = ''
  currentSource.relation = '='
  currentSource.value = ''

  emit('update:modelValue', false)
}

const handleClose = () => {
  if (savingRule.value) return
  resetAndClose()
}

const isDialogOpen = computed(() => props.modelValue)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, handleClose)

// Helper functions for UI
/* One owner in `utils/deviceIcon.ts`. This copy classified `door` as a sensor and lacked `sprinkler` and
   `home mode`, so the same device drew different icons here and in DeviceDialog. */
const getDeviceIcon = (node?: DeviceNode | null) => node ? deviceIconFor(node.templateName) : 'sensors'

function buildReadableRuleName(): string {
  const sources = ruleData.sources.map(source => {
    const deviceLabel = resolveDeviceNode(source.fromId)?.label || t('app.unknown')
    const itemLabel = formatRuleSourceName(source)
    if (isValueBasedSourceType(source.itemType)) {
      return `${deviceLabel}.${itemLabel} ${source.relation || '='} ${formatRuleSourceModelToken(source, source.value)}`.trim()
    }
    return `${deviceLabel} ${t('app.triggers')} ${itemLabel}`
  })
  const targetLabel = resolveDeviceNode(ruleData.toId)?.label || t('app.unknown')
  return t('app.ifThenDescription', {
    source: sources.join(` ${t('app.and')} `),
    target: targetLabel,
    action: formatTargetModelToken(ruleData.toApi)
  })
}

const getSourceTypeLabel = (type?: RuleSourceItemType) => {
  if (type === 'api') return t('app.actionEvent')
  if (type === 'variable') return t('app.variable')
  if (type === 'mode') return t('app.modes')
  if (type === 'state') return t('app.state')
  return t('app.actionEvent')
}

const getSourceTypeIcon = (type?: RuleSourceItemType | '') => {
  if (type === 'api') return 'bolt'
  if (type === 'variable') return 'tune'
  if (type === 'mode') return 'toggle_on'
  if (type === 'state') return 'account_tree'
  return 'category'
}

const getSourceTypeClass = (type?: RuleSourceItemType) => {
  if (type === 'api') return 'board-chip-info board-text-info'
  if (type === 'variable') return 'board-chip-success board-text-success'
  if (type === 'mode') return 'board-chip-info board-text-info'
  if (type === 'state') return 'board-chip-warning board-text-warning'
  return 'bg-slate-100 text-slate-600 dark:bg-slate-700 dark:text-slate-300'
}

const sourceShowsRelationValue = (type?: RuleSourceItemType) =>
  isValueBasedSourceType(type)
</script>

<template>
  <div
    v-show="modelValue"
    class="iot-dialog-overlay"
    @keydown="handleModalKeydown"
  >
    <div
      :ref="setDialogRef"
      data-testid="rule-builder-dialog"
      class="iot-dialog iot-dialog--xl"
      role="dialog"
      aria-modal="true"
      aria-labelledby="rule-builder-title"
      tabindex="-1"
    >
      <fieldset
        :disabled="savingRule"
        data-testid="rule-editor-fieldset"
        class="contents"
      >
      <!-- Header -->
      <div class="iot-dialog__header">
        <span class="iot-dialog__icon" aria-hidden="true">
          <span class="material-symbols-outlined">auto_fix_high</span>
        </span>
        <div class="iot-dialog__heading">
          <h2 id="rule-builder-title" class="iot-dialog__title">{{ t('app.createNewRule') }}</h2>
        </div>
        <button
          type="button"
          @click="handleClose"
          class="iot-dialog__close"
          :aria-label="t('app.close')"
        >
          <span class="material-icons-round" aria-hidden="true">close</span>
        </button>
      </div>

      <!-- Content -->
      <div class="iot-dialog__body iot-scroll-region space-y-8">
        <!-- Rule Name Input -->
        <div class="space-y-2">
          <label for="rule-builder-name" class="text-sm font-semibold text-slate-600 dark:text-slate-400">{{ t('app.ruleName') }}</label>
          <input
            id="rule-builder-name"
            v-model="ruleData.name"
            type="text"
            :placeholder="t('app.ruleNamePlaceholder')"
            class="w-full min-h-11 px-3 py-2 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 placeholder:text-slate-600 dark:placeholder:text-slate-400"
          />
        </div>

        <!-- IF (Trigger) Section -->
        <section class="space-y-4">
          <div class="flex items-center gap-2 mb-2">
            <span class="board-chip-info board-text-info text-xs font-bold px-2 py-1 rounded uppercase tracking-wider">
              {{ t('app.ifTrigger') }}
            </span>
            <h2 class="text-sm font-medium text-slate-500 dark:text-slate-400 uppercase tracking-wide">
              {{ t('app.sourceDevices') }}
            </h2>
          </div>
          <p class="text-xs leading-relaxed text-slate-500 dark:text-slate-400">
            {{ t('app.ruleLogicHint') }}
          </p>

          <!-- Add Source Form -->
          <div class="rule-builder-grid">
            <!-- 设备选择 -->
            <div class="space-y-2">
              <label for="rule-source-device" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.device') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  {{ currentSource.fromId ? getDeviceIcon(resolveDeviceNode(currentSource.fromId)) : 'sensors' }}
                </span>
                <select
                  id="rule-source-device"
                  v-model="currentSource.fromId"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="deviceNodes.length === 0"
                >
                  <option v-if="deviceNodes.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option v-for="node in deviceNodes" :key="node.id" :value="node.id">
                    {{ node.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 类型选择 (API / Variable / Mode / State) -->
            <div class="space-y-2">
              <label for="rule-source-type" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.type') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  {{ getSourceTypeIcon(currentSource.itemType) }}
                </span>
                <select
                  id="rule-source-type"
                  v-model="currentSource.itemType"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="!currentSource.fromId || sourceItemTypeOptions.length === 0"
                >
                  <option v-if="!currentSource.fromId && deviceNodes.length > 0" value="">{{ t('app.selectPlaceholder') }}</option>
                  <option v-else-if="sourceItemTypeOptions.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option
                    v-for="option in sourceItemTypeOptions"
                    :key="option.value"
                    :value="option.value"
                  >
                    {{ option.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- Observable action-event selection. Only Signal=true APIs can trigger a rule. -->
            <div class="space-y-2" v-if="currentSource.itemType === 'api'">
              <label for="rule-source-api" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.actionEvent') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  bolt
                </span>
                <select
                  id="rule-source-api"
                  v-model="currentSource.fromApi"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="filteredSourceItems.length === 0"
                >
                  <option v-if="filteredSourceItems.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option v-for="item in filteredSourceItems" :key="item.name" :value="item.name">
                    {{ item.label || formatCurrentSourceModelToken(item.name) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- Variable选择 - 仅选择 Variable 类型时显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'variable'">
              <label for="rule-source-variable" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.variable') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  tune
                </span>
                <select
                  id="rule-source-variable"
                  v-model="currentSource.fromApi"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="filteredSourceItems.length === 0"
                >
                  <option v-if="filteredSourceItems.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option v-for="item in filteredSourceItems" :key="item.name" :value="item.name">
                    {{ item.label || formatCurrentSourceModelToken(item.name) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- Mode 选择 - 仅选择 Mode 类型时显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'mode'">
              <label for="rule-source-mode" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.modes') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  toggle_on
                </span>
                <select
                  id="rule-source-mode"
                  v-model="currentSource.fromApi"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="filteredSourceItems.length === 0"
                >
                  <option v-if="filteredSourceItems.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option v-for="item in filteredSourceItems" :key="item.name" :value="item.name">
                    {{ formatCurrentSourceModelToken(item.name) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 条件选择 - 值条件类型显示 -->
            <div class="space-y-2" v-if="sourceShowsRelationValue(currentSource.itemType || undefined)">
              <label for="rule-source-condition" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.condition') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  compare_arrows
                </span>
                <select
                  id="rule-source-condition"
                  v-model="currentSource.relation"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="currentSource.itemType !== 'state' && !currentSource.fromApi"
                >
                  <option v-for="rel in conditionRelationOptions" :key="rel.value" :value="rel.value">
                    {{ rel.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 值输入 - 值条件类型显示 -->
            <div class="space-y-2" v-if="sourceShowsRelationValue(currentSource.itemType || undefined)">
              <label for="rule-source-value" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.value') }}</label>
              <div v-if="currentValueOptions.length > 0 && isSetRelation" class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  checklist
                </span>
                <select
                  id="rule-source-value"
                  v-model="currentSourceValueList"
                  multiple
                  size="4"
                  class="w-full min-h-[7.5rem] pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="!currentSource.relation"
                >
                  <option v-for="value in currentValueOptions" :key="value" :value="value">
                    {{ formatCurrentSourceModelToken(value) }}
                  </option>
                </select>
              </div>
              <div v-else-if="currentValueOptions.length > 0" class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  list
                </span>
                <select
                  id="rule-source-value"
                  v-model="currentSource.value"
                  class="w-full min-h-11 pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="!currentSource.relation"
                >
                  <option value="" disabled hidden>{{ t('app.selectPlaceholder') }}</option>
                  <option v-for="value in currentValueOptions" :key="value" :value="value">
                    {{ formatCurrentSourceModelToken(value) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
              <input
                v-else
                id="rule-source-value"
                v-model="currentSource.value"
                type="text"
                :placeholder="currentValuePlaceholder"
                class="w-full px-3 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200 text-sm placeholder:text-slate-600 dark:placeholder:text-slate-400"
                :disabled="!currentSource.relation"
                @keydown.enter.prevent="addSource"
              />
            </div>
          </div>

          <button
            type="button"
            @click="addSource"
            data-testid="rule-add-source"
            class="flex min-h-11 items-center gap-2 board-text-info font-medium text-sm hover:board-chip-info dark:hover:bg-[color:var(--accent-strong)]/20 px-3 py-2 rounded-lg transition-all group"
            :disabled="!canAddSource"
          >
            <span class="material-icons-round text-lg group-hover:scale-110 transition-transform">add_circle_outline</span>
            {{ t('app.addSource') }}
          </button>

          <!-- Sources List -->
          <div v-if="ruleData.sources.length > 0" class="space-y-2">
            <div
              v-for="(source, index) in ruleData.sources"
              :key="index"
              class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border"
              :class="resolveDeviceNode(source.fromId)
                ? 'border-slate-200 dark:border-slate-600'
                : 'board-border-subtle board-chip-danger'"
            >
              <!-- Decorative: the device label sits immediately beside it and carries the meaning. -->
              <span class="material-icons-round board-text-info text-sm" aria-hidden="true">sensors</span>
              <span class="text-sm text-slate-700 dark:text-slate-200 truncate" :title="resolveDeviceNode(source.fromId)?.label || source.fromId">
                {{ resolveDeviceNode(source.fromId)?.label || source.fromId }}
              </span>
              <span
                v-if="!resolveDeviceNode(source.fromId)"
                class="shrink-0 rounded board-chip-danger px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-danger"
              >
                {{ t('app.missingDevice') }}
              </span>
              <span class="text-xs text-slate-500">•</span>
              <span class="text-sm font-medium board-text-info truncate" :title="formatRuleSourceName(source)">
                {{ formatRuleSourceName(source) }}
              </span>
              <span class="text-xs px-1.5 py-0.5 rounded" :class="getSourceTypeClass(source.itemType)">
                {{ getSourceTypeLabel(source.itemType) }}
              </span>
              <!-- 条件和值仅对值条件类型显示 -->
              <template v-if="sourceShowsRelationValue(source.itemType)">
                <span class="text-xs text-slate-500">→</span>
                <span class="text-sm font-medium board-text-warning">
                  {{ relationOptions.find(r => r.value === source.relation)?.label || source.relation || '=' }}
                </span>
                <span class="text-sm text-slate-600 dark:text-slate-300 truncate" :title="formatSourceValue(source.value, `(${t('app.anyValue')})`, resolveDeviceNode(source.fromId)?.templateName)">
                  {{ formatSourceValue(source.value, `(${t('app.anyValue')})`, resolveDeviceNode(source.fromId)?.templateName) }}
                </span>
              </template>
              <button
                type="button"
                @click="removeSource(index)"
                class="ml-auto board-text-danger hover:text-sm transition-colors"
                :aria-label="t('app.remove')"
              >
                <span class="material-icons-round text-sm" aria-hidden="true">close</span>
              </button>
            </div>
          </div>
        </section>


        <!-- THEN (Action) Section -->
        <section class="space-y-4">
          <div class="flex items-center gap-2 mb-2">
            <span class="board-chip-success board-text-success text-xs font-bold px-2 py-1 rounded uppercase tracking-wider">
              {{ t('app.thenAction') }}
            </span>
            <h2 class="text-sm font-medium text-slate-500 dark:text-slate-400 uppercase tracking-wide">
              {{ t('app.targetDevice') }}
            </h2>
          </div>

          <div class="rule-builder-target-grid">
            <div class="space-y-2">
              <label for="rule-target-device" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.device') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  {{ ruleData.toId ? getDeviceIcon(resolveDeviceNode(ruleData.toId)) : 'sensors' }}
                </span>
                <select
                  id="rule-target-device"
                  v-model="ruleData.toId"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200"
                  :disabled="deviceNodes.length === 0"
                >
                  <option v-if="deviceNodes.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectDevicePlaceholder') }}</option>
                  <option v-for="node in deviceNodes" :key="node.id" :value="node.id">
                    {{ node.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <div class="space-y-2">
              <label for="rule-target-action" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">{{ t('app.action') }}</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                  bolt
                </span>
                <select
                  id="rule-target-action"
                  v-model="ruleData.toApi"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200"
                  :disabled="!ruleData.toId || availableTargetApis.length === 0"
                >
                  <option v-if="!ruleData.toId && deviceNodes.length > 0" value="" disabled hidden>{{ t('app.selectAction') }}</option>
                  <option v-else-if="availableTargetApis.length === 0" value="">{{ t('app.none') }}</option>
                  <option v-else value="" disabled hidden>{{ t('app.selectAction') }}</option>
                  <option v-for="api in availableTargetApis" :key="api" :value="api">
                    {{ formatTargetModelToken(api) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>
          </div>

          <div
            v-if="selectedTargetAcceptsContent && (contentCapableNodes.length > 0 || Boolean(ruleData.contentDevice))"
            class="rounded-2xl border border-slate-200 bg-slate-50/70 p-4 dark:border-slate-700 dark:bg-slate-900/40"
          >
            <div class="mb-3 flex items-start gap-2">
              <span class="material-icons-round text-sm board-text-success" aria-hidden="true">inventory_2</span>
              <div class="min-w-0">
                <p class="text-xs font-bold uppercase tracking-wide text-slate-600 dark:text-slate-300">
                  {{ t('app.contentPayload') }}
                </p>
                <p class="mt-0.5 text-xs leading-relaxed text-slate-500 dark:text-slate-400">
                  {{ t('app.contentPayloadHint') }}
                </p>
              </div>
            </div>

            <div class="rule-builder-target-grid">
              <div class="space-y-2">
                <label for="rule-content-device" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">
                  {{ t('app.contentSourceDevice') }}
                </label>
                <div class="relative group select-wrapper">
                  <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                    source
                  </span>
                  <select
                    id="rule-content-device"
                    v-model="ruleData.contentDevice"
                    data-testid="rule-content-device"
                    class="w-full pl-10 pr-10 py-3 bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200"
                  >
                    <option value="">{{ t('app.noContentPayload') }}</option>
                    <option v-for="node in contentCapableNodes" :key="node.id" :value="node.id">
                      {{ node.label }}
                    </option>
                  </select>
                  <span class="material-icons-round dropdown-arrow">expand_more</span>
                </div>
              </div>

              <div class="space-y-2">
                <label for="rule-content-name" class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">
                  {{ t('app.contentItem') }}
                </label>
                <div class="relative group select-wrapper">
                  <span class="material-icons-round select-icon text-slate-400 group-focus-within:board-text-info transition-colors" aria-hidden="true">
                    photo_library
                  </span>
                  <select
                    id="rule-content-name"
                    v-model="ruleData.content"
                    data-testid="rule-content-name"
                    class="w-full pl-10 pr-10 py-3 bg-white dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-[color:var(--accent-border)] focus:border-[color:var(--accent)] transition-all text-slate-700 dark:text-slate-200"
                    :disabled="!ruleData.contentDevice || availableContentItems.length === 0"
                  >
                    <option v-if="!ruleData.contentDevice" value="">{{ t('app.selectContentDeviceFirst') }}</option>
                    <option v-else-if="availableContentItems.length === 0" value="">{{ t('app.none') }}</option>
                    <option v-else value="" disabled hidden>{{ t('app.selectContent') }}</option>
                    <option v-for="content in availableContentItems" :key="content.name" :value="content.name">
                      {{ t('app.contentItemWithSensitivity', { name: formatContentModelToken(content.name), privacy: t(`app.${content.privacy}`) }) }}
                    </option>
                  </select>
                  <span class="material-icons-round dropdown-arrow">expand_more</span>
                </div>
              </div>
            </div>
          </div>
        </section>

        <!-- Rule Preview -->
        <div v-if="rulePreview" class="p-6 rounded-2xl bg-slate-50 dark:bg-slate-900/50 border border-dashed border-slate-300 dark:border-slate-600">
          <p class="text-xs font-bold text-slate-500 dark:text-slate-500 uppercase tracking-widest mb-4">{{ t('app.rulePreview') }}</p>
          <div class="flex items-center gap-3 text-sm font-medium text-slate-600 dark:text-slate-300">
            <!-- Source devices with conditions -->
            <div class="flex flex-wrap items-center gap-2">
              <template v-for="(source, index) in rulePreview.sourceConditions" :key="source.fromId + index">
                <div class="flex items-center gap-1 px-2 py-1.5 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600 text-xs">
                  <!-- Decorative: the device label sits immediately beside it and carries the meaning. -->
              <span class="material-icons-round board-text-info text-sm" aria-hidden="true">sensors</span>
                  <span class="truncate" :title="resolveDeviceNode(source.fromId)?.label || source.fromId || t('app.unknown')">{{ resolveDeviceNode(source.fromId)?.label || source.fromId || t('app.unknown') }}</span>
                  <span class="text-slate-500">→</span>
                  <span class="board-text-info truncate" :title="formatRuleSourceName(source)">{{ formatRuleSourceName(source) }}</span>
                  <span class="text-xs px-1 py-0.5 rounded" :class="getSourceTypeClass(source.itemType)">
                    {{ getSourceTypeLabel(source.itemType) }}
                  </span>
                  <!-- 条件和值仅对值条件类型显示 -->
                  <template v-if="sourceShowsRelationValue(source.itemType)">
                    <span class="board-text-warning">{{ relationOptions.find(r => r.value === source.relation)?.label.split(' ')[0] || '=' }}</span>
                    <span class="text-slate-700 dark:text-slate-300">{{ formatSourceValue(source.value, '*', resolveDeviceNode(source.fromId)?.templateName) }}</span>
                  </template>
                </div>
                <!-- Add "AND" connector if not the last source -->
                <span v-if="index < rulePreview.sourceConditions.length - 1" class="text-xs font-bold text-slate-500 dark:text-slate-500 px-1">
                  {{ t('app.and') }}
                </span>
              </template>
            </div>

            <!-- Arrow -->
            <span class="material-icons-round text-slate-500 dark:text-slate-500">trending_flat</span>

            <!-- Target device -->
            <div class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600 min-w-[60px] justify-center">
              <span class="material-icons-round board-text-success text-base">{{ getDeviceIcon(rulePreview.target!) }}</span>
              <span>{{ rulePreview.target?.label }}</span>
            </div>

            <!-- Description -->
            <div class="ml-auto text-xs text-slate-500 italic max-w-xs">
              <template v-if="rulePreview.sources.length === 1">
                {{ t('app.singleSourceRulePreview', { source: rulePreview.sources[0]?.label, target: rulePreview.target?.label, action: formatTargetModelToken(rulePreview.action) }) }}
              </template>
              <template v-else-if="rulePreview.sources.length === 2">
                {{ t('app.twoSourceRulePreview', { sourceA: rulePreview.sources[0]?.label, sourceB: rulePreview.sources[1]?.label, target: rulePreview.target?.label, action: formatTargetModelToken(rulePreview.action) }) }}
              </template>
              <template v-else>
                {{ t('app.multiSourceRulePreview', { source: rulePreview.sources[0]?.label, count: rulePreview.sources.length - 1, target: rulePreview.target?.label, action: formatTargetModelToken(rulePreview.action) }) }}
              </template>
              <span v-if="rulePreview.contentDevice && rulePreview.content" class="mt-1 block not-italic board-text-success">
                {{ t('app.copyFrom') }} {{ rulePreview.contentDevice.label }}.{{ formatContentModelToken(rulePreview.content) }}
              </span>
            </div>
          </div>
        </div>
      </div>
      </fieldset>

      <!-- Footer -->
      <div class="iot-dialog__footer flex-wrap">
        <button
          type="button"
          @click="handleClose"
          :disabled="savingRule"
          class="iot-dialog-btn iot-dialog-btn--ghost iot-dialog__footer-aside"
        >
          {{ t('app.cancel') }}
        </button>
        <div class="ml-auto flex min-w-0 flex-col items-end gap-2">
          <p
            v-if="ruleDraftIncompleteReason"
            id="rule-draft-readiness"
            data-testid="rule-draft-readiness"
            role="status"
            class="max-w-xl text-right text-xs leading-5 text-slate-500 dark:text-slate-400"
          >
            {{ ruleDraftIncompleteReason }}
          </p>
          <div class="flex flex-wrap items-center justify-end gap-3">
            <!-- No `disabled:opacity-50` on this one: it is a *text* button on a role colour already close to
                 the contrast floor, so halving it measured 2.09:1 in light theme. The cursor and the
                 `disabled` attribute carry the state without spending contrast — same call as the exploration
                 panel's "Select all". -->
            <button
              type="button"
              @click="handleCheckSimilarity"
              data-testid="rule-check-duplicate"
              :disabled="!isRuleDraftComplete || ruleActionBusy"
              :aria-describedby="ruleDraftIncompleteReason ? 'rule-draft-readiness' : undefined"
              class="iot-dialog-btn iot-dialog-btn--quiet"
            >
              <span v-if="checkingSimilarity" class="iot-dialog-btn__spinner"></span>
              <span>{{ checkingSimilarity ? t('app.checkingAiSimilarity') : t('app.aiSimilarityCheck') }}</span>
            </button>
            <button
              type="button"
              @click="handleSave"
              data-testid="rule-save"
              :disabled="!isRuleDraftComplete || ruleActionBusy"
              :aria-describedby="ruleDraftIncompleteReason ? 'rule-draft-readiness' : undefined"
              class="iot-dialog-btn iot-dialog-btn--primary"
            >
              {{ savingRule ? t('app.saving') : t('app.createRule') }}
            </button>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.rule-builder-grid,
.rule-builder-target-grid {
  display: grid;
  align-items: end;
  gap: clamp(0.75rem, 2vw, 1rem);
}

.rule-builder-grid {
  grid-template-columns: repeat(auto-fit, minmax(min(100%, 11rem), 1fr));
}

.rule-builder-target-grid {
  grid-template-columns: repeat(auto-fit, minmax(min(100%, 14rem), 1fr));
}

/* Focus styles for selects */
select:focus {
  outline: none;
  box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.1);
}

/* Hide default select dropdown arrow */
select {
  -webkit-appearance: none;
  -moz-appearance: none;
  appearance: none;
  background-image: none;
}

/* Ensure dropdown arrow is positioned correctly */
.select-wrapper {
  position: relative;
}

.select-wrapper .dropdown-arrow {
  position: absolute;
  right: 12px;
  top: 50%;
  transform: translateY(-50%);
  pointer-events: none;
  color: var(--text-muted);
  font-size: 18px;
  transition: color 0.2s ease;
}

.select-wrapper:hover .dropdown-arrow {
  color: var(--text-muted);
}

/* Ensure icons are perfectly aligned with select text */
.select-wrapper .select-icon {
  position: absolute;
  left: 12px;
  top: 50%;
  transform: translateY(-50%);
  pointer-events: none;
  font-size: 20px;
  line-height: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  width: 20px;
  height: 20px;
}
</style>
