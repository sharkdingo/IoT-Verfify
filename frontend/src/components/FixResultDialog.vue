<script setup lang="ts">
import { ref, computed, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { ElMessage, ElMessageBox } from 'element-plus'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import boardApi from '@/api/board'
import { FIX_RESPONSE_INCOMPLETE_CODE } from '@/utils/fixResponse'
import { generationIssueReasonKey } from '@/utils/generationIssue'
import { localizedErrorMessage, localizedTextOrFallback } from '@/utils/userMessage'
import type {
  FaultLocalizationResult,
  FaultRule,
  FixApplyResult,
  FixResult,
  FixStrategyAttempt,
  FixStrategyAttemptStatus,
  FixStrategyName,
  FixSuggestion,
  ParameterAdjustment,
  PreferredRangeSelection
} from '@/types/fix'

const props = defineProps<{
  visible: boolean
  traceId: number
  violatedSpecId?: string
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'applied': [result: FixApplyResult]
  'outcome-uncertain': []
}>()

const { t, locale } = useI18n()

const faultLoading = ref(false)
const faultLoadFailed = ref(false)
const strategyLoading = ref<FixStrategyName | null>(null)
const fixSearchElapsedSeconds = ref(0)
const activeFixRequestId = ref<string | null>(null)
const activeFixAbortController = ref<AbortController | null>(null)
let fixSearchTimer: ReturnType<typeof setInterval> | null = null
const strategyErrors = ref<Partial<Record<FixStrategyName, string>>>({})
const strategyWarnings = ref<Partial<Record<FixStrategyName, string[]>>>({})
const fixResult = ref<FixResult | null>(null)
const faultLocalization = ref<FaultLocalizationResult | null>(null)
const faultRules = ref<FaultRule[]>([])
const selectedStrategy = ref<FixStrategyName>('parameter')
const applyingFix = ref(false)
const parameterAdjustmentCatalog = ref<ParameterAdjustment[]>([])
const lastParameterRequestFingerprint = ref<string | null>(null)
// 记录本次 /fix 用的参数偏好选择，apply 时原样回传，保证后端重算复现同一建议。
const lastPreferredRangeSelections = ref<PreferredRangeSelection[] | undefined>(undefined)

type PreferredRangeRow = {
  id: string
  targetId: string
  lower: number | null
  upper: number | null
}

const strategyOrder: FixStrategyName[] = ['parameter', 'condition', 'remove']

const strategyIcons: Record<FixStrategyName, string> = {
  parameter: 'tune',
  condition: 'checklist',
  remove: 'delete_forever'
}

const strategyLabels = computed<Record<FixStrategyName, string>>(() => ({
  parameter: t('app.fixStrategyParameter'),
  condition: t('app.fixStrategyCondition'),
  remove: t('app.fixStrategyRemove')
}))

const strategyDescriptions = computed<Record<FixStrategyName, string>>(() => ({
  parameter: t('app.fixStrategyParameterDesc'),
  condition: t('app.fixStrategyConditionDesc'),
  remove: t('app.fixStrategyRemoveDesc')
}))

const strategyOptions = computed(() => strategyOrder.map(value => ({
  value,
  label: strategyLabels.value[value],
  icon: strategyIcons[value]
})))

const fixResponseErrorMessage = (error: any, fallback: string) =>
  error?.code === FIX_RESPONSE_INCOMPLETE_CODE
    ? t('app.fixResponseIncomplete')
    : localizedErrorMessage(error, fallback, locale.value)

const fixApplyErrorMessage = (error: any) => {
  const raw = error?.response?.data?.message || error?.message
  if (typeof raw === 'string'
    && (/rules\[\d+\]\.conditions\[\d+\]\.deviceName/i.test(raw)
      || /unknown (?:condition|command|content) device/i.test(raw))) {
    return t('app.fixDeviceReferenceUnavailable')
  }
  return localizedTextOrFallback(raw, t('app.failedToApplyFix'), locale.value)
}

const displayedFixWarnings = computed(() => Array.from(new Set([
  ...(faultLocalization.value?.warnings || []),
  ...(fixResult.value?.warnings || [])
])))

const displayedSourceGenerationIssues = computed(() =>
  fixResult.value?.sourceGenerationIssues?.length
    ? fixResult.value.sourceGenerationIssues
    : faultLocalization.value?.sourceGenerationIssues || [])

const localizedFixLimitations = computed(() => {
  const messages: string[] = []
  const source = fixResult.value || faultLocalization.value
  if (source && source.sourceModelComplete === false) {
    messages.push(t('app.fixSourceModelIncompleteLimitation', {
      rules: source.sourceDisabledRuleCount,
      specs: source.sourceSkippedSpecCount
    }))
  }
  if (fixResult.value?.templateSnapshotComparison === 'CHANGED') {
    messages.push(t('app.fixTemplateSnapshotChangedLimitation'))
  } else if (fixResult.value?.templateSnapshotComparison === 'UNAVAILABLE') {
    messages.push(t('app.fixTemplateSnapshotUnavailableLimitation'))
  }
  return Array.from(new Set(messages))
})

const currentStrategyLoading = computed(() => strategyLoading.value === selectedStrategy.value)
const anotherStrategyLoading = computed(() => strategyLoading.value !== null && !currentStrategyLoading.value)
const hasAttemptResults = computed(() => (fixResult.value?.strategyAttempts?.length ?? 0) > 0)

const headerStatus = computed(() => {
  if (strategyLoading.value) {
    return t('app.tryingFixStrategy', { strategy: strategyLabels.value[strategyLoading.value] })
  }
  if (verifiedCount.value > 0) {
    return t('app.verifiedSolutionsCount', { count: verifiedCount.value })
  }
  if (fixResult.value?.strategyAttempts?.length) {
    return t('app.noVerifiedSolutionsYet')
  }
  return t('app.selectFixStrategyPrompt')
})

const preferredRangeRows = ref<PreferredRangeRow[]>([])

const newRangeRowId = () => `${Date.now()}-${Math.random().toString(36).slice(2)}`

const parameterAdjustments = computed(() => {
  return parameterAdjustmentCatalog.value
})

const preferredRangeTargetId = (adjustment: ParameterAdjustment) => adjustment.targetId

const formatPreferredRangeTarget = (adjustment: ParameterAdjustment) => t('app.preferredRangeTargetLabel', {
  description: adjustment.description || t('app.parameterAdjustmentFallback', {
    attribute: adjustment.attribute,
    relation: adjustment.relation,
    original: adjustment.originalValue,
    suggested: adjustment.newValue
  })
})

const preferredRangeTargetOptions = computed(() => parameterAdjustments.value.map(adjustment => ({
  value: preferredRangeTargetId(adjustment),
  label: formatPreferredRangeTarget(adjustment),
  adjustment
})).filter(option => option.value))

const parameterAdjustmentByTargetId = computed(() => {
  const byTargetId = new Map<string, ParameterAdjustment>()
  parameterAdjustments.value.forEach(adjustment => {
    const targetId = preferredRangeTargetId(adjustment)
    if (targetId) byTargetId.set(targetId, adjustment)
  })
  return byTargetId
})

const preferredRangeTargetLabel = (targetId: string) =>
  preferredRangeTargetOptions.value.find(option => option.value === targetId)?.label || t('app.unknownPreferredRangeTarget')

const activePreferredRangeCount = computed(() => {
  return lastPreferredRangeSelections.value?.length ?? 0
})

const parameterPreferenceFingerprint = () => JSON.stringify(preferredRangeRows.value.map(row => ({
  targetId: row.targetId,
  lower: row.lower,
  upper: row.upper
})))

const parameterPreferencesChanged = computed(() => {
  if (!fixResult.value?.suggestions.some(item => item.strategy === 'parameter')) return false
  return lastParameterRequestFingerprint.value !== parameterPreferenceFingerprint()
})

const suggestionIsCurrent = (suggestion: FixSuggestion) =>
  suggestion.strategy !== 'parameter' || !parameterPreferencesChanged.value

const isBlank = (value: unknown) => value === null || value === undefined || value === ''

const buildPreferredRangeSelections = (showWarnings = false): PreferredRangeSelection[] | undefined | null => {
  const selections: PreferredRangeSelection[] = []
  const seen = new Set<string>()

  for (const row of preferredRangeRows.value) {
    const values = [row.targetId, row.lower, row.upper]
    if (values.every(isBlank)) {
      continue
    }
    if (values.some(isBlank)) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeCompleteFields'))
      return null
    }

    const targetId = String(row.targetId)
    const lower = Number(row.lower)
    const upper = Number(row.upper)

    const adjustment = parameterAdjustmentByTargetId.value.get(targetId)
    if (!adjustment) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeSelectTarget'))
      return null
    }
    if (!Number.isFinite(lower) || !Number.isFinite(upper) || !Number.isInteger(lower) || !Number.isInteger(upper)) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeIntegerBounds'))
      return null
    }
    if (lower > upper) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeLowerBeforeUpper'))
      return null
    }

    if (seen.has(targetId)) {
      if (showWarnings) ElMessage.warning(t('app.duplicatePreferredRange', { key: preferredRangeTargetLabel(targetId) }))
      return null
    }
    seen.add(targetId)
    selections.push({
      targetId,
      lower,
      upper
    })
  }

  return selections.length > 0 ? selections : undefined
}

const addPreferenceRow = (adjustment?: ParameterAdjustment) => {
  const nextAdjustment = adjustment ?? parameterAdjustments.value.find(adj => {
    const targetId = preferredRangeTargetId(adj)
    return targetId && !preferredRangeRows.value.some(row => row.targetId === targetId)
  })
  if (!nextAdjustment) {
    ElMessage.warning(t('app.noParameterPreferenceTargets'))
    return
  }
  preferredRangeRows.value.push({
    id: newRangeRowId(),
    targetId: preferredRangeTargetId(nextAdjustment),
    lower: nextAdjustment?.lowerBound ?? null,
    upper: nextAdjustment?.upperBound ?? null
  })
}

const useAdjustmentAsPreference = (adjustment: ParameterAdjustment) => {
  const targetId = preferredRangeTargetId(adjustment)
  const existing = preferredRangeRows.value.find(row => row.targetId === targetId)

  if (existing) {
    existing.lower = adjustment.lowerBound
    existing.upper = adjustment.upperBound
  } else {
    addPreferenceRow(adjustment)
  }
}

const seedPreferenceRowsFromSuggestion = () => {
  const adjustments = parameterAdjustments.value.filter(adjustment => preferredRangeTargetId(adjustment))
  if (adjustments.length === 0) {
    ElMessage.warning(t('app.noParameterPreferenceTargets'))
    return
  }
  preferredRangeRows.value = adjustments.map(adj => ({
    id: newRangeRowId(),
    targetId: preferredRangeTargetId(adj),
    lower: adj.lowerBound,
    upper: adj.upperBound
  }))
}

const removePreferenceRow = (rowId: string) => {
  preferredRangeRows.value = preferredRangeRows.value.filter(row => row.id !== rowId)
}

// Fetch fault localization
const fetchFaultRules = async () => {
  if (!props.traceId) return

  const traceId = props.traceId
  const requestVersion = dialogRequestVersion
  faultLoading.value = true
  faultLoadFailed.value = false
  try {
    const result = await boardApi.getFaultRules(traceId)
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    faultLocalization.value = result
    faultRules.value = result.faultRules
  } catch (error: any) {
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    console.error('Failed to fetch fault rules:', error)
    faultLoadFailed.value = true
    ElMessage.error(fixResponseErrorMessage(error, t('app.failedToLoadFaultLocalization')))
  } finally {
    if (requestVersion === dialogRequestVersion && traceId === props.traceId) {
      faultLoading.value = false
    }
  }
}

// Fetch fix suggestions
const mergeFixResult = (current: FixResult | null, incoming: FixResult): FixResult => {
  if (!current) return incoming

  const incomingStrategies = new Set([
    ...(incoming.strategyAttempts || []).map(attempt => attempt.strategy),
    ...(incoming.suggestions || []).map(suggestion => suggestion.strategy)
  ])
  const suggestions = [
    ...(current.suggestions || []).filter(suggestion => !incomingStrategies.has(suggestion.strategy)),
    ...(incoming.suggestions || [])
  ]
  const strategyAttempts = [
    ...(current.strategyAttempts || []).filter(attempt => !incomingStrategies.has(attempt.strategy)),
    ...(incoming.strategyAttempts || [])
  ]

  return {
    ...current,
    ...incoming,
    faultRules: incoming.faultRules?.length ? incoming.faultRules : current.faultRules,
    suggestions,
    strategyAttempts,
    fixable: suggestions.some(suggestion => suggestion.verified),
    warnings: Array.from(new Set(strategyOrder.flatMap(strategy => strategyWarnings.value[strategy] || []))),
    unusedPreferredRangeSelections: incomingStrategies.has('parameter')
      ? incoming.unusedPreferredRangeSelections
      : current.unusedPreferredRangeSelections
  }
}

const invalidateStrategyResult = (strategy: FixStrategyName) => {
  if (!fixResult.value) return
  const suggestions = fixResult.value.suggestions.filter(item => item.strategy !== strategy)
  fixResult.value = {
    ...fixResult.value,
    suggestions,
    strategyAttempts: fixResult.value.strategyAttempts.filter(item => item.strategy !== strategy),
    fixable: suggestions.some(item => item.verified),
    warnings: Array.from(new Set(strategyOrder.flatMap(item => strategyWarnings.value[item] || []))),
    unusedPreferredRangeSelections: strategy === 'parameter'
      ? undefined
      : fixResult.value.unusedPreferredRangeSelections
  }
}

const fetchFixSuggestions = async (strategy: FixStrategyName = selectedStrategy.value) => {
  if (!props.traceId || strategyLoading.value) return

  const traceId = props.traceId
  const requestVersion = dialogRequestVersion
  const requestFingerprint = strategy === 'parameter' ? parameterPreferenceFingerprint() : null
  const preferredRangeSelections = strategy === 'parameter'
    ? buildPreferredRangeSelections()
    : undefined
  if (preferredRangeSelections === null) return
  delete strategyWarnings.value[strategy]
  invalidateStrategyResult(strategy)
  strategyLoading.value = strategy
  fixSearchElapsedSeconds.value = 0
  const requestId = crypto.randomUUID()
  const controller = new AbortController()
  const startedAt = Date.now()
  activeFixRequestId.value = requestId
  activeFixAbortController.value = controller
  if (fixSearchTimer) clearInterval(fixSearchTimer)
  fixSearchTimer = setInterval(() => {
    fixSearchElapsedSeconds.value = Math.floor((Date.now() - startedAt) / 1000)
  }, 1000)
  delete strategyErrors.value[strategy]
  try {
    if (strategy === 'parameter') {
      lastPreferredRangeSelections.value = preferredRangeSelections
    }
    const result = await boardApi.fixTrace(
      traceId,
      { strategies: [strategy], preferredRangeSelections },
      { requestId, signal: controller.signal }
    )
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    strategyWarnings.value[strategy] = result.warnings || []
    if (strategy === 'parameter') {
      const suggestion = result.suggestions.find(item => item.strategy === 'parameter')
      lastParameterRequestFingerprint.value = requestFingerprint
      if (suggestion?.parameterAdjustments?.length) {
        parameterAdjustmentCatalog.value = suggestion.parameterAdjustments
      }
    }
    fixResult.value = mergeFixResult(fixResult.value, result)
    if (result.faultRules?.length) faultRules.value = result.faultRules
  } catch (error: any) {
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    if (error?.name === 'CanceledError' || error?.code === 'ERR_CANCELED') return
    console.error('Failed to fetch fix suggestions:', error)
    strategyErrors.value[strategy] = fixResponseErrorMessage(error, t('app.failedToLoadFixSuggestions'))
    ElMessage.error(strategyErrors.value[strategy])
  } finally {
    if (requestVersion === dialogRequestVersion && traceId === props.traceId
      && strategyLoading.value === strategy) {
      strategyLoading.value = null
    }
    if (activeFixRequestId.value === requestId) activeFixRequestId.value = null
    if (activeFixAbortController.value === controller) activeFixAbortController.value = null
    if (fixSearchTimer) {
      clearInterval(fixSearchTimer)
      fixSearchTimer = null
    }
  }
}

const refreshWithPreferences = async () => {
  if (buildPreferredRangeSelections(true) === null) return
  await fetchFixSuggestions('parameter')
}

const clearPreferenceRows = async () => {
  preferredRangeRows.value = []
  await fetchFixSuggestions('parameter')
}

let dialogRequestVersion = 0

// Handle dialog open
const handleOpen = () => {
  dialogRequestVersion += 1
  fixResult.value = null
  faultLocalization.value = null
  faultRules.value = []
  faultLoadFailed.value = false
  strategyLoading.value = null
  strategyErrors.value = {}
  strategyWarnings.value = {}
  preferredRangeRows.value = []
  parameterAdjustmentCatalog.value = []
  lastParameterRequestFingerprint.value = null
  lastPreferredRangeSelections.value = undefined
  selectedStrategy.value = 'parameter'
  void fetchFaultRules()
}

// Switch strategy
const switchStrategy = (strategy: FixStrategyName) => {
  selectedStrategy.value = strategy
}

const trySelectedStrategy = () => fetchFixSuggestions(selectedStrategy.value)

// Apply the exact signed suggestion after the server checks the complete formal-model snapshot.
const applyFix = async (suggestion: FixSuggestion) => {
  if (!props.traceId) return
  if (!suggestion.verified) {
    ElMessage.warning(t('app.unverifiedFixCannotApply'))
    return
  }
  if (suggestion.strategy === 'remove') {
    try {
      await ElMessageBox.confirm(
        t('app.confirmRemoveRulesFix', { count: suggestion.removedRuleDescriptions?.length || 0 }),
        t('app.removeRulesFixTitle'),
        {
          confirmButtonText: t('app.removeRulesAndApply'),
          cancelButtonText: t('app.cancel'),
          type: 'warning'
        }
      )
    } catch {
      return
    }
  }
  applyingFix.value = true
  try {
    const result = await boardApi.applyFix(
      props.traceId,
      suggestion,
      suggestion.strategy === 'parameter' ? lastPreferredRangeSelections.value : undefined
    )
    if (!result.applied || (!result.verificationRechecked && !result.verificationEvidenceReused)) {
      ElMessage.warning(localizedTextOrFallback(result.message, t('app.failedToApplyFix'), locale.value))
      return
    }
    ElMessage.success(t('app.fixAppliedSuccessfully'))
    emit('applied', result)
    emit('update:visible', false)
  } catch (error: any) {
    console.error('Failed to apply fix:', error)
    const status = Number(error?.response?.status)
    const definitiveRejection = Number.isFinite(status) && status >= 400 && status < 500
    if (!definitiveRejection) {
      emit('outcome-uncertain')
      emit('update:visible', false)
      return
    }
    // Board drift and invalid/stale targets are definitive 4xx rejections with a user-facing reason.
    ElMessage.error(fixApplyErrorMessage(error))
  } finally {
    applyingFix.value = false
  }
}

// Current strategy suggestion
const currentSuggestion = computed(() => {
  if (!fixResult.value) return null
  const suggestion = fixResult.value.suggestions.find(s => s.strategy === selectedStrategy.value)
  return suggestion && suggestionIsCurrent(suggestion) ? suggestion : null
})

const currentStrategyAttempt = computed(() =>
  fixResult.value?.strategyAttempts?.find(attempt => attempt.strategy === selectedStrategy.value) ?? null
)

const localizedFaultLocalizationSummary = computed(() => {
  if (!faultLocalization.value) return ''
  return faultRules.value.length > 0
    ? t('app.faultLocalizationScopeCaveat')
    : t('app.faultLocalizationNoRuleCaveat')
})

const strategyAttemptStatusLabel = (status?: FixStrategyAttemptStatus) => {
  if (!status) return ''
  return t(`app.fixAttemptStatus.${status}`)
}

const strategyAttemptReasonLabel = (status?: FixStrategyAttemptStatus) => {
  if (!status) return ''
  return t(`app.fixAttemptReason.${status}`)
}

// A completed strategy with no verified proposal is different from a strategy
// that was never run. Keep the empty state explicit so users do not read it as
// a loading or transport failure.
const strategyAttemptOutcomeTitle = (attempt: FixStrategyAttempt | null) => {
  if (!attempt) return t('app.noFixSuggestionsForStrategy')
  if (attempt.status === 'NO_VERIFIED_SUGGESTION') {
    return attempt.strategy === 'condition'
      ? t('app.conditionFixNoVerifiedSuggestion')
      : t('app.noVerifiedFixSuggestion')
  }
  if (attempt.status === 'NOT_VERIFIED') return t('app.fixSuggestionNotVerifiedTitle')
  if (attempt.status === 'TIMED_OUT' || attempt.status === 'SKIPPED_TIMEOUT') {
    return t('app.fixStrategyTimedOutTitle')
  }
  if (attempt.status.startsWith('SKIPPED_')) return t('app.fixStrategyNotRunTitle')
  return t('app.noFixSuggestionsForStrategy')
}

const strategyAttemptOutcomeDetail = (attempt: FixStrategyAttempt | null) => {
  if (!attempt) return ''
  if (attempt.strategy === 'condition' && attempt.status === 'NO_VERIFIED_SUGGESTION') {
    return t('app.conditionFixNoVerifiedSuggestionDetail')
  }
  return strategyAttemptReasonLabel(attempt.status)
}

// Get verified strategies count
const verifiedCount = computed(() => {
  if (!fixResult.value) return 0
  return fixResult.value.suggestions.filter(s => s.verified && suggestionIsCurrent(s)).length
})

const getFaultRuleReason = (rule: FaultRule) => {
  if (rule.reasonCode === 'CONFLICTING_END_STATES'
    && rule.conflictingRuleString
    && rule.targetEndState
    && rule.conflictingEndState) {
    return t('app.faultRuleConflictReason', {
      rule: rule.conflictingRuleString,
      device: rule.targetDeviceLabel,
      first: rule.targetEndState,
      second: rule.conflictingEndState
    })
  }
  if (rule.reasonCode === 'TRIGGERED') {
    return t('app.faultRuleTriggeredReason', {
      transition: rule.transitionNumber,
      action: rule.targetActionLabel,
      device: rule.targetDeviceLabel
    })
  }
  return rule.reason
}

const getConditionActionLabel = (action?: string) => {
  if (action === 'remove') return t('app.remove')
  if (action === 'add') return t('app.add')
  if (action === 'keep') return t('app.keep')
  return action || ''
}

const formatConditionAdjustment = (adjustment: NonNullable<FixSuggestion['conditionAdjustments']>[number]) => {
  const device = adjustment.deviceLabel || t('app.unknownModelItem')
  const condition = [
    `${device}.${adjustment.attribute}`,
    adjustment.relation,
    adjustment.value
  ].filter(Boolean).join(' ')
  const rule = adjustment.ruleDescription || t('app.affectedRule')
  if (adjustment.action === 'add') {
    return t('app.addConditionAdjustment', { condition, rule })
  }
  if (adjustment.action === 'remove') {
    return t('app.removeConditionAdjustment', { condition, rule })
  }
  return adjustment.description
}

// Watch visible prop
watch(() => props.visible, (val) => {
  if (val) {
    handleOpen()
  }
}, { immediate: true })

// Close dialog
const closeDialog = () => {
  if (applyingFix.value) {
    ElMessage.warning(t('app.fixApplyStillRunning'))
    return
  }
  if (activeFixRequestId.value) {
    void boardApi.cancelFixRequest(activeFixRequestId.value)
    activeFixRequestId.value = null
  }
  activeFixAbortController.value?.abort()
  activeFixAbortController.value = null
  strategyLoading.value = null
  if (fixSearchTimer) {
    clearInterval(fixSearchTimer)
    fixSearchTimer = null
  }
  dialogRequestVersion += 1
  emit('update:visible', false)
}

const isDialogOpen = computed(() => props.visible)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, closeDialog)
</script>

<template>
  <!-- Fix Result Dialog - Following Verification Result Style -->
  <div
    v-if="visible"
    data-testid="fix-result-dialog"
    class="fixed inset-0 z-[2500] bg-black/60 backdrop-blur-sm flex items-center justify-center"
    @click="closeDialog"
    @keydown="handleModalKeydown"
  >
    <div
      :ref="setDialogRef"
      class="min-h-0 max-h-[85vh] w-[800px] max-w-[95vw] overflow-hidden rounded-2xl border border-slate-200 bg-white shadow-2xl flex flex-col"
      role="dialog"
      aria-modal="true"
      aria-labelledby="fix-result-dialog-title"
      tabindex="-1"
      @click.stop
    >
      
      <!-- Header -->
      <div
        data-testid="fix-result-header"
        class="relative flex-shrink-0 overflow-hidden rounded-t-2xl border-b"
        :class="verifiedCount > 0
          ? 'bg-amber-50 border-amber-200'
          : hasAttemptResults
            ? 'bg-red-50 border-red-200'
            : 'bg-blue-50 border-blue-200'"
      >
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div
              class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm"
              :class="verifiedCount > 0 ? 'bg-amber-100' : hasAttemptResults ? 'bg-red-100' : 'bg-blue-100'"
            >
              <span
                class="material-symbols-outlined text-2xl"
                :class="verifiedCount > 0 ? 'text-amber-600' : hasAttemptResults ? 'text-red-600' : 'text-blue-600'"
                aria-hidden="true"
              >
                {{ strategyLoading ? 'progress_activity' : verifiedCount > 0 ? 'build' : hasAttemptResults ? 'search_off' : 'build' }}
              </span>
            </div>
            <div>
              <h3 id="fix-result-dialog-title" class="text-xl font-bold text-slate-800">{{ t('app.fixSuggestions') }}</h3>
              <p class="text-sm text-slate-600">{{ headerStatus }}</p>
            </div>
          </div>
          <button
            type="button"
            :disabled="applyingFix"
            @click="closeDialog"
            class="w-9 h-9 flex items-center justify-center rounded-lg text-slate-500 hover:text-slate-700 hover:bg-slate-200 transition-all disabled:cursor-not-allowed disabled:opacity-40"
            :aria-label="t('app.close')"
          >
            <span class="material-symbols-outlined text-xl" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Content -->
      <div data-testid="fix-result-scroll" class="min-h-0 flex-1 overflow-y-auto p-6">
        
        <div class="space-y-4">
          
          <!-- Violation Info Card -->
          <div class="p-5 rounded-xl bg-gradient-to-r from-red-50 to-orange-50 border border-red-200">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center bg-red-100">
                <span class="material-symbols-outlined text-red-600">warning</span>
              </div>
              <div class="flex-1">
                <span class="text-lg font-bold text-red-800">{{ t('app.violationDetected') }}</span>
                <div class="flex items-center gap-2 mt-1">
                  <span class="text-sm text-red-600">
                    {{ faultLoading
                      ? t('app.loadingFaultLocalization')
                      : t('app.faultRulesIdentified', { count: faultRules.length }) }}
                  </span>
                </div>
                <p v-if="localizedFaultLocalizationSummary" class="mt-2 text-xs leading-relaxed text-red-700">
                  {{ localizedFaultLocalizationSummary }}
                </p>
                <details v-if="fixResult?.violatedSpecId || violatedSpecId" class="mt-2 text-[11px] text-red-700/80">
                  <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                  <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                    <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                    <code class="break-all rounded bg-red-100/70 px-2 py-1 text-[11px] text-red-800">{{ fixResult?.violatedSpecId || violatedSpecId }}</code>
                  </div>
                </details>
              </div>
            </div>
            <p class="text-sm text-red-700 mt-3 ml-13">
              {{ fixResult ? t('app.fixResultsRemainAdvisory') : t('app.fixAdvisoryBeforeRun') }}
            </p>
          </div>

          <div
            v-if="localizedFixLimitations.length || displayedFixWarnings.length || displayedSourceGenerationIssues.length"
            class="rounded-xl border border-amber-200 bg-amber-50 p-4 text-sm text-amber-800"
          >
            <div class="mb-2 flex items-center gap-2 font-bold">
              <span class="material-symbols-outlined text-lg">warning</span>
              {{ t('app.fixLimitations') }}
            </div>
            <ul v-if="localizedFixLimitations.length || displayedSourceGenerationIssues.length" class="list-disc space-y-1 pl-5">
              <li v-for="warning in localizedFixLimitations" :key="warning">{{ warning }}</li>
              <li
                v-for="issue in displayedSourceGenerationIssues"
                :key="`${issue.issueType}:${issue.itemLabel}:${issue.reasonCode}`"
              >
                <strong>{{ issue.itemLabel }}</strong>: {{ t(generationIssueReasonKey(issue)) }}
              </li>
            </ul>
            <details v-if="displayedFixWarnings.length" class="mt-3 text-xs text-amber-800/80">
              <summary class="cursor-pointer font-semibold">{{ t('app.fixTechnicalDiagnostics') }}</summary>
              <ul class="mt-2 list-disc space-y-1 pl-5 font-mono text-[11px]">
                <li v-for="warning in displayedFixWarnings" :key="warning">{{ warning }}</li>
              </ul>
            </details>
          </div>

          <!-- Strategy Tabs -->
          <div class="border border-slate-200 rounded-xl overflow-hidden">
            <div class="bg-slate-50 px-4 py-3 border-b border-slate-200">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-slate-600">tune</span>
                <span class="font-bold text-slate-800">{{ t('app.fixStrategies') }}</span>
              </div>
            </div>
            
            <div class="p-4">
              <!-- Strategy Buttons -->
              <div class="flex gap-2 mb-4">
                <button
                  v-for="option in strategyOptions"
                  :key="option.value"
                  type="button"
                  :data-testid="`fix-strategy-${option.value}`"
                  @click="switchStrategy(option.value)"
                  :aria-pressed="selectedStrategy === option.value"
                  class="flex-1 px-4 py-3 rounded-lg font-medium text-sm transition-all flex items-center justify-center gap-2"
                  :class="selectedStrategy === option.value
                    ? 'bg-blue-500 text-white shadow-md' 
                    : 'bg-slate-100 text-slate-600 hover:bg-slate-200'"
                >
                  <span class="material-symbols-outlined text-lg" aria-hidden="true">
                    {{ option.icon }}
                  </span>
                  {{ option.label }}
                  <span
                    v-if="fixResult?.suggestions.some(s => s.strategy === option.value && s.verified && suggestionIsCurrent(s))"
                    class="material-symbols-outlined text-sm"
                  >verified</span>
                </button>
              </div>

              <!-- Strategy Description -->
              <div class="text-sm text-slate-500 mb-4 pl-1">
                {{ strategyDescriptions[selectedStrategy] }}
                <div
                  v-if="currentStrategyAttempt"
                  class="mt-2 rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs text-slate-700"
                >
                  <span class="font-bold">{{ strategyAttemptStatusLabel(currentStrategyAttempt.status) }}</span>
                  <span class="ml-1">{{ strategyAttemptReasonLabel(currentStrategyAttempt.status) }}</span>
                </div>
              </div>

              <div
                v-if="currentStrategyLoading"
                data-testid="fix-strategy-loading"
                class="mb-4 rounded-lg border border-blue-200 bg-blue-50 px-4 py-3 text-sm text-blue-800"
              >
                <div class="flex items-center gap-2 font-semibold">
                  <span class="material-symbols-outlined animate-spin text-lg" aria-hidden="true">progress_activity</span>
                  {{ t('app.tryingFixStrategy', { strategy: strategyLabels[selectedStrategy] }) }}
                </div>
                <p class="mt-1 text-xs text-blue-700">{{ t('app.fixAttemptDoesNotApply') }}</p>
                <p class="mt-1 text-xs text-blue-700">
                  {{ t('app.fixSearchProgress', { seconds: fixSearchElapsedSeconds }) }}
                </p>
              </div>
              <div
                v-else-if="anotherStrategyLoading"
                class="mb-4 rounded-lg border border-slate-200 bg-slate-50 px-4 py-3 text-xs text-slate-600"
              >
                {{ t('app.anotherFixStrategyRunning', { strategy: strategyLabels[strategyLoading!] }) }}
              </div>

              <!-- Preferred Ranges -->
              <div
                v-if="selectedStrategy === 'parameter' && parameterAdjustments.length"
                class="border border-slate-200 rounded-lg overflow-hidden mb-4"
              >
                <div class="bg-slate-50 px-3 py-2 border-b border-slate-200 flex items-center gap-2">
                  <span class="material-symbols-outlined text-slate-600 text-lg">speed</span>
                  <span class="font-bold text-sm text-slate-800">{{ t('app.parameterPreferences') }}</span>
                  <span
                    v-if="activePreferredRangeCount"
                    class="ml-auto px-2 py-0.5 bg-blue-100 text-blue-700 text-xs rounded-full"
                  >{{ activePreferredRangeCount }} {{ t('app.active') }}</span>
                </div>
                <div class="p-3 space-y-3">
                  <div v-if="preferredRangeRows.length" class="space-y-2">
                    <div
                      v-for="row in preferredRangeRows"
                      :key="row.id"
                      class="grid grid-cols-1 sm:grid-cols-[minmax(0,1.6fr)_1fr_1fr_36px] gap-2 items-end"
                    >
                      <label class="text-xs font-medium text-slate-600">
                        {{ t('app.preferredRangeTarget') }}
                        <select
                          v-model="row.targetId"
                          class="mt-1 w-full rounded-md border border-slate-300 px-2 py-1.5 text-sm text-slate-800 focus:border-blue-400 focus:outline-none"
                        >
                          <option value="" disabled>{{ t('app.selectPreferredRangeTarget') }}</option>
                          <option
                            v-for="option in preferredRangeTargetOptions"
                            :key="option.value"
                            :value="option.value"
                          >
                            {{ option.label }}
                          </option>
                        </select>
                      </label>
                      <label class="text-xs font-medium text-slate-600">
                        {{ t('app.lowerBound') }}
                        <input
                          v-model.number="row.lower"
                          type="number"
                          class="mt-1 w-full rounded-md border border-slate-300 px-2 py-1.5 text-sm text-slate-800 focus:border-blue-400 focus:outline-none"
                        />
                      </label>
                      <label class="text-xs font-medium text-slate-600">
                        {{ t('app.upperBound') }}
                        <input
                          v-model.number="row.upper"
                          type="number"
                          class="mt-1 w-full rounded-md border border-slate-300 px-2 py-1.5 text-sm text-slate-800 focus:border-blue-400 focus:outline-none"
                        />
                      </label>
                      <button
                        type="button"
                        :title="t('app.removePreference')"
                        :aria-label="t('app.removePreference')"
                        @click="removePreferenceRow(row.id)"
                        class="w-9 h-9 rounded-md bg-slate-100 hover:bg-red-100 text-slate-500 hover:text-red-600 flex items-center justify-center transition-colors"
                      >
                        <span class="material-symbols-outlined text-lg" aria-hidden="true">delete</span>
                      </button>
                    </div>
                  </div>
                  <div
                    v-else-if="preferredRangeTargetOptions.length === 0"
                    class="rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs text-slate-500"
                  >
                    {{ t('app.noParameterPreferenceTargets') }}
                  </div>

                  <div
                    v-if="fixResult?.unusedPreferredRangeSelections?.length"
                    class="rounded-md border border-amber-200 bg-amber-50 px-3 py-2 text-xs text-amber-700"
                  >
                    {{ t('app.unusedPreferencesDetail', { count: fixResult.unusedPreferredRangeSelections.length }) }}
                  </div>

                  <div class="flex flex-wrap gap-2">
                    <button
                      type="button"
                      data-testid="fix-use-current-preferences"
                      @click="seedPreferenceRowsFromSuggestion"
                      :disabled="preferredRangeTargetOptions.length === 0"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors disabled:cursor-not-allowed disabled:opacity-50"
                    >
                      <span class="material-symbols-outlined text-base">playlist_add</span>
                      {{ t('app.useCurrent') }}
                    </button>
                    <button
                      type="button"
                      @click="addPreferenceRow()"
                      :disabled="preferredRangeTargetOptions.length === 0"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors disabled:cursor-not-allowed disabled:opacity-50"
                    >
                      <span class="material-symbols-outlined text-base">add</span>
                      {{ t('app.add') }}
                    </button>
                    <button
                      type="button"
                      data-testid="fix-run-with-preferences"
                      @click="refreshWithPreferences"
                      class="px-3 py-2 rounded-md bg-blue-500 hover:bg-blue-600 text-white text-sm font-bold flex items-center gap-1 transition-colors"
                    >
                      <span class="material-symbols-outlined text-base">refresh</span>
                      {{ t('app.runWithPreferences') }}
                    </button>
                    <button
                      v-if="preferredRangeRows.length || activePreferredRangeCount"
                      type="button"
                      @click="clearPreferenceRows"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors"
                    >
                      <span class="material-symbols-outlined text-base">restart_alt</span>
                      {{ t('app.reset') }}
                    </button>
                  </div>
                </div>
              </div>

              <!-- Current Suggestion -->
              <div v-if="currentSuggestion">
                
                <!-- Status Card -->
                <div class="p-4 rounded-xl mb-4" :class="currentSuggestion.verified 
                  ? 'bg-gradient-to-r from-green-50 to-emerald-50 border border-green-200' 
                  : 'bg-gradient-to-r from-red-50 to-orange-50 border border-red-200'">
                  <div class="flex items-center gap-3">
                    <div class="w-10 h-10 rounded-xl flex items-center justify-center" :class="currentSuggestion.verified ? 'bg-green-100' : 'bg-red-100'">
                      <span class="material-symbols-outlined" :class="currentSuggestion.verified ? 'text-green-600' : 'text-red-600'">
                        {{ currentSuggestion.verified ? 'verified' : 'cancel' }}
                      </span>
                    </div>
                    <div class="flex-1">
                      <span class="font-bold" :class="currentSuggestion.verified ? 'text-green-800' : 'text-red-800'">
                        {{ currentSuggestion.verified ? t('app.verifiedSolution') : t('app.notVerified') }}
                      </span>
                      <p class="text-sm" :class="currentSuggestion.verified ? 'text-green-600' : 'text-red-600'">
                        {{ strategyDescriptions[currentSuggestion.strategy] }}
                      </p>
                    </div>
                  </div>
                </div>

                <!-- Parameter Adjustments -->
                <div v-if="currentSuggestion.parameterAdjustments?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700">
                    <span class="material-symbols-outlined text-blue-500">tune</span>
                    {{ t('app.parameterAdjustments') }} ({{ currentSuggestion.parameterAdjustments.length }})
                  </div>
                  <div class="space-y-2">
                    <div
                      v-for="(adj, idx) in currentSuggestion.parameterAdjustments"
                      :key="idx"
                      class="bg-blue-50 border border-blue-200 rounded-lg p-3"
                    >
                      <div class="flex items-center justify-between">
                        <div class="min-w-0 flex items-center gap-2">
                          <span
                            class="max-w-[14rem] truncate px-2 py-0.5 bg-blue-500 text-white text-xs rounded font-bold"
                            :title="formatPreferredRangeTarget(adj)"
                          >{{ formatPreferredRangeTarget(adj) }}</span>
                          <code class="min-w-0 truncate text-sm font-mono text-slate-700" :title="`${adj.attribute} ${adj.relation}`">{{ adj.attribute }} {{ adj.relation }}</code>
                        </div>
                        <div class="flex items-center gap-2">
                          <span class="text-xs text-slate-500">{{ t('app.rangeLabel') }}: [{{ adj.lowerBound }}, {{ adj.upperBound }}]</span>
                          <button
                            type="button"
                            @click="useAdjustmentAsPreference(adj)"
                            class="px-2 py-1 rounded bg-white border border-blue-200 text-blue-700 hover:bg-blue-100 text-xs font-medium transition-colors"
                          >
                            {{ t('app.prefer') }}
                          </button>
                        </div>
                      </div>
                      <div class="flex items-center gap-2 mt-2">
                        <span class="px-2 py-1 bg-red-100 text-red-700 rounded font-mono text-sm line-through">{{ adj.originalValue }}</span>
                        <span class="material-symbols-outlined text-slate-400">arrow_forward</span>
                        <span class="px-2 py-1 bg-green-100 text-green-700 rounded font-mono text-sm">{{ adj.newValue }}</span>
                      </div>
                    </div>
                  </div>
                </div>

                <!-- Condition Adjustments -->
                <div v-if="currentSuggestion.conditionAdjustments?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700">
                    <span class="material-symbols-outlined text-emerald-500">checklist</span>
                    {{ t('app.conditionAdjustments') }} ({{ currentSuggestion.conditionAdjustments.length }})
                  </div>
                  <div class="space-y-2">
                    <div
                      v-for="(adj, idx) in currentSuggestion.conditionAdjustments"
                      :key="idx"
                      class="bg-emerald-50 border border-emerald-200 rounded-lg p-3 flex items-center gap-3"
                    >
                      <div 
                        class="w-8 h-8 rounded-lg flex items-center justify-center"
                        :class="adj.action === 'remove' ? 'bg-red-100' : adj.action === 'add' ? 'bg-emerald-100' : 'bg-slate-100'"
                      >
                        <span class="material-symbols-outlined text-sm" :class="adj.action === 'remove' ? 'text-red-600' : adj.action === 'add' ? 'text-emerald-600' : 'text-slate-600'">
                          {{ adj.action === 'remove' ? 'remove' : adj.action === 'add' ? 'add' : 'check' }}
                        </span>
                      </div>
                      <div class="flex-1">
                        <span class="text-sm font-medium text-slate-700">{{ formatConditionAdjustment(adj) }}</span>
                      </div>
                      <span 
                        class="px-2 py-0.5 rounded text-xs font-medium"
                        :class="adj.action === 'remove' ? 'bg-red-100 text-red-700' : adj.action === 'add' ? 'bg-emerald-100 text-emerald-700' : 'bg-slate-100 text-slate-600'"
                      >
                        {{ getConditionActionLabel(adj.action) }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Disabled Rules -->
                <div v-if="currentSuggestion.removedRuleDescriptions?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700">
                    <span class="material-symbols-outlined text-orange-500">block</span>
                    {{ t('app.rulesToRemove') }} ({{ currentSuggestion.removedRuleDescriptions.length }})
                  </div>
                  <div class="bg-orange-50 border border-orange-200 rounded-lg p-3">
                    <div class="space-y-2">
                      <span 
                        v-for="description in currentSuggestion.removedRuleDescriptions"
                        :key="description"
                        class="block rounded-lg bg-orange-500 px-3 py-1 text-sm font-medium text-white"
                      >
                        {{ description }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Apply Button -->
                <div v-if="currentSuggestion.verified" class="pt-4 border-t border-slate-200">
                  <button 
                    data-testid="fix-apply-current"
                    class="w-full py-3 rounded-lg font-bold text-base transition-all flex items-center justify-center gap-2"
                    :class="applyingFix || strategyLoading
                      ? 'bg-slate-300 text-slate-500 cursor-not-allowed' 
                      : currentSuggestion.strategy === 'remove'
                        ? 'bg-red-600 hover:bg-red-700 text-white shadow-md hover:shadow-lg'
                        : 'bg-green-500 hover:bg-green-600 text-white shadow-md hover:shadow-lg'"
                    :disabled="applyingFix || strategyLoading !== null"
                    @click="applyFix(currentSuggestion)"
                  >
                    <span v-if="!applyingFix" class="material-symbols-outlined">check_circle</span>
                    <div v-else class="animate-spin rounded-full h-5 w-5 border-2 border-white border-t-transparent"></div>
                    {{ applyingFix
                      ? t('app.applying')
                      : currentSuggestion.strategy === 'remove'
                        ? t('app.removeRulesAndApply')
                        : t('app.applyThisFix') }}
                  </button>
                </div>
                <div v-else class="pt-4 border-t border-slate-200 text-center">
                  <div class="flex items-center justify-center gap-2 text-red-600">
                    <span class="material-symbols-outlined">info</span>
                    <span class="font-medium">{{ t('app.solutionNotVerified') }}</span>
                  </div>
                  <p class="text-xs text-red-500 mt-1">{{ t('app.tryAnotherStrategy') }}</p>
                </div>
              </div>

              <div v-else-if="strategyErrors[selectedStrategy]" class="rounded-lg border border-red-200 bg-red-50 px-4 py-4 text-red-700">
                <div class="flex items-start gap-2">
                  <span class="material-symbols-outlined text-lg" aria-hidden="true">error</span>
                  <div>
                    <p class="font-semibold">{{ t('app.fixStrategyRequestFailed') }}</p>
                    <p class="mt-1 text-xs">{{ strategyErrors[selectedStrategy] }}</p>
                  </div>
                </div>
              </div>

              <div
                v-else-if="selectedStrategy === 'parameter' && parameterPreferencesChanged"
                data-testid="fix-parameter-preferences-stale"
                class="rounded-lg border border-amber-200 bg-amber-50 px-4 py-4 text-amber-800"
              >
                <div class="flex items-start gap-2">
                  <span class="material-symbols-outlined text-lg" aria-hidden="true">edit_note</span>
                  <div>
                    <p class="font-semibold">{{ t('app.parameterPreferencesChanged') }}</p>
                    <p class="mt-1 text-xs">{{ t('app.parameterPreferencesRequireRetry') }}</p>
                  </div>
                </div>
              </div>

              <div v-else-if="currentStrategyAttempt" class="text-center py-8 text-slate-500">
                <span class="material-symbols-outlined text-4xl mb-2 block">help</span>
                <p>{{ strategyAttemptOutcomeTitle(currentStrategyAttempt) }}</p>
                <p class="mx-auto mt-2 max-w-lg text-xs text-slate-500">
                  {{ strategyAttemptOutcomeDetail(currentStrategyAttempt) }}
                </p>
              </div>

              <div v-else-if="!currentStrategyLoading" class="rounded-lg border border-dashed border-slate-300 bg-slate-50 px-4 py-5 text-center text-slate-600">
                <span class="material-symbols-outlined mb-2 block text-3xl text-slate-400" aria-hidden="true">science</span>
                <p class="font-semibold">{{ t('app.fixStrategyNotTried') }}</p>
                <p class="mt-1 text-xs text-slate-500">{{ t('app.fixAttemptDoesNotApply') }}</p>
              </div>

              <button
                v-if="!currentSuggestion?.verified"
                type="button"
                data-testid="fix-try-current"
                :disabled="strategyLoading !== null"
                @click="trySelectedStrategy"
                class="mt-4 flex w-full items-center justify-center gap-2 rounded-lg bg-blue-600 px-4 py-3 text-sm font-bold text-white transition-colors hover:bg-blue-700 disabled:cursor-not-allowed disabled:bg-slate-300"
              >
                <span class="material-symbols-outlined text-lg" aria-hidden="true">science</span>
                {{ currentStrategyAttempt || strategyErrors[selectedStrategy]
                  ? t('app.retryFixStrategy')
                  : t('app.tryFixStrategy') }}
              </button>
            </div>
          </div>

          <!-- Fault Rules Section -->
          <div class="border border-slate-200 rounded-xl overflow-hidden">
            <div class="bg-slate-50 px-4 py-3 border-b border-slate-200">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-slate-600">search</span>
                <span class="font-bold text-slate-800">{{ t('app.faultLocalization') }}</span>
                <span class="ml-auto px-2 py-0.5 bg-red-100 text-red-700 text-xs rounded-full">{{ t('app.rulesCount', { count: faultRules.length }) }}</span>
              </div>
            </div>
            
            <div class="p-4">
              <div v-if="faultLoading" class="flex items-center justify-center gap-2 py-8 text-sm text-slate-500">
                <span class="material-symbols-outlined animate-spin" aria-hidden="true">progress_activity</span>
                {{ t('app.loadingFaultLocalization') }}
              </div>
              <div v-else-if="faultLoadFailed" class="text-center py-8 text-red-600">
                <span class="material-symbols-outlined text-3xl" aria-hidden="true">error</span>
                <p class="mt-2 text-sm font-medium">{{ t('app.failedToLoadFaultLocalization') }}</p>
              </div>
              <div v-else-if="faultRules.length === 0" class="text-center py-8 text-slate-400">
                <span class="material-symbols-outlined text-4xl mb-2 block">check_circle</span>
                <p>{{ t('app.noFaultRulesFound') }}</p>
                <p class="text-xs mt-1">{{ t('app.violationMayBeDeviceTransitions') }}</p>
              </div>
              
              <div v-else class="space-y-2">
                <div 
                  v-for="(rule, idx) in faultRules"
                  :key="idx"
                  class="border border-slate-200 rounded-lg p-3 hover:bg-slate-50 transition-colors"
                  :class="{ 'border-orange-300 bg-orange-50/50': rule.conflicting }"
                >
                  <div class="flex items-center justify-between mb-2">
                    <div class="flex items-center gap-2">
                      <span class="w-6 h-6 bg-blue-500 text-white rounded flex items-center justify-center text-xs font-bold">{{ idx + 1 }}</span>
                      <code class="text-xs bg-slate-100 px-2 py-1 rounded font-mono">{{ rule.ruleString }}</code>
                    </div>
                    <span v-if="rule.conflicting" class="px-2 py-0.5 bg-orange-100 text-orange-700 text-xs rounded flex items-center gap-1">
                      <span class="material-symbols-outlined text-xs">warning</span>
                      {{ t('app.conflicts') }}
                    </span>
                  </div>
                  <div class="grid grid-cols-1 gap-2 text-xs text-slate-600 sm:grid-cols-3">
                    <div>{{ t('app.transitionNumberLabel') }}: <span class="font-medium">{{ rule.transitionNumber }}</span></div>
                    <div>{{ t('app.device') }}: <span class="font-medium">{{ rule.targetDeviceLabel }}</span></div>
                    <div>{{ t('app.action') }}: <span class="font-medium">{{ rule.targetActionLabel }}</span></div>
                  </div>
                  <div v-if="rule.reason" class="mt-2 text-xs text-slate-500 flex items-start gap-1">
                    <span class="material-symbols-outlined text-xs mt-0.5">info</span>
                    {{ getFaultRuleReason(rule) }}
                  </div>
                </div>
              </div>
            </div>
          </div>

          <!-- Other Strategies -->
          <div v-if="(fixResult?.suggestions.length || 0) > 1" class="border border-slate-200 rounded-xl p-4">
            <div class="text-sm font-bold text-slate-700 mb-3 flex items-center gap-2">
              <span class="material-symbols-outlined text-slate-600">layers</span>
              {{ t('app.otherAvailableStrategies') }}
            </div>
            <div class="flex flex-wrap gap-2">
              <button
                v-for="s in fixResult?.suggestions || []"
                :key="s.strategy"
                v-show="s.strategy !== selectedStrategy"
                @click="switchStrategy(s.strategy)"
                class="px-4 py-2 rounded-lg text-sm font-medium transition-colors flex items-center gap-2"
                :class="s.verified && suggestionIsCurrent(s)
                  ? 'bg-green-100 text-green-700 hover:bg-green-200 border border-green-300' 
                  : 'bg-slate-100 text-slate-600 hover:bg-slate-200 border border-slate-300'"
              >
                <span class="material-symbols-outlined text-sm">
                  {{ strategyIcons[s.strategy] }}
                </span>
                {{ strategyLabels[s.strategy] }}
                <span v-if="s.verified && suggestionIsCurrent(s)" class="material-symbols-outlined text-green-600 text-xs">verified</span>
              </button>
            </div>
          </div>

        </div>
      </div>

      <!-- Footer -->
      <div class="border-t border-slate-200 p-4 bg-slate-50 rounded-b-2xl">
        <div class="flex justify-end">
          <button 
            type="button"
            :disabled="applyingFix"
            @click="closeDialog"
            class="px-6 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg font-medium transition-colors flex items-center gap-2 disabled:cursor-not-allowed disabled:opacity-50"
          >
            <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
            {{ t('app.close') }}
          </button>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
/* Custom scrollbar */
:deep(.p-6::-webkit-scrollbar) {
  width: 8px;
}

:deep(.p-6::-webkit-scrollbar-track) {
  background: #f1f5f9;
  border-radius: 4px;
}

:deep(.p-6::-webkit-scrollbar-thumb) {
  background: #cbd5e1;
  border-radius: 4px;
}

:deep(.p-6::-webkit-scrollbar-thumb:hover) {
  background: #94a3b8;
}
</style>
