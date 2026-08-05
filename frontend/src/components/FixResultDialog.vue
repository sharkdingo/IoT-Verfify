<script setup lang="ts">
import { ref, computed, watch, onBeforeUnmount } from 'vue'
import { useI18n } from 'vue-i18n'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import boardApi from '@/api/board'
import { FIX_RESPONSE_INCOMPLETE_CODE } from '@/utils/fixResponse'
import { generationIssueReasonKey } from '@/utils/generationIssue'
import { localizedErrorMessage, localizedTextOrFallback } from '@/utils/userMessage'
import { requestInteractiveCancellation } from '@/utils/interactiveCancellation'
import { formatModelTokenBySource } from '@/utils/modelTokenDisplay'
import { useAuth } from '@/stores/auth'
import type {
  FaultLocalizationResult,
  FaultRule,
  FixApplyResult,
  FixResult,
  FixStrategyAttempt,
  FixStrategyAttemptStatus,
  FixStrategyName,
  FixSuggestion,
  ModelTokenSource,
  ParameterAdjustment,
  ParameterTarget,
  PreferredRangeSelection
} from '@/types/fix'
import type { InteractiveOperationStage } from '@/types/task'
import { confirmDestructive, notifyBlocked, notifyError, notifySuccess } from '@/utils/feedback'

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
const { getToken } = useAuth()

const faultLoading = ref(false)
const faultLoadFailed = ref(false)
const strategyLoading = ref<FixStrategyName | null>(null)
const fixSearchElapsedSeconds = ref(0)
const fixProgressStage = ref<InteractiveOperationStage>('QUEUED')
const activeFixRequestId = ref<string | null>(null)
const activeFixTraceId = ref<number | null>(null)
const activeFixAbortController = ref<AbortController | null>(null)
const activeFixAuthToken = ref<string | null>(null)
const pendingFixCancellationId = ref<string | null>(null)
const unresolvedFixRequestId = ref<string | null>(null)
const FIX_CANCELLATION_STATUS_FAILURE_LIMIT = 30
const FIX_CANCELLATION_RETRY_DELAY_MS = 50
const FIX_RECOVERY_BACKOFF_MS = 10_000
const FIX_PROGRESS_POLL_INTERVAL_MS = 1_000
// FINISHED is published just before the authoritative POST result leaves the worker. Release is
// deliberately a two-poll handshake: one poll records `observedAt`, a later poll releases only
// once this grace has elapsed — giving the in-flight POST body a full extra interval to arrive
// (and its own terminal evidence clears tracking the instant it does).
const FIX_FINISHED_POST_GRACE_MS = FIX_PROGRESS_POLL_INTERVAL_MS
let fixSearchTimer: ReturnType<typeof setInterval> | null = null
let fixProgressRefreshInFlight = false
let fixCancellationStatusFailures = 0
let fixRecoveryRetryNotBefore = 0
let fixFinishedObservation: { requestId: string, observedAt: number } | null = null
let fixOutcomeUnknownWarningRequestId: string | null = null
type FixRequestTerminalEvidence = 'post-terminal' | 'cancel-accepted' | 'status-finished'
let lastResolvedFixRequest: {
  requestId: string
  evidence: FixRequestTerminalEvidence
} | null = null
const strategyErrors = ref<Partial<Record<FixStrategyName, string>>>({})
const strategyWarnings = ref<Partial<Record<FixStrategyName, string[]>>>({})
const fixResult = ref<FixResult | null>(null)
const faultLocalization = ref<FaultLocalizationResult | null>(null)
const faultRules = ref<FaultRule[]>([])
const selectedStrategy = ref<FixStrategyName>('parameter')
const applyingFix = ref(false)
const parameterTargetCatalog = ref<ParameterTarget[]>([])
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

const fixProgressStageLabel = computed(() => t(`app.fixProgressStage_${fixProgressStage.value}`))

const waitForFixCancellationRetry = () => new Promise<void>(resolve => {
  setTimeout(resolve, FIX_CANCELLATION_RETRY_DELAY_MS)
})

const cancelOwnedFixRequest = (
  requestId: string,
  authToken: string | null = activeFixAuthToken.value
): Promise<boolean> => authToken
  ? boardApi.cancelFixRequest(requestId, authToken)
  : Promise.reject(new Error('Automatic-fix owner credential is unavailable'))

const readOwnedFixRequestStatus = (
  requestId: string,
  authToken: string | null = activeFixAuthToken.value
) => authToken
  ? boardApi.getFixRequestStatus(requestId, authToken)
  : Promise.reject(new Error('Automatic-fix owner credential is unavailable'))

const refreshFixProgress = async (requestId: string) => {
  if (fixProgressRefreshInFlight || Date.now() < fixRecoveryRetryNotBefore) return
  fixProgressRefreshInFlight = true
  try {
    if (activeFixRequestId.value === requestId && pendingFixCancellationId.value === requestId) {
      try {
        if (await cancelOwnedFixRequest(requestId)) {
          clearActiveFixTracking(requestId, 'cancel-accepted')
          return
        }
      } catch {
        // Keep polling: the request can become cancellable after POST registration.
      }
    }
    const status = await readOwnedFixRequestStatus(requestId)
    if (activeFixRequestId.value === requestId) {
      if (pendingFixCancellationId.value === requestId) fixCancellationStatusFailures = 0
      fixProgressStage.value = status.stage
      if (status.state === 'FINISHED') {
        const recoveringUnknownOutcome = pendingFixCancellationId.value === requestId
          || unresolvedFixRequestId.value === requestId
          || activeFixAbortController.value?.signal.aborted === true
        if (recoveringUnknownOutcome) {
          clearActiveFixTracking(requestId, 'status-finished')
        } else if (fixFinishedObservation?.requestId !== requestId) {
          // The backend publishes FINISHED immediately before the POST result leaves its worker.
          // Give that authoritative response one polling interval to arrive before treating it as hung.
          fixFinishedObservation = { requestId, observedAt: Date.now() }
        } else if (Date.now() - fixFinishedObservation.observedAt >= FIX_FINISHED_POST_GRACE_MS) {
          clearActiveFixTracking(requestId, 'status-finished')
        }
      } else if (fixFinishedObservation?.requestId === requestId) {
        fixFinishedObservation = null
      }
    }
  } catch {
    if (activeFixRequestId.value === requestId && pendingFixCancellationId.value === requestId) {
      fixCancellationStatusFailures += 1
      if (fixCancellationStatusFailures >= FIX_CANCELLATION_STATUS_FAILURE_LIMIT) {
        backOffFixCancellationRecovery(requestId)
      }
    }
    // Registration and completion can race with this read; only terminal evidence releases tracking.
  } finally {
    fixProgressRefreshInFlight = false
  }
}

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

const fixResponseErrorMessage = (error: any, fallback: string) => {
  if (error?.response?.status === 429
    && error?.response?.data?.data?.reasonCode === 'USER_FORMAL_OPERATION_BUSY') {
    return t('app.formalOperationBusy')
  }
  return error?.code === FIX_RESPONSE_INCOMPLETE_CODE
    ? t('app.fixResponseIncomplete')
    : localizedErrorMessage(error, fallback, locale.value)
}

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
    // Only UNAVAILABLE means a comparison was attempted and failed, so only it can be retried.
    // NOT_CHECKED is deliberately silent: the backend skips the comparison entirely when it has
    // already refused to search an incomplete source model, and that blocker is the message above.
    // Naming an unattempted comparison would invite a retry that cannot change the outcome.
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
  return parameterTargetCatalog.value
})

const preferredRangeTargetId = (adjustment: ParameterTarget) => adjustment.targetId

const formatModelToken = (value: unknown, source: ModelTokenSource) => {
  return formatModelTokenBySource(source, value, t)
}

const formatRelation = (value: unknown) => {
  const raw = String(value ?? '').trim()
  const normalized = raw.toLowerCase().replace(/_/g, ' ')
  const labels: Record<string, string> = {
    '=': t('app.relationEquals'),
    '==': t('app.relationEquals'),
    '!=': t('app.relationNotEquals'),
    '>': t('app.relationGreater'),
    '<': t('app.relationLess'),
    '>=': t('app.relationGreaterEqual'),
    '<=': t('app.relationLessEqual'),
    in: t('app.relationIn'),
    'not in': t('app.relationNotIn')
  }
  return labels[normalized] || raw
}

const formatPreferredRangeTarget = (adjustment: ParameterTarget) => t('app.preferredRangeTargetLabel', {
  description: t('app.parameterTargetFallback', {
    attribute: formatModelToken(adjustment.attribute, adjustment.modelTokenSource),
    relation: formatRelation(adjustment.relation),
    original: formatModelToken(adjustment.originalValue, adjustment.modelTokenSource)
  })
})

const preferredRangeTargetOptions = computed(() => parameterAdjustments.value.map(adjustment => ({
  value: preferredRangeTargetId(adjustment),
  label: formatPreferredRangeTarget(adjustment),
  adjustment
})).filter(option => option.value))

const parameterAdjustmentByTargetId = computed(() => {
  const byTargetId = new Map<string, ParameterTarget>()
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

const templateSnapshotAllowsApply = computed(() =>
  fixResult.value?.templateSnapshotComparison === 'UNCHANGED')

/**
 * Why Apply cannot proceed, as a standing precondition. Empty string means nothing blocks it.
 *
 * A disabled submit has to say why inline, and both the disabled state and the `aria-describedby`
 * target derive from this one value so they cannot disagree. Deliberately excludes in-flight work:
 * the button already renders "Applying…" with a spinner, and repeating that as an explanation would
 * be duplicate feedback for a state the user cannot act on. `applyDisabled` owns the union.
 */
const applyBlockedReason = computed(() => {
  if (fixResult.value?.templateSnapshotComparison === 'CHANGED') {
    return t('app.fixTemplateSnapshotChangedLimitation')
  }
  if (!templateSnapshotAllowsApply.value) return t('app.fixTemplateSnapshotUnavailableLimitation')
  return ''
})

/** Apply is unavailable while a precondition blocks it or while any fix request is in flight. */
const applyDisabled = computed(() =>
  Boolean(applyBlockedReason.value) || applyingFix.value || strategyLoading.value !== null)

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
      if (showWarnings) notifyBlocked(t('app.preferredRangeCompleteFields'))
      return null
    }

    const targetId = String(row.targetId)
    const lower = Number(row.lower)
    const upper = Number(row.upper)

    const adjustment = parameterAdjustmentByTargetId.value.get(targetId)
    if (!adjustment) {
      if (showWarnings) notifyBlocked(t('app.preferredRangeSelectTarget'))
      return null
    }
    if (!Number.isFinite(lower) || !Number.isFinite(upper) || !Number.isInteger(lower) || !Number.isInteger(upper)) {
      if (showWarnings) notifyBlocked(t('app.preferredRangeIntegerBounds'))
      return null
    }
    if (lower > upper) {
      if (showWarnings) notifyBlocked(t('app.preferredRangeLowerBeforeUpper'))
      return null
    }

    if (seen.has(targetId)) {
      if (showWarnings) notifyBlocked(t('app.duplicatePreferredRange', { key: preferredRangeTargetLabel(targetId) }))
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

const addPreferenceRow = (adjustment?: ParameterTarget) => {
  const nextAdjustment = adjustment ?? parameterAdjustments.value.find(adj => {
    const targetId = preferredRangeTargetId(adj)
    return targetId && !preferredRangeRows.value.some(row => row.targetId === targetId)
  })
  if (!nextAdjustment) {
    notifyBlocked(t('app.noParameterPreferenceTargets'))
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

const lockAdjustmentAtOriginal = (adjustment: ParameterAdjustment) => {
  const original = Number(adjustment.originalValue)
  if (!Number.isInteger(original)) {
    notifyBlocked(t('app.preferredRangeIntegerBounds'))
    return
  }
  useAdjustmentAsPreference(adjustment)
  const row = preferredRangeRows.value.find(item => item.targetId === preferredRangeTargetId(adjustment))
  if (row) {
    row.lower = original
    row.upper = original
  }
}

const seedPreferenceRowsFromSuggestion = () => {
  const adjustments = parameterAdjustments.value.filter(adjustment => preferredRangeTargetId(adjustment))
  if (adjustments.length === 0) {
    notifyBlocked(t('app.noParameterPreferenceTargets'))
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
    notifyError(fixResponseErrorMessage(error, t('app.failedToLoadFaultLocalization')))
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
      : current.unusedPreferredRangeSelections,
    parameterTargets: incomingStrategies.has('parameter')
      ? incoming.parameterTargets
      : current.parameterTargets
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
      ? []
      : fixResult.value.unusedPreferredRangeSelections
  }
}

const fetchFixSuggestions = async (strategy: FixStrategyName = selectedStrategy.value) => {
  if (!props.traceId || strategyLoading.value || activeFixRequestId.value || unresolvedFixRequestId.value) return

  const authToken = getToken()
  if (!authToken) {
    strategyErrors.value[strategy] = t('app.fixAuthenticationRequired')
    notifyError(strategyErrors.value[strategy])
    return
  }

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
  fixProgressStage.value = 'QUEUED'
  const requestId = crypto.randomUUID()
  const controller = new AbortController()
  const startedAt = Date.now()
  activeFixRequestId.value = requestId
  activeFixTraceId.value = traceId
  activeFixAbortController.value = controller
  activeFixAuthToken.value = authToken
  pendingFixCancellationId.value = null
  unresolvedFixRequestId.value = null
  fixCancellationStatusFailures = 0
  fixRecoveryRetryNotBefore = 0
  fixFinishedObservation = null
  fixOutcomeUnknownWarningRequestId = null
  lastResolvedFixRequest = null
  if (fixSearchTimer) clearInterval(fixSearchTimer)
  const requestProgressTimer = setInterval(() => {
    fixSearchElapsedSeconds.value = Math.floor((Date.now() - startedAt) / 1000)
    void refreshFixProgress(requestId)
  }, FIX_PROGRESS_POLL_INTERVAL_MS)
  fixSearchTimer = requestProgressTimer
  delete strategyErrors.value[strategy]
  let postSettledWithTerminalEvidence = false
  try {
    if (strategy === 'parameter') {
      lastPreferredRangeSelections.value = preferredRangeSelections
    }
    const result = await boardApi.fixTrace(
      traceId,
      { strategies: [strategy], preferredRangeSelections },
      { authToken, requestId, signal: controller.signal }
    )
    postSettledWithTerminalEvidence = true
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    strategyWarnings.value[strategy] = result.warnings || []
    if (strategy === 'parameter') {
      lastParameterRequestFingerprint.value = requestFingerprint
      parameterTargetCatalog.value = result.parameterTargets || []
    }
    fixResult.value = mergeFixResult(fixResult.value, result)
    if (result.faultRules?.length) faultRules.value = result.faultRules
  } catch (error: any) {
    postSettledWithTerminalEvidence = Boolean(error?.response)
      || error?.code === FIX_RESPONSE_INCOMPLETE_CODE
    if (!postSettledWithTerminalEvidence && activeFixRequestId.value === requestId) {
      beginUnknownFixRecovery(requestId)
    }
    if (requestVersion !== dialogRequestVersion || traceId !== props.traceId || !props.visible) return
    if (error?.name === 'CanceledError' || error?.code === 'ERR_CANCELED') return
    console.error('Failed to fetch fix suggestions:', error)
    strategyErrors.value[strategy] = fixResponseErrorMessage(error, t('app.failedToLoadFixSuggestions'))
    notifyError(strategyErrors.value[strategy])
  } finally {
    if (postSettledWithTerminalEvidence && activeFixRequestId.value === requestId) {
      clearActiveFixTracking(requestId, 'post-terminal')
    } else if (activeFixRequestId.value === requestId) {
      beginUnknownFixRecovery(requestId)
    }
    if (activeFixRequestId.value !== requestId) {
      if (activeFixRequestId.value === null
        && requestVersion === dialogRequestVersion && traceId === props.traceId
        && strategyLoading.value === strategy) {
        strategyLoading.value = null
      }
      if (activeFixAbortController.value === controller) activeFixAbortController.value = null
      if (fixSearchTimer === requestProgressTimer) {
        clearInterval(requestProgressTimer)
        fixSearchTimer = null
      }
    }
  }
}

const refreshWithPreferences = async () => {
  if (preferenceActionBlockedReason.value) return
  if (buildPreferredRangeSelections(true) === null) return
  await fetchFixSuggestions('parameter')
}

/**
 * Why the preference actions are unavailable, or '' when they are usable.
 *
 * One computed drives both the disabled state and the visible reason, so the button and the message
 * cannot disagree. Reset previously cleared the rows *before* `fetchFixSuggestions` silently
 * returned, so a click during an in-flight search destroyed the user's typed bounds and issued no
 * re-run — and the returning result was then hidden behind "preferences changed, re-run".
 */
const preferenceActionBlockedReason = computed(() => {
  if (strategyLoading.value) return t('app.fixSearchInProgress')
  if (activeFixRequestId.value || unresolvedFixRequestId.value) return t('app.fixSearchInProgress')
  return ''
})

const clearPreferenceRows = async () => {
  if (preferenceActionBlockedReason.value) return
  preferredRangeRows.value = []
  await fetchFixSuggestions('parameter')
}

let dialogRequestVersion = 0

// Handle dialog open
const handleOpen = () => {
  dialogRequestVersion += 1
  if (activeFixRequestId.value || unresolvedFixRequestId.value) {
    if (activeFixTraceId.value !== props.traceId) {
      notifyBlocked(t('app.fixTraceSwitchBlockedByActiveSearch'))
      emit('update:visible', false)
      return
    }
    void fetchFaultRules()
    return
  }
  fixResult.value = null
  faultLocalization.value = null
  faultRules.value = []
  faultLoadFailed.value = false
  strategyLoading.value = null
  strategyErrors.value = {}
  strategyWarnings.value = {}
  preferredRangeRows.value = []
  parameterTargetCatalog.value = []
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
    notifyBlocked(t('app.unverifiedFixCannotApply'))
    return
  }
  if (!templateSnapshotAllowsApply.value) {
    notifyBlocked(fixResult.value?.templateSnapshotComparison === 'CHANGED'
      ? t('app.fixTemplateSnapshotChangedLimitation')
      : t('app.fixTemplateSnapshotUnavailableLimitation'))
    return
  }
  if (suggestion.strategy === 'remove' && !await confirmDestructive({
    title: t('app.removeRulesFixTitle'),
    message: t('app.confirmRemoveRulesFix', { count: suggestion.removedRuleDescriptions?.length || 0 }),
    confirmText: t('app.removeRulesAndApply')
  })) return
  applyingFix.value = true
  try {
    const result = await boardApi.applyFix(
      props.traceId,
      suggestion,
      suggestion.strategy === 'parameter' ? lastPreferredRangeSelections.value : undefined
    )
    if (!result.applied || !result.verificationEvidenceReused) {
      notifyBlocked(localizedTextOrFallback(result.message, t('app.failedToApplyFix'), locale.value))
      return
    }
    notifySuccess(t('app.fixAppliedWithSignedEvidence'))
    emit('applied', result)
    emit('update:visible', false)
  } catch (error: any) {
    console.error('Failed to apply fix:', error)
    const status = Number(error?.response?.status)
    const reasonCode = error?.response?.data?.data?.reasonCode
    const definitiveRejection = Number.isFinite(status)
      && ((status >= 400 && status < 500)
        || (status === 503 && reasonCode === 'FIX_APPLY_PREFLIGHT_UNAVAILABLE'))
    if (!definitiveRejection) {
      emit('outcome-uncertain')
      emit('update:visible', false)
      return
    }
    // Drift, stale targets, and service-unavailable preflight failures occur before the write.
    notifyError(fixApplyErrorMessage(error))
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

const strategyAttemptProgress = (attempt: FixStrategyAttempt | null) => {
  if (!attempt || !Number.isInteger(attempt.attemptsUsed) || !Number.isInteger(attempt.attemptLimit)) {
    return ''
  }
  return t('app.fixAttemptProgress', {
    used: attempt.attemptsUsed,
    limit: attempt.attemptLimit
  })
}

const parameterAdjustmentMakesRuleUnreachable = (adjustment: ParameterAdjustment) => {
  const relation = adjustment.relation.trim().toLowerCase()
  const newValue = Number(adjustment.newValue)
  if (!Number.isSafeInteger(newValue)) return false
  return (['>', 'gt'].includes(relation) && newValue === adjustment.upperBound)
    || (['<', 'lt'].includes(relation) && newValue === adjustment.lowerBound)
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
  if (attempt.status === 'FAILED_MODEL_GENERATION') return t('app.fixStrategyGenerationFailedTitle')
  if (attempt.status === 'FAILED_SOLVER_EXECUTION') return t('app.fixStrategySolverFailedTitle')
  if (attempt.status === 'SEARCH_BUDGET_EXHAUSTED') return t('app.fixStrategyBudgetExhaustedTitle')
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
    && rule.targetEndState
    && rule.conflictingEndState) {
    return t('app.faultRuleConflictReason', {
      rule: rule.conflictingRuleString?.trim() || t('app.noDescription'),
      device: rule.targetDeviceLabel,
      first: formatModelToken(rule.targetEndState, rule.modelTokenSource),
      second: formatModelToken(rule.conflictingEndState, rule.modelTokenSource)
    })
  }
  if (rule.reasonCode === 'TRIGGERED') {
    return t('app.faultRuleTriggeredReason', {
      transition: rule.transitionNumber,
      action: formatModelToken(rule.targetActionLabel, rule.modelTokenSource),
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
    `${device}.${formatModelToken(adjustment.attribute, adjustment.modelTokenSource)}`,
    formatRelation(adjustment.relation),
    adjustment.value === undefined
      ? undefined
      : formatModelToken(adjustment.value, adjustment.modelTokenSource)
  ].filter(Boolean).join(' ')
  const rule = adjustment.ruleDescription || t('app.affectedRule')
  if (adjustment.action === 'add') {
    return t('app.addConditionAdjustment', { condition, rule })
  }
  if (adjustment.action === 'remove') {
    return t('app.removeConditionAdjustment', { condition, rule })
  }
  return t('app.keepConditionAdjustment', { condition, rule })
}

const clearActiveFixTracking = (
  requestId: string,
  evidence: FixRequestTerminalEvidence
) => {
  if (activeFixRequestId.value !== requestId) return
  lastResolvedFixRequest = { requestId, evidence }
  activeFixAbortController.value?.abort()
  activeFixAbortController.value = null
  activeFixRequestId.value = null
  activeFixTraceId.value = null
  activeFixAuthToken.value = null
  pendingFixCancellationId.value = null
  if (unresolvedFixRequestId.value === requestId) unresolvedFixRequestId.value = null
  fixCancellationStatusFailures = 0
  fixRecoveryRetryNotBefore = 0
  if (fixFinishedObservation?.requestId === requestId) fixFinishedObservation = null
  if (fixOutcomeUnknownWarningRequestId === requestId) fixOutcomeUnknownWarningRequestId = null
  strategyLoading.value = null
  if (fixSearchTimer) {
    clearInterval(fixSearchTimer)
    fixSearchTimer = null
  }
}

const warnFixOutcomeUnknown = (requestId: string) => {
  if (fixOutcomeUnknownWarningRequestId === requestId) return
  fixOutcomeUnknownWarningRequestId = requestId
  notifyBlocked(t('app.fixStopRequestMayStillBeRunning'))
}

const beginUnknownFixRecovery = (requestId: string) => {
  if (activeFixRequestId.value !== requestId) return
  unresolvedFixRequestId.value = requestId
  warnFixOutcomeUnknown(requestId)
  if (pendingFixCancellationId.value !== requestId) {
    void cancelActiveFixSearch()
  }
}

const backOffFixCancellationRecovery = (requestId: string) => {
  if (activeFixRequestId.value !== requestId) return
  unresolvedFixRequestId.value = requestId
  activeFixAbortController.value?.abort()
  fixCancellationStatusFailures = 0
  fixRecoveryRetryNotBefore = Date.now() + FIX_RECOVERY_BACKOFF_MS
  warnFixOutcomeUnknown(requestId)
}

const cancelActiveFixSearch = async () => {
  const requestId = activeFixRequestId.value
  if (!requestId || pendingFixCancellationId.value === requestId) return
  pendingFixCancellationId.value = requestId
  fixCancellationStatusFailures = 0
  fixProgressStage.value = 'CANCELLING'
  try {
    const accepted = await requestInteractiveCancellation({
      cancel: () => cancelOwnedFixRequest(requestId),
      waitBeforeRetry: waitForFixCancellationRetry,
      shouldContinue: () => activeFixRequestId.value === requestId
    })
    if (accepted) {
      clearActiveFixTracking(requestId, 'cancel-accepted')
      return
    }
    warnFixOutcomeUnknown(requestId)
    await refreshFixProgress(requestId)
  } catch (error) {
    // Keep the request id and progress polling alive until its terminal state is observed.
    console.warn(`[Fix] Failed to cancel automatic-fix request ${requestId}:`, error)
    warnFixOutcomeUnknown(requestId)
    await refreshFixProgress(requestId)
  }
}

const disposeActiveFixSearch = () => {
  const requestId = activeFixRequestId.value
  if (!requestId) return
  const controller = activeFixAbortController.value
  const authToken = activeFixAuthToken.value
  pendingFixCancellationId.value = requestId
  fixProgressStage.value = 'CANCELLING'
  if (fixSearchTimer) {
    clearInterval(fixSearchTimer)
    fixSearchTimer = null
  }
  void requestInteractiveCancellation({
    cancel: () => cancelOwnedFixRequest(requestId, authToken),
    waitBeforeRetry: () => new Promise<void>(resolve => setTimeout(resolve, 100)),
    shouldContinue: () => activeFixRequestId.value === requestId,
    maxAttempts: 20
  }).then(accepted => {
    if (accepted) clearActiveFixTracking(requestId, 'cancel-accepted')
    else beginUnknownFixRecovery(requestId)
  }).catch(error => {
    console.warn(`[Fix] Failed to cancel automatic-fix request ${requestId} during teardown:`, error)
    beginUnknownFixRecovery(requestId)
  }).finally(() => {
    controller?.abort()
  })
}

const prepareForLogout = async (): Promise<'ready' | 'outcome-unknown'> => {
  const requestId = activeFixRequestId.value
  if (!requestId) return unresolvedFixRequestId.value ? 'outcome-unknown' : 'ready'
  const authToken = activeFixAuthToken.value
  pendingFixCancellationId.value = requestId
  fixProgressStage.value = 'CANCELLING'
  try {
    const accepted = await requestInteractiveCancellation({
      cancel: () => cancelOwnedFixRequest(requestId, authToken),
      waitBeforeRetry: waitForFixCancellationRetry,
      shouldContinue: () => activeFixRequestId.value === requestId,
      maxAttempts: 20
    })
    if (accepted) {
      clearActiveFixTracking(requestId, 'cancel-accepted')
      return 'ready'
    }
    if (lastResolvedFixRequest?.requestId === requestId) return 'ready'
    try {
      const status = await readOwnedFixRequestStatus(requestId, authToken)
      if (activeFixRequestId.value === requestId) fixProgressStage.value = status.stage
      if (status.state === 'FINISHED') {
        clearActiveFixTracking(requestId, 'status-finished')
        return 'ready'
      }
    } catch {
      // Missing status is not evidence that an admission-unknown request has finished.
    }
    if (lastResolvedFixRequest?.requestId === requestId) return 'ready'
    return 'outcome-unknown'
  } catch (error) {
    console.warn(`[Fix] Failed to stop automatic-fix request ${requestId} before logout:`, error)
    return 'outcome-unknown'
  }
}

// Watch visible prop. Parent-driven hides and route teardown must cancel expensive searches too.
watch(() => props.visible, (val) => {
  if (val) {
    handleOpen()
  } else {
    void cancelActiveFixSearch()
    dialogRequestVersion += 1
  }
}, { immediate: true })

onBeforeUnmount(() => {
  disposeActiveFixSearch()
  dialogRequestVersion += 1
})

const canOpenTrace = (traceId: number): boolean => {
  if (!activeFixRequestId.value && !unresolvedFixRequestId.value) return true
  return activeFixTraceId.value === traceId
}

defineExpose({ canOpenTrace, prepareForLogout })

// Close dialog
const closeDialog = () => {
  if (applyingFix.value) {
    notifyBlocked(t('app.fixApplyStillRunning'))
    return
  }
  cancelActiveFixSearch()
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
    class="fixed inset-0 z-[var(--z-modal-nested)] bg-black/60 backdrop-blur-sm flex items-center justify-center p-3 sm:p-4"
    @click="closeDialog"
    @keydown="handleModalKeydown"
  >
    <div
      :ref="setDialogRef"
      class="min-h-0 max-h-[85vh] w-[800px] max-w-[95vw] overflow-hidden rounded-2xl border border-slate-200 bg-white shadow-2xl flex flex-col dark:border-slate-700 dark:bg-slate-900"
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
          ? 'board-chip-warning board-border-subtle'
          : hasAttemptResults
            ? 'board-chip-danger'
            : 'board-chip-info'"
      >
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div
              class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm"
              :class="verifiedCount > 0 ? 'board-chip-warning' : hasAttemptResults ? 'board-chip-danger' : 'board-chip-info'"
            >
              <span
                class="material-symbols-outlined text-2xl"
                :class="verifiedCount > 0 ? 'board-text-warning' : hasAttemptResults ? 'board-text-danger' : 'board-text-info'"
                aria-hidden="true"
              >
                {{ strategyLoading ? 'progress_activity' : verifiedCount > 0 ? 'build' : hasAttemptResults ? 'search_off' : 'build' }}
              </span>
            </div>
            <div>
              <h3 id="fix-result-dialog-title" class="text-xl font-bold text-slate-800 dark:text-slate-100">{{ t('app.fixSuggestions') }}</h3>
              <p class="text-sm text-slate-600 dark:text-slate-300">{{ headerStatus }}</p>
            </div>
          </div>
          <button
            type="button"
            :disabled="applyingFix"
            @click="closeDialog"
            class="board-panel-close text-slate-500 hover:text-slate-700 hover:bg-slate-200 disabled:cursor-not-allowed disabled:opacity-40 dark:text-slate-300 dark:hover:bg-slate-800 dark:hover:text-white"
            :aria-label="t('app.close')"
          >
            <span class="material-symbols-outlined text-xl" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Content -->
      <div
        data-testid="fix-result-scroll"
        class="iot-scroll-region iot-scroll-region--inset-end min-h-0 flex-1 p-6"
      >
        
        <div class="space-y-4">
          
          <!-- Violation Info Card -->
          <div class="p-5 rounded-xl bg-gradient-to-r from-[color:var(--danger-surface)] to-[color:var(--warning-surface)] border board-border-subtle">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center board-chip-danger">
                <span class="material-symbols-outlined board-text-danger">warning</span>
              </div>
              <div class="flex-1">
                <span class="text-lg font-bold board-text-danger">{{ t('app.violationDetected') }}</span>
                <div class="flex items-center gap-2 mt-1">
                  <span class="text-sm board-text-danger">
                    {{ faultLoading
                      ? t('app.loadingFaultLocalization')
                      : t('app.faultRulesIdentified', { count: faultRules.length }) }}
                  </span>
                </div>
                <p v-if="localizedFaultLocalizationSummary" class="mt-2 text-xs leading-relaxed board-text-danger">
                  {{ localizedFaultLocalizationSummary }}
                </p>
                <details v-if="fixResult?.violatedSpecId || violatedSpecId" class="mt-2 text-[11px] board-text-danger">
                  <summary class="cursor-pointer font-semibold">{{ t('app.technicalDetails') }}</summary>
                  <div class="mt-1 grid gap-1 sm:grid-cols-[9rem_minmax(0,1fr)]">
                    <span class="font-medium">{{ t('app.specificationTechnicalId') }}</span>
                    <code class="break-all rounded board-chip-danger px-2 py-1 text-[11px] board-text-danger">{{ fixResult?.violatedSpecId || violatedSpecId }}</code>
                  </div>
                </details>
              </div>
            </div>
            <p class="text-sm board-text-danger mt-3 ml-13">
              {{ fixResult ? t('app.fixResultsRemainAdvisory') : t('app.fixAdvisoryBeforeRun') }}
            </p>
          </div>

          <div
            v-if="localizedFixLimitations.length || displayedFixWarnings.length || displayedSourceGenerationIssues.length"
            class="board-surface-warning rounded-xl p-4 text-sm"
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
            <details v-if="displayedFixWarnings.length" class="mt-3 text-xs board-text-warning">
              <summary class="cursor-pointer font-semibold">{{ t('app.fixTechnicalDiagnostics') }}</summary>
              <ul class="mt-2 list-disc space-y-1 pl-5 font-mono text-[11px]">
                <li v-for="warning in displayedFixWarnings" :key="warning">{{ warning }}</li>
              </ul>
            </details>
          </div>

          <!-- Strategy Tabs -->
          <div class="border border-slate-200 rounded-xl overflow-hidden dark:border-slate-700">
            <div class="bg-slate-50 px-4 py-3 border-b border-slate-200 dark:border-slate-700 dark:bg-slate-800">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-slate-600 dark:text-slate-300">tune</span>
                <span class="font-bold text-slate-800 dark:text-slate-100">{{ t('app.fixStrategies') }}</span>
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
                    ? 'bg-[color:var(--accent-fill)] text-white shadow-md'
                    : 'bg-slate-100 text-slate-600 hover:bg-slate-200 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700'"
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
              <div class="text-sm text-slate-500 mb-4 pl-1 dark:text-slate-300">
                {{ strategyDescriptions[selectedStrategy] }}
                <div
                  v-if="currentStrategyAttempt"
                  class="mt-2 rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs text-slate-700 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-200"
                >
                  <span class="font-bold">{{ strategyAttemptStatusLabel(currentStrategyAttempt.status) }}</span>
                  <span class="ml-1">{{ strategyAttemptReasonLabel(currentStrategyAttempt.status) }}</span>
                  <span v-if="strategyAttemptProgress(currentStrategyAttempt)" class="ml-1 font-semibold">
                    {{ strategyAttemptProgress(currentStrategyAttempt) }}
                  </span>
                </div>
              </div>

              <div
                v-if="currentStrategyLoading"
                data-testid="fix-strategy-loading"
                class="board-surface-info mb-4 rounded-lg px-4 py-3 text-sm"
              >
                <div class="flex items-center gap-2 font-semibold">
                  <span class="material-symbols-outlined animate-spin text-lg" aria-hidden="true">progress_activity</span>
                  {{ t('app.tryingFixStrategy', { strategy: strategyLabels[selectedStrategy] }) }}
                </div>
                <p class="mt-1 text-xs board-text-info">{{ t('app.fixAttemptDoesNotApply') }}</p>
                <p class="mt-1 text-xs font-semibold board-text-info">{{ fixProgressStageLabel }}</p>
                <p class="mt-1 text-xs board-text-info">
                  {{ t('app.fixSearchProgress', { seconds: fixSearchElapsedSeconds }) }}
                </p>
              </div>
              <div
                v-else-if="anotherStrategyLoading"
                class="mb-4 rounded-lg border border-slate-200 bg-slate-50 px-4 py-3 text-xs text-slate-600 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-300"
              >
                {{ t('app.anotherFixStrategyRunning', { strategy: strategyLabels[strategyLoading!] }) }}
              </div>

              <!-- Preferred Ranges -->
              <div
                v-if="selectedStrategy === 'parameter' && parameterAdjustments.length"
                class="border border-slate-200 rounded-lg overflow-hidden mb-4 dark:border-slate-700"
              >
                <div class="bg-slate-50 px-3 py-2 border-b border-slate-200 flex items-center gap-2 dark:border-slate-700 dark:bg-slate-800">
                  <span class="material-symbols-outlined text-slate-600 text-lg dark:text-slate-300">speed</span>
                  <span class="font-bold text-sm text-slate-800 dark:text-slate-100">{{ t('app.parameterPreferences') }}</span>
                  <span
                    v-if="activePreferredRangeCount"
                    class="ml-auto px-2 py-0.5 board-chip-info text-xs rounded-full"
                  >{{ activePreferredRangeCount }} {{ t('app.active') }}</span>
                </div>
                <div class="p-3 space-y-3">
                  <div v-if="preferredRangeRows.length" class="space-y-2">
                    <div
                      v-for="row in preferredRangeRows"
                      :key="row.id"
                      class="grid grid-cols-1 sm:grid-cols-[minmax(0,1.6fr)_1fr_1fr_36px] gap-2 items-end"
                    >
                      <label class="text-xs font-medium text-slate-600 dark:text-slate-300">
                        {{ t('app.preferredRangeTarget') }}
                        <select
                          v-model="row.targetId"
                          class="mt-1 w-full rounded-md border border-slate-300 bg-white px-2 py-1.5 text-sm text-slate-800 focus:border-[color:var(--accent-border)] focus:outline-none dark:border-slate-600 dark:bg-slate-950 dark:text-slate-100"
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
                      <label class="text-xs font-medium text-slate-600 dark:text-slate-300">
                        {{ t('app.lowerBound') }}
                        <input
                          v-model.number="row.lower"
                          type="number"
                          class="mt-1 w-full rounded-md border border-slate-300 bg-white px-2 py-1.5 text-sm text-slate-800 focus:border-[color:var(--accent-border)] focus:outline-none dark:border-slate-600 dark:bg-slate-950 dark:text-slate-100"
                        />
                      </label>
                      <label class="text-xs font-medium text-slate-600 dark:text-slate-300">
                        {{ t('app.upperBound') }}
                        <input
                          v-model.number="row.upper"
                          type="number"
                          class="mt-1 w-full rounded-md border border-slate-300 bg-white px-2 py-1.5 text-sm text-slate-800 focus:border-[color:var(--accent-border)] focus:outline-none dark:border-slate-600 dark:bg-slate-950 dark:text-slate-100"
                        />
                      </label>
                      <button
                        type="button"
                        :title="t('app.removePreference')"
                        :aria-label="t('app.removePreference')"
                        @click="removePreferenceRow(row.id)"
                        class="w-9 h-9 rounded-md bg-slate-100 hover:board-chip-danger text-slate-500 hover:board-text-danger flex items-center justify-center transition-colors dark:bg-slate-800 dark:text-slate-300 dark:hover:bg-[color:var(--danger-surface)]/60 dark:hover:board-text-danger"
                      >
                        <span class="material-symbols-outlined text-lg" aria-hidden="true">delete</span>
                      </button>
                    </div>
                  </div>
                  <div
                    v-else-if="preferredRangeTargetOptions.length === 0"
                    class="rounded-md border border-slate-200 bg-slate-50 px-3 py-2 text-xs text-slate-500 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-300"
                  >
                    {{ t('app.noParameterPreferenceTargets') }}
                  </div>

                  <div
                    v-if="fixResult?.unusedPreferredRangeSelections?.length"
                    class="board-surface-warning rounded-md px-3 py-2 text-xs"
                  >
                    {{ t('app.unusedPreferencesDetail', { count: fixResult.unusedPreferredRangeSelections.length }) }}
                  </div>

                  <div class="flex flex-wrap gap-2">
                    <button
                      type="button"
                      data-testid="fix-use-current-preferences"
                      @click="seedPreferenceRowsFromSuggestion"
                      :disabled="preferredRangeTargetOptions.length === 0"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors disabled:cursor-not-allowed disabled:opacity-50 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
                    >
                      <span class="material-symbols-outlined text-base">playlist_add</span>
                      {{ t('app.useCurrent') }}
                    </button>
                    <button
                      type="button"
                      @click="addPreferenceRow()"
                      :disabled="preferredRangeTargetOptions.length === 0"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors disabled:cursor-not-allowed disabled:opacity-50 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
                    >
                      <span class="material-symbols-outlined text-base">add</span>
                      {{ t('app.add') }}
                    </button>
                    <button
                      type="button"
                      data-testid="fix-run-with-preferences"
                      :disabled="Boolean(preferenceActionBlockedReason)"
                      :aria-describedby="preferenceActionBlockedReason ? 'fix-preference-blocked' : undefined"
                      @click="refreshWithPreferences"
                      class="board-action-inline text-sm"
                    >
                      <span class="material-symbols-outlined text-base">refresh</span>
                      {{ t('app.runWithPreferences') }}
                    </button>
                    <button
                      v-if="preferredRangeRows.length || activePreferredRangeCount"
                      type="button"
                      data-testid="fix-clear-preferences"
                      :disabled="Boolean(preferenceActionBlockedReason)"
                      :aria-describedby="preferenceActionBlockedReason ? 'fix-preference-blocked' : undefined"
                      @click="clearPreferenceRows"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors disabled:cursor-not-allowed disabled:opacity-60 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
                    >
                      <span class="material-symbols-outlined text-base">restart_alt</span>
                      {{ t('app.reset') }}
                    </button>
                  </div>
                  <p
                    v-if="preferenceActionBlockedReason"
                    id="fix-preference-blocked"
                    data-testid="fix-preference-blocked"
                    class="mt-2 text-xs text-slate-500 dark:text-slate-400"
                  >{{ preferenceActionBlockedReason }}</p>
                </div>
              </div>

              <!-- Current Suggestion -->
              <div v-if="currentSuggestion">
                
                <!-- Status Card -->
                <div class="p-4 rounded-xl mb-4" :class="currentSuggestion.verified 
                  ? 'bg-gradient-to-r bg-[color:var(--success-surface)] bg-[color:var(--success-surface)] border border-[color:var(--success-border)]'
                  : 'bg-gradient-to-r from-[color:var(--danger-surface)] to-[color:var(--warning-surface)] border board-border-subtle'">
                  <div class="flex items-center gap-3">
                    <div class="w-10 h-10 rounded-xl flex items-center justify-center" :class="currentSuggestion.verified ? 'board-chip-success' : 'board-chip-danger'">
                      <span class="material-symbols-outlined" :class="currentSuggestion.verified ? 'board-text-success' : 'board-text-danger'">
                        {{ currentSuggestion.verified ? 'verified' : 'cancel' }}
                      </span>
                    </div>
                    <div class="flex-1">
                      <span class="font-bold" :class="currentSuggestion.verified ? 'board-text-success' : 'board-text-danger'">
                        {{ currentSuggestion.verified ? t('app.verifiedSolution') : t('app.notVerified') }}
                      </span>
                      <p class="text-sm" :class="currentSuggestion.verified ? 'board-text-success' : 'board-text-danger'">
                        {{ strategyDescriptions[currentSuggestion.strategy] }}
                      </p>
                    </div>
                  </div>
                </div>

                <!-- Parameter Adjustments -->
                <div v-if="currentSuggestion.parameterAdjustments?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700 dark:text-slate-200">
                    <span class="material-symbols-outlined board-text-info">tune</span>
                    {{ t('app.parameterAdjustments') }} ({{ currentSuggestion.parameterAdjustments.length }})
                  </div>
                  <div class="space-y-2">
                    <div
                      v-for="(adj, idx) in currentSuggestion.parameterAdjustments"
                      :key="idx"
                      class="board-chip-info border board-border-subtle rounded-lg p-3"
                    >
                      <div class="flex items-center justify-between">
                        <div class="min-w-0 flex items-center gap-2">
                          <span
                            class="max-w-[14rem] truncate px-2 py-0.5 bg-[color:var(--accent-fill)] text-white text-xs rounded font-bold"
                            :title="formatPreferredRangeTarget(adj)"
                          >{{ formatPreferredRangeTarget(adj) }}</span>
                          <code class="min-w-0 truncate text-sm font-mono text-slate-700 dark:text-slate-200" :title="`${formatModelToken(adj.attribute, adj.modelTokenSource)} ${adj.relation}`">{{ formatModelToken(adj.attribute, adj.modelTokenSource) }} {{ adj.relation }}</code>
                        </div>
                        <div class="flex items-center gap-2">
                          <span class="text-xs text-slate-500 dark:text-slate-300">{{ t('app.rangeLabel') }}: [{{ adj.lowerBound }}, {{ adj.upperBound }}]</span>
                          <button
                            type="button"
                            @click="useAdjustmentAsPreference(adj)"
                            class="px-2 py-1 rounded bg-white border board-border-subtle board-text-info hover:board-chip-info text-xs font-medium transition-colors dark:bg-slate-900 dark:hover:bg-[color:var(--accent-strong)]/60"
                          >
                            {{ t('app.prefer') }}
                          </button>
                          <button
                            type="button"
                            data-testid="fix-lock-original"
                            :title="t('app.lockOriginalValue')"
                            :aria-label="t('app.lockOriginalValue')"
                            @click="lockAdjustmentAtOriginal(adj)"
                            class="flex h-7 w-7 items-center justify-center rounded border board-border-subtle bg-white board-text-info transition-colors hover:board-chip-info dark:bg-slate-900 dark:hover:bg-[color:var(--accent-strong)]/60"
                          >
                            <span class="material-symbols-outlined text-base" aria-hidden="true">lock</span>
                          </button>
                        </div>
                      </div>
                      <div class="flex items-center gap-2 mt-2">
                        <span class="px-2 py-1 board-chip-danger rounded font-mono text-sm line-through">{{ adj.originalValue }}</span>
                        <span class="material-symbols-outlined text-slate-500 dark:text-slate-500">arrow_forward</span>
                        <span class="px-2 py-1 board-chip-success rounded font-mono text-sm">{{ adj.newValue }}</span>
                      </div>
                      <p
                        v-if="parameterAdjustmentMakesRuleUnreachable(adj)"
                        data-testid="fix-parameter-unreachable-warning"
                        class="mt-2 text-xs font-semibold board-text-warning"
                      >
                        {{ t('app.fixParameterMakesRuleUnreachable') }}
                      </p>
                    </div>
                  </div>
                </div>

                <!-- Condition Adjustments -->
                <div v-if="currentSuggestion.conditionAdjustments?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700 dark:text-slate-200">
                    <span class="material-symbols-outlined board-text-success">checklist</span>
                    {{ t('app.conditionAdjustments') }} ({{ currentSuggestion.conditionAdjustments.length }})
                  </div>
                  <div class="space-y-2">
                    <div
                      v-for="(adj, idx) in currentSuggestion.conditionAdjustments"
                      :key="idx"
                      class="board-chip-success border board-border-subtle rounded-lg p-3 flex items-center gap-3"
                    >
                      <div 
                        class="w-8 h-8 rounded-lg flex items-center justify-center"
                        :class="adj.action === 'remove' ? 'board-chip-danger' : adj.action === 'add' ? 'board-chip-success' : 'bg-slate-100 dark:bg-slate-700'"
                      >
                        <span class="material-symbols-outlined text-sm" :class="adj.action === 'remove' ? 'board-text-danger' : adj.action === 'add' ? 'board-text-success' : 'text-slate-600 dark:text-slate-200'" aria-hidden="true">
                          {{ adj.action === 'remove' ? 'remove' : adj.action === 'add' ? 'add' : 'check' }}
                        </span>
                      </div>
                      <div class="flex-1">
                        <span class="text-sm font-medium text-slate-700 dark:text-slate-200">{{ formatConditionAdjustment(adj) }}</span>
                      </div>
                      <span 
                        class="px-2 py-0.5 rounded text-xs font-medium"
                        :class="adj.action === 'remove' ? 'board-chip-danger board-text-danger' : adj.action === 'add' ? 'board-chip-success board-text-success' : 'bg-slate-100 text-slate-600 dark:bg-slate-700 dark:text-slate-200'"
                      >
                        {{ getConditionActionLabel(adj.action) }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Disabled Rules -->
                <div v-if="currentSuggestion.removedRuleDescriptions?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700 dark:text-slate-200">
                    <span class="material-symbols-outlined board-text-warning">block</span>
                    {{ t('app.rulesToRemove') }} ({{ currentSuggestion.removedRuleDescriptions.length }})
                  </div>
                  <div class="board-chip-warning border border-[color:var(--warning-border)] rounded-lg p-3">
                    <div class="space-y-2">
                      <span
                        v-for="(description, index) in currentSuggestion.removedRuleDescriptions"
                        :key="`${index}-${description}`"
                        data-testid="fix-removed-rule"
                        class="block rounded-lg bg-[color:var(--warning-fill)] px-3 py-1 text-sm font-medium text-white"
                      >
                        {{ description }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Apply lives in the footer; this only explains an unverified suggestion. -->
                <div v-if="!currentSuggestion.verified" class="pt-4 border-t border-slate-200 text-center dark:border-slate-700">
                  <div class="flex items-center justify-center gap-2 board-text-danger">
                    <span class="material-symbols-outlined">info</span>
                    <span class="font-medium">{{ t('app.solutionNotVerified') }}</span>
                  </div>
                  <p class="text-xs board-text-danger mt-1">{{ t('app.tryAnotherStrategy') }}</p>
                </div>
              </div>

              <div v-else-if="strategyErrors[selectedStrategy]" class="board-surface-danger rounded-lg px-4 py-4">
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
                class="board-surface-warning rounded-lg px-4 py-4"
              >
                <div class="flex items-start gap-2">
                  <span class="material-symbols-outlined text-lg" aria-hidden="true">edit_note</span>
                  <div>
                    <p class="font-semibold">{{ t('app.parameterPreferencesChanged') }}</p>
                    <p class="mt-1 text-xs">{{ t('app.parameterPreferencesRequireRetry') }}</p>
                  </div>
                </div>
              </div>

              <div v-else-if="currentStrategyAttempt" class="text-center py-8 text-slate-500 dark:text-slate-300">
                <span class="material-symbols-outlined text-4xl mb-2 block">help</span>
                <p>{{ strategyAttemptOutcomeTitle(currentStrategyAttempt) }}</p>
                <p class="mx-auto mt-2 max-w-lg text-xs text-slate-500 dark:text-slate-400">
                  {{ strategyAttemptOutcomeDetail(currentStrategyAttempt) }}
                </p>
                <p
                  v-if="strategyAttemptProgress(currentStrategyAttempt)"
                  class="mx-auto mt-2 max-w-lg text-xs font-semibold text-slate-600 dark:text-slate-300"
                >
                  {{ strategyAttemptProgress(currentStrategyAttempt) }}
                </p>
              </div>

              <div v-else-if="!currentStrategyLoading" class="rounded-lg border border-dashed border-slate-300 bg-slate-50 px-4 py-5 text-center text-slate-600 dark:border-slate-600 dark:bg-slate-800 dark:text-slate-300">
                <span class="material-symbols-outlined mb-2 block text-3xl text-slate-400 dark:text-slate-500" aria-hidden="true">science</span>
                <p class="font-semibold">{{ t('app.fixStrategyNotTried') }}</p>
                <p class="mt-1 text-xs text-slate-500 dark:text-slate-400">{{ t('app.fixAttemptDoesNotApply') }}</p>
              </div>

            </div>
          </div>

          <!-- Fault Rules Section -->
          <div class="border border-slate-200 rounded-xl overflow-hidden dark:border-slate-700">
            <div class="bg-slate-50 px-4 py-3 border-b border-slate-200 dark:border-slate-700 dark:bg-slate-800">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-slate-600 dark:text-slate-300">search</span>
                <span class="font-bold text-slate-800 dark:text-slate-100">{{ t('app.faultLocalization') }}</span>
                <span class="ml-auto px-2 py-0.5 board-chip-danger text-xs rounded-full">{{ t('app.rulesCount', { count: faultRules.length }) }}</span>
              </div>
            </div>
            
            <div class="p-4">
              <div v-if="faultLoading" class="flex items-center justify-center gap-2 py-8 text-sm text-slate-500 dark:text-slate-300">
                <span class="material-symbols-outlined animate-spin" aria-hidden="true">progress_activity</span>
                {{ t('app.loadingFaultLocalization') }}
              </div>
              <div v-else-if="faultLoadFailed" class="text-center py-8 board-text-danger">
                <span class="material-symbols-outlined text-3xl" aria-hidden="true">error</span>
                <p class="mt-2 text-sm font-medium">{{ t('app.failedToLoadFaultLocalization') }}</p>
              </div>
              <div v-else-if="faultRules.length === 0" class="text-center py-8 text-slate-500 dark:text-slate-400">
                <span class="material-symbols-outlined text-4xl mb-2 block">check_circle</span>
                <p>{{ t('app.noFaultRulesFound') }}</p>
                <p class="text-xs mt-1">{{ t('app.violationMayBeDeviceTransitions') }}</p>
              </div>
              
              <div v-else class="space-y-2">
                <div 
                  v-for="(rule, idx) in faultRules"
                  :key="idx"
                  class="border border-slate-200 rounded-lg p-3 hover:bg-slate-50 transition-colors dark:border-slate-700 dark:hover:bg-slate-800"
                  :class="{ 'border-[color:var(--warning-border)] board-chip-warning': rule.conflicting }"
                >
                  <div class="flex items-center justify-between mb-2">
                    <div class="flex items-center gap-2">
                      <span class="w-6 h-6 bg-[color:var(--accent-fill-hover)] text-white rounded flex items-center justify-center text-xs font-bold">{{ idx + 1 }}</span>
                      <code class="text-xs bg-slate-100 px-2 py-1 rounded font-mono dark:bg-slate-800 dark:text-slate-100">{{ rule.ruleString?.trim() || t('app.noDescription') }}</code>
                    </div>
                    <span v-if="rule.conflicting" class="px-2 py-0.5 board-chip-warning board-text-warning text-xs rounded flex items-center gap-1">
                      <span class="material-symbols-outlined text-xs">warning</span>
                      {{ t('app.conflicts') }}
                    </span>
                  </div>
                  <div class="grid grid-cols-1 gap-2 text-xs text-slate-600 sm:grid-cols-3 dark:text-slate-300">
                    <div>{{ t('app.transitionNumberLabel') }}: <span class="font-medium">{{ rule.transitionNumber }}</span></div>
                    <div>{{ t('app.device') }}: <span class="font-medium">{{ rule.targetDeviceLabel }}</span></div>
                    <div>{{ t('app.action') }}: <span data-testid="fix-fault-action" class="font-medium">{{ formatModelToken(rule.targetActionLabel, rule.modelTokenSource) }}</span></div>
                  </div>
                  <div v-if="rule.reason" class="mt-2 text-xs text-slate-500 flex items-start gap-1 dark:text-slate-400">
                    <span class="material-symbols-outlined text-xs mt-0.5">info</span>
                    {{ getFaultRuleReason(rule) }}
                  </div>
                </div>
              </div>
            </div>
          </div>

          <!-- Other Strategies -->
          <div v-if="(fixResult?.suggestions.length || 0) > 1" class="border border-slate-200 rounded-xl p-4 dark:border-slate-700">
            <div class="text-sm font-bold text-slate-700 mb-3 flex items-center gap-2 dark:text-slate-200">
              <span class="material-symbols-outlined text-slate-600 dark:text-slate-300">layers</span>
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
                  ? 'board-chip-success board-text-success hover:bg-[color:var(--success-surface)] border border-[color:var(--success-border)] dark:hover:bg-[color:var(--success-surface)]'
                  : 'bg-slate-100 text-slate-600 hover:bg-slate-200 border border-slate-300 dark:border-slate-600 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700'"
              >
                <span class="material-symbols-outlined text-sm">
                  {{ strategyIcons[s.strategy] }}
                </span>
                {{ strategyLabels[s.strategy] }}
                <span v-if="s.verified && suggestionIsCurrent(s)" class="material-symbols-outlined board-text-success text-xs">verified</span>
              </button>
            </div>
          </div>

        </div>
      </div>

      <!-- Footer: dismiss on the left, the one primary action on the right.
           Try and Apply are mutually exclusive (Try while unverified, Apply once verified), so
           exactly one shows here. Both used to sit at the end of the scroll body, where the
           strategy detail is routinely ~300px taller than the fold: the action landed 19px past
           the visible edge and read as a broken, half-drawn control in both themes. An action the
           user must reach to make progress does not belong behind a scroll. Matches the
           dismiss-left / primary-right footer RuleBuilderDialog already establishes. -->
      <div class="flex flex-wrap items-center gap-3 border-t border-slate-200 p-4 bg-slate-50 rounded-b-2xl dark:border-slate-700 dark:bg-slate-950">
        <button
          type="button"
          :disabled="applyingFix"
          @click="closeDialog"
          class="min-h-11 px-6 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg font-medium transition-colors flex items-center gap-2 disabled:cursor-not-allowed disabled:opacity-50 dark:bg-slate-800 dark:text-slate-200 dark:hover:bg-slate-700"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">close</span>
          {{ t('app.close') }}
        </button>

        <div class="ml-auto flex min-w-0 flex-col items-end gap-2">
          <p
            v-if="applyBlockedReason"
            id="fix-apply-readiness"
            data-testid="fix-apply-readiness"
            role="status"
            class="max-w-xl text-right text-xs leading-5 text-slate-500 dark:text-slate-400"
          >
            {{ applyBlockedReason }}
          </p>

          <button
            v-if="currentSuggestion?.verified"
            type="button"
            data-testid="fix-apply-current"
            class="px-8 text-sm"
            :class="applyDisabled
              ? 'flex items-center justify-center gap-2 rounded-lg py-2.5 font-bold bg-slate-300 text-slate-500 cursor-not-allowed dark:bg-slate-700 dark:text-slate-400'
              : currentSuggestion.strategy === 'remove'
                ? 'board-action-inline-danger'
                : 'board-action-inline-affirm'"
            :disabled="applyDisabled"
            :aria-describedby="applyBlockedReason ? 'fix-apply-readiness' : undefined"
            @click="applyFix(currentSuggestion)"
          >
            <span v-if="!applyingFix" class="material-symbols-outlined text-lg" aria-hidden="true">check_circle</span>
            <span v-else class="h-5 w-5 animate-spin rounded-full border-2 border-white border-t-transparent"></span>
            {{ applyingFix
              ? t('app.applying')
              : currentSuggestion.strategy === 'remove'
                ? t('app.removeRulesAndApply')
                : t('app.applyThisFix') }}
          </button>

          <button
            v-else
            type="button"
            data-testid="fix-try-current"
            :disabled="strategyLoading !== null"
            @click="trySelectedStrategy"
            class="flex items-center justify-center gap-2 min-h-11 rounded-lg bg-[color:var(--accent-fill)] px-8 py-2.5 text-sm font-bold text-white transition-colors hover:bg-[color:var(--accent-fill-hover)] disabled:cursor-not-allowed disabled:bg-slate-300 dark:disabled:bg-slate-700 dark:disabled:text-slate-400"
          >
            <span class="material-symbols-outlined text-lg" aria-hidden="true">science</span>
            {{ currentStrategyAttempt || strategyErrors[selectedStrategy]
              ? t('app.retryFixStrategy')
              : t('app.tryFixStrategy') }}
          </button>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
</style>
