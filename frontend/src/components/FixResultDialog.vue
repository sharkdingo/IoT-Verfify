<script setup lang="ts">
import { ref, computed, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { ElMessage } from 'element-plus'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import boardApi from '@/api/board'
import type {
  FaultRule,
  FixResult,
  FixStrategyName,
  FixSuggestion,
  ParameterAdjustment,
  PreferredRange
} from '@/types/fix'

const props = defineProps<{
  visible: boolean
  traceId: number
  violatedSpecId?: string
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'applied': []
}>()

const { t } = useI18n()

const loading = ref(false)
const fixResult = ref<FixResult | null>(null)
const faultRules = ref<FaultRule[]>([])
const selectedStrategy = ref<FixStrategyName>('parameter')
const applyingFix = ref(false)
// 记录本次 /fix 用的 preferredRanges，apply 时原样回传，保证后端重算复现同一建议。
const lastPreferredRanges = ref<Record<string, PreferredRange> | undefined>(undefined)

type PreferredRangeRow = {
  id: string
  ruleNumber: number | null
  conditionNumber: number | null
  lower: number | null
  upper: number | null
}

const strategyOrder: FixStrategyName[] = ['parameter', 'condition', 'disable']

const strategyIcons: Record<FixStrategyName, string> = {
  parameter: 'tune',
  condition: 'checklist',
  disable: 'block'
}

const strategyLabels = computed<Record<FixStrategyName, string>>(() => ({
  parameter: t('app.fixStrategyParameter'),
  condition: t('app.fixStrategyCondition'),
  disable: t('app.fixStrategyDisable')
}))

const strategyDescriptions = computed<Record<FixStrategyName, string>>(() => ({
  parameter: t('app.fixStrategyParameterDesc'),
  condition: t('app.fixStrategyConditionDesc'),
  disable: t('app.fixStrategyDisableDesc')
}))

const strategyOptions = computed(() => strategyOrder.map(value => ({
  value,
  label: strategyLabels.value[value],
  icon: strategyIcons[value]
})))

const preferredRangeRows = ref<PreferredRangeRow[]>([])

const newRangeRowId = () => `${Date.now()}-${Math.random().toString(36).slice(2)}`

const parameterSuggestion = computed(() => {
  return fixResult.value?.suggestions.find(s => s.strategy === 'parameter') ?? null
})

const parameterAdjustments = computed(() => {
  return parameterSuggestion.value?.parameterAdjustments ?? []
})

const activePreferredRangeCount = computed(() => {
  return Object.keys(lastPreferredRanges.value ?? {}).length
})

const isBlank = (value: unknown) => value === null || value === undefined || value === ''

const buildPreferredRanges = (showWarnings = false): Record<string, PreferredRange> | undefined | null => {
  const ranges: Record<string, PreferredRange> = {}
  const seen = new Set<string>()

  for (const row of preferredRangeRows.value) {
    const values = [row.ruleNumber, row.conditionNumber, row.lower, row.upper]
    if (values.every(isBlank)) {
      continue
    }
    if (values.some(isBlank)) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeCompleteFields'))
      return null
    }

    const ruleNumber = Number(row.ruleNumber)
    const conditionNumber = Number(row.conditionNumber)
    const lower = Number(row.lower)
    const upper = Number(row.upper)

    if (!Number.isInteger(ruleNumber) || !Number.isInteger(conditionNumber)
        || ruleNumber < 1 || conditionNumber < 1) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangePositiveIntegers'))
      return null
    }
    if (!Number.isFinite(lower) || !Number.isFinite(upper) || lower > upper) {
      if (showWarnings) ElMessage.warning(t('app.preferredRangeLowerBeforeUpper'))
      return null
    }

    const key = `r${ruleNumber - 1}_c${conditionNumber - 1}`
    if (seen.has(key)) {
      if (showWarnings) ElMessage.warning(t('app.duplicatePreferredRange', { key }))
      return null
    }
    seen.add(key)
    ranges[key] = { lower, upper }
  }

  return Object.keys(ranges).length > 0 ? ranges : undefined
}

const addPreferenceRow = (adjustment?: ParameterAdjustment) => {
  const nextAdjustment = adjustment ?? parameterAdjustments.value.find(adj => {
    return !preferredRangeRows.value.some(row =>
      row.ruleNumber === adj.ruleIndex + 1 && row.conditionNumber === adj.conditionIndex + 1)
  })
  preferredRangeRows.value.push({
    id: newRangeRowId(),
    ruleNumber: nextAdjustment ? nextAdjustment.ruleIndex + 1 : null,
    conditionNumber: nextAdjustment ? nextAdjustment.conditionIndex + 1 : null,
    lower: nextAdjustment?.lowerBound ?? null,
    upper: nextAdjustment?.upperBound ?? null
  })
}

const useAdjustmentAsPreference = (adjustment: ParameterAdjustment) => {
  const ruleNumber = adjustment.ruleIndex + 1
  const conditionNumber = adjustment.conditionIndex + 1
  const existing = preferredRangeRows.value.find(row =>
    row.ruleNumber === ruleNumber && row.conditionNumber === conditionNumber)

  if (existing) {
    existing.lower = adjustment.lowerBound
    existing.upper = adjustment.upperBound
  } else {
    addPreferenceRow(adjustment)
  }
}

const seedPreferenceRowsFromSuggestion = () => {
  const adjustments = parameterAdjustments.value
  if (adjustments.length === 0) {
    addPreferenceRow()
    return
  }
  preferredRangeRows.value = adjustments.map(adj => ({
    id: newRangeRowId(),
    ruleNumber: adj.ruleIndex + 1,
    conditionNumber: adj.conditionIndex + 1,
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
  
  loading.value = true
  try {
    faultRules.value = await boardApi.getFaultRules(props.traceId)
  } catch (error) {
    console.error('Failed to fetch fault rules:', error)
    ElMessage.error(t('app.failedToLoadFaultLocalization'))
  } finally {
    loading.value = false
  }
}

// Fetch fix suggestions
const fetchFixSuggestions = async () => {
  if (!props.traceId) return
  
  loading.value = true
  try {
    const preferredRanges = buildPreferredRanges()
    if (preferredRanges === null) return
    lastPreferredRanges.value = preferredRanges
    fixResult.value = await boardApi.fixTrace(props.traceId, {
      strategies: strategyOrder,
      preferredRanges
    })
  } catch (error) {
    console.error('Failed to fetch fix suggestions:', error)
    ElMessage.error(t('app.failedToLoadFixSuggestions'))
  } finally {
    loading.value = false
  }
}

const refreshWithPreferences = async () => {
  if (buildPreferredRanges(true) === null) return
  await fetchFixSuggestions()
}

const clearPreferenceRows = async () => {
  preferredRangeRows.value = []
  await fetchFixSuggestions()
}

// Load all data
const loadData = async () => {
  await Promise.all([
    fetchFaultRules(),
    fetchFixSuggestions()
  ])
}

// Handle dialog open
const handleOpen = () => {
  fixResult.value = null
  faultRules.value = []
  preferredRangeRows.value = []
  lastPreferredRanges.value = undefined
  selectedStrategy.value = 'parameter'
  loadData()
}

// Switch strategy
const switchStrategy = (strategy: FixStrategyName) => {
  selectedStrategy.value = strategy
}

// Apply fix：把当前展示的（已验证的）建议原样回传后端落库，成功后通知父组件刷新规则。
const applyFix = async (suggestion: FixSuggestion) => {
  if (!props.traceId) return
  if (!suggestion.verified) {
    ElMessage.warning(t('app.unverifiedFixCannotApply'))
    return
  }
  applyingFix.value = true
  try {
    const result = await boardApi.applyFix(props.traceId, suggestion.strategy, suggestion, lastPreferredRanges.value)
    ElMessage.success(result.message || t('app.fixAppliedSuccessfully'))
    emit('applied')
    emit('update:visible', false)
  } catch (error: any) {
    console.error('Failed to apply fix:', error)
    // 后端会在 board 规则漂移、索引越界等情况下返回带原因的 400，优先展示它。
    const msg = error?.response?.data?.message || error?.message || t('app.failedToApplyFix')
    ElMessage.error(msg)
  } finally {
    applyingFix.value = false
  }
}

// Current strategy suggestion
const currentSuggestion = computed(() => {
  if (!fixResult.value) return null
  return fixResult.value.suggestions.find(s => s.strategy === selectedStrategy.value)
})

// Get verified strategies count
const verifiedCount = computed(() => {
  if (!fixResult.value) return 0
  return fixResult.value.suggestions.filter(s => s.verified).length
})

// Get step label
const getStepLabel = (step: number) => {
  return step === 0 ? t('app.traceVisualization.initialState') : `${t('app.step')} ${step}`
}

const getConditionActionLabel = (action?: string) => {
  if (action === 'remove') return t('app.remove')
  if (action === 'add') return t('app.add')
  if (action === 'keep') return t('app.keep')
  return action || ''
}

// Watch visible prop
watch(() => props.visible, (val) => {
  if (val) {
    handleOpen()
  }
})

// Close dialog
const closeDialog = () => {
  emit('update:visible', false)
}

const isDialogOpen = computed(() => props.visible)
const { setDialogRef, handleModalKeydown } = useModalAccessibility(isDialogOpen, closeDialog)
</script>

<template>
  <!-- Fix Result Dialog - Following Verification Result Style -->
  <div
    v-if="visible"
    class="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50"
    @click="closeDialog"
    @keydown="handleModalKeydown"
  >
    <div
      :ref="setDialogRef"
      class="bg-white rounded-2xl w-[800px] max-w-[95vw] shadow-2xl max-h-[85vh] flex flex-col border border-slate-200"
      role="dialog"
      aria-modal="true"
      aria-labelledby="fix-result-dialog-title"
      tabindex="-1"
      @click.stop
    >
      
      <!-- Header -->
      <div class="relative overflow-hidden rounded-t-2xl border-b" :class="verifiedCount > 0 ? 'bg-amber-50 border-amber-200' : 'bg-red-50 border-red-200'">
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm" :class="verifiedCount > 0 ? 'bg-amber-100' : 'bg-red-100'">
              <span class="material-symbols-outlined text-2xl" :class="verifiedCount > 0 ? 'text-amber-600' : 'text-red-600'" aria-hidden="true">
                {{ verifiedCount > 0 ? 'build' : 'error' }}
              </span>
            </div>
            <div>
              <h3 id="fix-result-dialog-title" class="text-xl font-bold text-slate-800">{{ t('app.fixSuggestions') }}</h3>
              <p class="text-sm text-slate-600">{{ verifiedCount > 0 ? t('app.verifiedSolutionsCount', { count: verifiedCount }) : t('app.noVerifiedSolutionsYet') }}</p>
            </div>
          </div>
          <button type="button" @click="closeDialog" class="w-9 h-9 flex items-center justify-center rounded-lg text-slate-500 hover:text-slate-700 hover:bg-slate-200 transition-all" :aria-label="t('app.close')">
            <span class="material-symbols-outlined text-xl" aria-hidden="true">close</span>
          </button>
        </div>
      </div>

      <!-- Content -->
      <div class="p-6 flex-1 overflow-y-auto">
        
        <!-- Loading State -->
        <div v-if="loading" class="flex flex-col items-center justify-center py-16">
          <div class="relative mb-4">
            <div class="animate-spin rounded-full h-12 w-12 border-4 border-slate-200 border-t-blue-500"></div>
          </div>
          <span class="text-slate-600 font-medium">{{ t('app.analyzingFixSuggestions') }}</span>
        </div>

        <div v-else-if="fixResult" class="space-y-4">
          
          <!-- Violation Info Card -->
          <div class="p-5 rounded-xl bg-gradient-to-r from-red-50 to-orange-50 border border-red-200">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center bg-red-100">
                <span class="material-symbols-outlined text-red-600">warning</span>
              </div>
              <div class="flex-1">
                <span class="text-lg font-bold text-red-800">{{ t('app.violationDetected') }}</span>
                <div class="flex items-center gap-2 mt-1">
                  <span class="px-2 py-0.5 bg-red-100 text-red-700 text-xs rounded font-mono">{{ fixResult.violatedSpecId }}</span>
                  <span class="text-sm text-red-600">{{ t('app.faultRulesIdentified', { count: faultRules.length }) }}</span>
                </div>
              </div>
            </div>
            <p class="text-sm text-red-700 mt-3 ml-13">{{ fixResult.summary }}</p>
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
                    v-if="fixResult.suggestions.some(s => s.strategy === option.value && s.verified)"
                    class="material-symbols-outlined text-sm"
                  >verified</span>
                </button>
              </div>

              <!-- Strategy Description -->
              <div class="text-sm text-slate-500 mb-4 pl-1">
                {{ strategyDescriptions[selectedStrategy] }}
              </div>

              <!-- Preferred Ranges -->
              <div class="border border-slate-200 rounded-lg overflow-hidden mb-4">
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
                      class="grid grid-cols-2 sm:grid-cols-[80px_96px_1fr_1fr_36px] gap-2 items-end"
                    >
                      <label class="text-xs font-medium text-slate-600">
                        {{ t('app.ruleName') }}
                        <input
                          v-model.number="row.ruleNumber"
                          type="number"
                          min="1"
                          class="mt-1 w-full rounded-md border border-slate-300 px-2 py-1.5 text-sm text-slate-800 focus:border-blue-400 focus:outline-none"
                        />
                      </label>
                      <label class="text-xs font-medium text-slate-600">
                        {{ t('app.condition') }}
                        <input
                          v-model.number="row.conditionNumber"
                          type="number"
                          min="1"
                          class="mt-1 w-full rounded-md border border-slate-300 px-2 py-1.5 text-sm text-slate-800 focus:border-blue-400 focus:outline-none"
                        />
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
                    v-if="fixResult.unusedPreferredRangeKeys?.length"
                    class="rounded-md border border-amber-200 bg-amber-50 px-3 py-2 text-xs text-amber-700"
                  >
                    {{ t('app.unusedPreferences') }}: {{ fixResult.unusedPreferredRangeKeys.join(', ') }}
                  </div>

                  <div class="flex flex-wrap gap-2">
                    <button
                      type="button"
                      @click="seedPreferenceRowsFromSuggestion"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors"
                    >
                      <span class="material-symbols-outlined text-base">playlist_add</span>
                      {{ t('app.useCurrent') }}
                    </button>
                    <button
                      type="button"
                      @click="addPreferenceRow()"
                      class="px-3 py-2 rounded-md bg-slate-100 hover:bg-slate-200 text-slate-700 text-sm font-medium flex items-center gap-1 transition-colors"
                    >
                      <span class="material-symbols-outlined text-base">add</span>
                      {{ t('app.add') }}
                    </button>
                    <button
                      type="button"
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
                        {{ currentSuggestion.description }}
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
                        <div class="flex items-center gap-2">
                          <span class="px-2 py-0.5 bg-blue-500 text-white text-xs rounded font-bold">{{ t('app.ruleNumber', { number: adj.ruleIndex + 1 }) }}</span>
                          <span class="px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded font-medium">{{ t('app.conditionNumber', { number: adj.conditionIndex + 1 }) }}</span>
                          <code class="text-sm font-mono text-slate-700">{{ adj.attribute }} {{ adj.relation }}</code>
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
                        <span class="text-sm font-medium text-slate-700">{{ adj.description }}</span>
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
                <div v-if="currentSuggestion.disabledRuleIndices?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700">
                    <span class="material-symbols-outlined text-orange-500">block</span>
                    {{ t('app.rulesToDisable') }} ({{ currentSuggestion.disabledRuleIndices.length }})
                  </div>
                  <div class="bg-orange-50 border border-orange-200 rounded-lg p-3">
                    <div class="flex flex-wrap gap-2">
                      <span 
                        v-for="idx in currentSuggestion.disabledRuleIndices" 
                        :key="idx"
                        class="px-3 py-1 bg-orange-500 text-white rounded-lg text-sm font-medium"
                      >
                        {{ t('app.ruleNumber', { number: idx + 1 }) }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Apply Button -->
                <div v-if="currentSuggestion.verified" class="pt-4 border-t border-slate-200">
                  <button 
                    class="w-full py-3 rounded-lg font-bold text-base transition-all flex items-center justify-center gap-2"
                    :class="applyingFix 
                      ? 'bg-slate-300 text-slate-500 cursor-not-allowed' 
                      : 'bg-green-500 hover:bg-green-600 text-white shadow-md hover:shadow-lg'"
                    :disabled="applyingFix"
                    @click="applyFix(currentSuggestion)"
                  >
                    <span v-if="!applyingFix" class="material-symbols-outlined">check_circle</span>
                    <div v-else class="animate-spin rounded-full h-5 w-5 border-2 border-white border-t-transparent"></div>
                    {{ applyingFix ? t('app.applying') : t('app.applyThisFix') }}
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

              <div v-else class="text-center py-8 text-slate-400">
                <span class="material-symbols-outlined text-4xl mb-2 block">help</span>
                <p>{{ t('app.noFixSuggestionsForStrategy') }}</p>
              </div>
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
              <div v-if="faultRules.length === 0" class="text-center py-8 text-slate-400">
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
                      <span class="w-6 h-6 bg-blue-500 text-white rounded flex items-center justify-center text-xs font-bold">{{ rule.ruleIndex + 1 }}</span>
                      <code class="text-xs bg-slate-100 px-2 py-1 rounded font-mono">{{ rule.ruleString }}</code>
                    </div>
                    <span v-if="rule.conflicting" class="px-2 py-0.5 bg-orange-100 text-orange-700 text-xs rounded flex items-center gap-1">
                      <span class="material-symbols-outlined text-xs">warning</span>
                      {{ t('app.conflicts') }}
                    </span>
                  </div>
                  <div class="grid grid-cols-3 gap-2 text-xs text-slate-600">
                    <div>{{ t('app.step') }}: <span class="font-medium">{{ getStepLabel(rule.triggerStep) }}</span></div>
                    <div>{{ t('app.device') }}: <span class="font-medium">{{ rule.targetDevice }}</span></div>
                    <div>{{ t('app.action') }}: <span class="font-medium">{{ rule.targetAction }}</span></div>
                  </div>
                  <div v-if="rule.reason" class="mt-2 text-xs text-slate-500 flex items-start gap-1">
                    <span class="material-symbols-outlined text-xs mt-0.5">info</span>
                    {{ rule.reason }}
                  </div>
                </div>
              </div>
            </div>
          </div>

          <!-- Other Strategies -->
          <div v-if="fixResult.suggestions.length > 1" class="border border-slate-200 rounded-xl p-4">
            <div class="text-sm font-bold text-slate-700 mb-3 flex items-center gap-2">
              <span class="material-symbols-outlined text-slate-600">layers</span>
              {{ t('app.otherAvailableStrategies') }}
            </div>
            <div class="flex flex-wrap gap-2">
              <button
                v-for="s in fixResult.suggestions"
                :key="s.strategy"
                v-show="s.strategy !== selectedStrategy"
                @click="switchStrategy(s.strategy)"
                class="px-4 py-2 rounded-lg text-sm font-medium transition-colors flex items-center gap-2"
                :class="s.verified 
                  ? 'bg-green-100 text-green-700 hover:bg-green-200 border border-green-300' 
                  : 'bg-slate-100 text-slate-600 hover:bg-slate-200 border border-slate-300'"
              >
                <span class="material-symbols-outlined text-sm">
                  {{ strategyIcons[s.strategy] }}
                </span>
                {{ strategyLabels[s.strategy] }}
                <span v-if="s.verified" class="material-symbols-outlined text-green-600 text-xs">verified</span>
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
            @click="closeDialog"
            class="px-6 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg font-medium transition-colors flex items-center gap-2"
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
