<script setup lang="ts">
import { ref, computed } from 'vue'
import { ElMessage } from 'element-plus'
import boardApi from '@/api/board'
import type { FixResult, FixSuggestion, FaultRule } from '@/types/fix'

const props = defineProps<{
  visible: boolean
  traceId: number
  violatedSpecId?: string
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'applied': []
}>()

const loading = ref(false)
const fixResult = ref<FixResult | null>(null)
const faultRules = ref<FaultRule[]>([])
const selectedStrategy = ref<string>('parameter')
const applyingFix = ref(false)

const strategyLabels: Record<string, string> = {
  parameter: 'Parameter Adjustment',
  condition: 'Condition Adjustment',
  disable: 'Disable Rules'
}

const strategyDescriptions: Record<string, string> = {
  parameter: 'Modify condition values to prevent rule triggering',
  condition: 'Add or remove conditions to refine rule scope',
  disable: 'Completely disable problematic rules'
}

const strategyColors: Record<string, string> = {
  parameter: 'from-blue-500 to-blue-600',
  condition: 'from-emerald-500 to-emerald-600',
  disable: 'from-orange-500 to-orange-600'
}

// Fetch fault localization
const fetchFaultRules = async () => {
  if (!props.traceId) return
  
  loading.value = true
  try {
    faultRules.value = await boardApi.getFaultRules(props.traceId)
  } catch (error) {
    console.error('Failed to fetch fault rules:', error)
    ElMessage.error('Failed to load fault localization')
  } finally {
    loading.value = false
  }
}

// Fetch fix suggestions
const fetchFixSuggestions = async () => {
  if (!props.traceId) return
  
  loading.value = true
  try {
    fixResult.value = await boardApi.fixTrace(props.traceId, {
      strategies: [selectedStrategy.value]
    })
  } catch (error) {
    console.error('Failed to fetch fix suggestions:', error)
    ElMessage.error('Failed to load fix suggestions')
  } finally {
    loading.value = false
  }
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
  loadData()
}

// Switch strategy
const switchStrategy = async (strategy: string) => {
  selectedStrategy.value = strategy
  await fetchFixSuggestions()
}

// Apply fix
const applyFix = async (suggestion: FixSuggestion) => {
  applyingFix.value = true
  try {
    // TODO: Implement actual fix application logic
    console.log('Applying fix:', suggestion)
    ElMessage.success('Fix applied successfully')
    emit('applied')
    emit('update:visible', false)
  } catch (error) {
    console.error('Failed to apply fix:', error)
    ElMessage.error('Failed to apply fix')
  } finally {
    applyingFix.value = false
  }
}

// Current strategy suggestion
const currentSuggestion = computed(() => {
  if (!fixResult.value) return null
  return fixResult.value.suggestions.find(s => s.strategy === selectedStrategy.value)
})

// Format parameter adjustment
const formatParameterAdjustment = (adj: any) => {
  return `${adj.attribute} ${adj.relation} ${adj.originalValue} → ${adj.newValue}`
}

// Format condition adjustment
const formatConditionAdjustment = (adj: any) => {
  if (adj.action === 'remove') {
    return `Remove condition: ${adj.attribute}`
  } else if (adj.action === 'add') {
    return `Add condition: ${adj.deviceName}.${adj.attribute} ${adj.relation} ${adj.value}`
  }
  return adj.description
}

// Get step label
const getStepLabel = (step: number) => {
  return step === 0 ? 'Initial State' : `Step ${step}`
}
</script>

<template>
  <el-dialog
    :model-value="visible"
    @update:model-value="$emit('update:visible', $event)"
    title="Fault Localization & Fix"
    width="900px"
    :before-close="() => $emit('update:visible', false)"
    @open="handleOpen"
    class="fix-dialog"
  >
    <!-- Loading State -->
    <div v-if="loading" class="flex flex-col items-center justify-center py-16">
      <div class="animate-spin rounded-full h-12 w-12 border-4 border-blue-500 border-t-transparent mb-4"></div>
      <span class="text-slate-500">Analyzing trace and generating suggestions...</span>
    </div>

    <div v-else-if="fixResult" class="space-y-6">
      <!-- Violation Summary -->
      <div class="bg-gradient-to-r from-red-50 to-orange-50 border border-red-200 rounded-xl p-5">
        <div class="flex items-start gap-3">
          <div class="flex-shrink-0 w-10 h-10 bg-red-100 rounded-full flex items-center justify-center">
            <svg class="w-6 h-6 text-red-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z"></path>
            </svg>
          </div>
          <div class="flex-1">
            <div class="flex items-center gap-2 mb-1">
              <span class="text-lg font-semibold text-red-800">Violated Specification</span>
              <code class="px-2 py-0.5 bg-red-100 text-red-700 rounded text-sm font-mono">{{ fixResult.violatedSpecId }}</code>
            </div>
            <p class="text-sm text-red-700">{{ fixResult.summary }}</p>
          </div>
        </div>
      </div>

      <!-- Fault Localization Section -->
      <div class="border border-slate-200 rounded-xl overflow-hidden">
        <div class="bg-slate-50 px-5 py-3 border-b border-slate-200 flex items-center gap-2">
          <svg class="w-5 h-5 text-slate-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z"></path>
          </svg>
          <h3 class="font-semibold text-slate-800">Fault Localization</h3>
          <span v-if="faultRules.length > 0" class="ml-auto px-2 py-0.5 bg-blue-100 text-blue-700 text-xs rounded-full">
            {{ faultRules.length }} rule(s) identified
          </span>
        </div>
        
        <div class="p-5">
          <div v-if="faultRules.length === 0" class="text-center py-8">
            <svg class="w-16 h-16 mx-auto text-slate-300 mb-3" fill="none" stroke="currentColor" viewBox="0 0 24 24">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="1.5" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z"></path>
            </svg>
            <p class="text-slate-500 mb-1">No fault rules found in counterexample trace</p>
            <p class="text-sm text-slate-400">The violation may be caused by device transitions or environment conditions</p>
          </div>
          
          <div v-else class="space-y-3">
            <div
              v-for="(rule, idx) in faultRules"
              :key="idx"
              class="bg-white border border-slate-200 rounded-lg p-4 hover:shadow-md transition-shadow"
              :class="{ 'border-orange-300 bg-orange-50': rule.conflicting }"
            >
              <div class="flex items-start justify-between gap-4">
                <div class="flex items-center gap-2">
                  <span class="w-6 h-6 bg-blue-100 text-blue-700 rounded-full flex items-center justify-center text-sm font-medium">
                    {{ rule.ruleIndex + 1 }}
                  </span>
                  <code class="text-sm bg-slate-100 px-2 py-1 rounded font-mono text-slate-700">{{ rule.ruleString }}</code>
                </div>
                <el-tag v-if="rule.conflicting" type="warning" size="small">
                  Conflicts with Rule {{ rule.conflictWithRuleIndex! + 1 }}
                </el-tag>
              </div>
              
              <div class="mt-3 grid grid-cols-3 gap-4 text-sm">
                <div class="flex items-center gap-2">
                  <span class="text-slate-400">Trigger Step:</span>
                  <span class="font-medium text-slate-700">{{ getStepLabel(rule.triggerStep) }}</span>
                </div>
                <div class="flex items-center gap-2">
                  <span class="text-slate-400">Target Device:</span>
                  <span class="font-medium text-slate-700">{{ rule.targetDevice }}</span>
                </div>
                <div class="flex items-center gap-2">
                  <span class="text-slate-400">Action:</span>
                  <span class="font-medium text-slate-700">{{ rule.targetAction }}</span>
                </div>
              </div>
              
              <div v-if="rule.reason" class="mt-2 text-sm text-slate-500 flex items-start gap-2">
                <svg class="w-4 h-4 mt-0.5 flex-shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z"></path>
                </svg>
                {{ rule.reason }}
              </div>
            </div>
          </div>
        </div>
      </div>

      <!-- Fix Suggestions Section -->
      <div class="border border-slate-200 rounded-xl overflow-hidden">
        <div class="bg-slate-50 px-5 py-3 border-b border-slate-200 flex items-center gap-2">
          <svg class="w-5 h-5 text-slate-600" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M10.325 4.317c.426-1.756 2.924-1.756 3.35 0a1.724 1.724 0 002.573 1.066c1.543-.94 3.31.826 2.37 2.37a1.724 1.724 0 001.065 2.572c1.756.426 1.756 2.924 0 3.35a1.724 1.724 0 00-1.066 2.573c.94 1.543-.826 3.31-2.37 2.37a1.724 1.724 0 00-2.572 1.065c-.426 1.756-2.924 1.756-3.35 0a1.724 1.724 0 00-2.573-1.066c-1.543.94-3.31-.826-2.37-2.37a1.724 1.724 0 00-1.065-2.572c-1.756-.426-1.756-2.924 0-3.35a1.724 1.724 0 001.066-2.573c-.94-1.543.826-3.31 2.37-2.37.996.608 2.296.07 2.572-1.065z"></path>
            <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15 12a3 3 0 11-6 0 3 3 0 016 0z"></path>
          </svg>
          <h3 class="font-semibold text-slate-800">Fix Suggestions</h3>
        </div>
        
        <div class="p-5">
          <!-- Strategy Tabs -->
          <div class="flex gap-2 mb-6">
            <button
              v-for="(label, key) in strategyLabels"
              :key="key"
              @click="switchStrategy(key)"
              class="flex-1 px-4 py-3 rounded-lg font-medium text-sm transition-all"
              :class="selectedStrategy === key 
                ? `bg-gradient-to-r ${strategyColors[key]} text-white shadow-md` 
                : 'bg-slate-100 text-slate-600 hover:bg-slate-200'"
            >
              {{ label }}
            </button>
          </div>

          <!-- Strategy Description -->
          <div class="mb-4 text-sm text-slate-500">
            {{ strategyDescriptions[selectedStrategy] }}
          </div>

          <!-- Current Strategy Suggestion -->
          <div v-if="currentSuggestion" class="space-y-4">
            <div class="border border-slate-200 rounded-lg overflow-hidden">
              <!-- Suggestion Header -->
              <div class="bg-slate-50 px-4 py-3 flex items-center justify-between">
                <div class="flex items-center gap-2">
                  <span 
                    class="px-2 py-1 rounded text-xs font-medium"
                    :class="currentSuggestion.verified ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'"
                  >
                    {{ currentSuggestion.verified ? '✓ Verified' : '✗ Not Verified' }}
                  </span>
                </div>
                <span class="text-sm text-slate-500">
                  {{ currentSuggestion.description }}
                </span>
              </div>
              
              <!-- Suggestion Content -->
              <div class="p-4 space-y-4">
                <!-- Parameter Adjustments -->
                <div v-if="currentSuggestion.parameterAdjustments?.length" class="space-y-2">
                  <div class="text-sm font-medium text-slate-700 flex items-center gap-2">
                    <svg class="w-4 h-4 text-blue-500" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M7 7h.01M7 3h5c.512 0 1.024.195 1.414.586l7 7a2 2 0 010 2.828l-7 7a2 2 0 01-2.828 0l-7-7A1.994 1.994 0 013 12V7a4 4 0 014-4z"></path>
                    </svg>
                    Parameter Adjustments
                  </div>
                  <div
                    v-for="(adj, idx) in currentSuggestion.parameterAdjustments"
                    :key="idx"
                    class="bg-blue-50 border border-blue-200 rounded-lg px-4 py-3"
                  >
                    <div class="flex items-center justify-between">
                      <div class="font-mono text-sm">
                        <span class="text-blue-700">Rule {{ adj.ruleIndex + 1 }}</span>
                        <span class="text-slate-500 mx-2">:</span>
                        <span class="text-slate-700">{{ formatParameterAdjustment(adj) }}</span>
                      </div>
                      <span class="text-xs text-slate-500">
                        Range: [{{ adj.lowerBound }}, {{ adj.upperBound }}]
                      </span>
                    </div>
                  </div>
                </div>
                
                <!-- Condition Adjustments -->
                <div v-if="currentSuggestion.conditionAdjustments?.length" class="space-y-2">
                  <div class="text-sm font-medium text-slate-700 flex items-center gap-2">
                    <svg class="w-4 h-4 text-emerald-500" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z"></path>
                    </svg>
                    Condition Adjustments
                  </div>
                  <div
                    v-for="(adj, idx) in currentSuggestion.conditionAdjustments"
                    :key="idx"
                    class="bg-emerald-50 border border-emerald-200 rounded-lg px-4 py-3 text-sm"
                  >
                    {{ formatConditionAdjustment(adj) }}
                  </div>
                </div>
                
                <!-- Disabled Rules -->
                <div v-if="currentSuggestion.disabledRuleIndices?.length" class="space-y-2">
                  <div class="text-sm font-medium text-slate-700 flex items-center gap-2">
                    <svg class="w-4 h-4 text-orange-500" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                      <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M18.364 18.364A9 9 0 005.636 5.636m12.728 12.728A9 9 0 015.636 5.636m12.728 12.728L5.636 5.636"></path>
                    </svg>
                    Rules to Disable
                  </div>
                  <div class="bg-orange-50 border border-orange-200 rounded-lg px-4 py-3">
                    <div class="flex flex-wrap gap-2">
                      <span 
                        v-for="idx in currentSuggestion.disabledRuleIndices" 
                        :key="idx"
                        class="px-2 py-1 bg-orange-100 text-orange-700 rounded text-sm font-medium"
                      >
                        Rule {{ idx + 1 }}
                      </span>
                    </div>
                  </div>
                </div>
              </div>
            </div>

            <!-- Apply Fix Button -->
            <div v-if="currentSuggestion.verified" class="flex justify-end">
              <el-button 
                type="primary" 
                size="large"
                :loading="applyingFix"
                @click="applyFix(currentSuggestion)"
                class="px-8"
              >
                <svg v-if="!applyingFix" class="w-5 h-5 mr-2" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M5 13l4 4L19 7"></path>
                </svg>
                Apply This Fix
              </el-button>
            </div>
            <div v-else class="bg-red-50 border border-red-200 rounded-lg px-4 py-3 text-center text-red-600 text-sm">
              This fix solution did not pass verification and cannot be applied
            </div>
          </div>

          <div v-else class="text-center py-8 text-slate-400">
            No fix suggestions available for this strategy
          </div>

          <!-- Other Available Strategies -->
          <div v-if="fixResult.suggestions.length > 1" class="mt-6 pt-4 border-t border-slate-200">
            <div class="text-sm text-slate-500 mb-3">Other available strategies:</div>
            <div class="flex flex-wrap gap-2">
              <button
                v-for="s in fixResult.suggestions"
                :key="s.strategy"
                v-show="s.strategy !== selectedStrategy"
                @click="switchStrategy(s.strategy)"
                class="px-3 py-1.5 rounded-lg text-sm font-medium transition-colors"
                :class="s.verified 
                  ? 'bg-green-100 text-green-700 hover:bg-green-200' 
                  : 'bg-slate-100 text-slate-600 hover:bg-slate-200'"
              >
                {{ strategyLabels[s.strategy] }}
                <span class="ml-1">{{ s.verified ? '✓' : '(unverified)' }}</span>
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>

    <template #footer>
      <el-button @click="$emit('update:visible', false)">Close</el-button>
    </template>
  </el-dialog>
</template>

<style scoped>
:deep(.el-dialog__header) {
  background: linear-gradient(135deg, #1e293b 0%, #334155 100%);
  padding: 16px 20px;
  margin: 0;
}

:deep(.el-dialog__title) {
  color: white;
  font-weight: 600;
}

:deep(.el-dialog__headerbtn .el-dialog__close) {
  color: white;
}

:deep(.el-dialog__body) {
  padding: 20px;
  max-height: 70vh;
  overflow-y: auto;
}

:deep(.el-dialog__footer) {
  border-top: 1px solid #e2e8f0;
  padding: 12px 20px;
}
</style>
