<script setup lang="ts">
import { ref, computed, watch } from 'vue'
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

// Get verified strategies count
const verifiedCount = computed(() => {
  if (!fixResult.value) return 0
  return fixResult.value.suggestions.filter(s => s.verified).length
})

// Get step label
const getStepLabel = (step: number) => {
  return step === 0 ? 'Initial State' : `Step ${step}`
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
</script>

<template>
  <!-- Fix Result Dialog - Following Verification Result Style -->
  <div v-if="visible" class="fixed inset-0 bg-black/60 backdrop-blur-sm flex items-center justify-center z-50" @click="closeDialog">
    <div class="bg-white rounded-2xl w-[800px] max-w-[95vw] shadow-2xl max-h-[85vh] flex flex-col border border-slate-200" @click.stop>
      
      <!-- Header -->
      <div class="relative overflow-hidden rounded-t-2xl border-b" :class="verifiedCount > 0 ? 'bg-amber-50 border-amber-200' : 'bg-red-50 border-red-200'">
        <div class="relative flex items-center justify-between p-5">
          <div class="flex items-center gap-4">
            <div class="w-12 h-12 rounded-xl flex items-center justify-center shadow-sm" :class="verifiedCount > 0 ? 'bg-amber-100' : 'bg-red-100'">
              <span class="material-symbols-outlined text-2xl" :class="verifiedCount > 0 ? 'text-amber-600' : 'text-red-600'">
                {{ verifiedCount > 0 ? 'build' : 'error' }}
              </span>
            </div>
            <div>
              <h3 class="text-xl font-bold text-slate-800">Fix Suggestions</h3>
              <p class="text-sm text-slate-600">{{ verifiedCount > 0 ? `${verifiedCount} solution(s) verified` : 'No verified solutions yet' }}</p>
            </div>
          </div>
          <button @click="closeDialog" class="w-9 h-9 flex items-center justify-center rounded-lg text-slate-500 hover:text-slate-700 hover:bg-slate-200 transition-all">
            <span class="material-symbols-outlined text-xl">close</span>
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
          <span class="text-slate-600 font-medium">Analyzing trace and generating suggestions...</span>
        </div>

        <div v-else-if="fixResult" class="space-y-4">
          
          <!-- Violation Info Card -->
          <div class="p-5 rounded-xl bg-gradient-to-r from-red-50 to-orange-50 border border-red-200">
            <div class="flex items-center gap-3">
              <div class="w-10 h-10 rounded-xl flex items-center justify-center bg-red-100">
                <span class="material-symbols-outlined text-red-600">warning</span>
              </div>
              <div class="flex-1">
                <span class="text-lg font-bold text-red-800">Violation Detected</span>
                <div class="flex items-center gap-2 mt-1">
                  <span class="px-2 py-0.5 bg-red-100 text-red-700 text-xs rounded font-mono">{{ fixResult.violatedSpecId }}</span>
                  <span class="text-sm text-red-600">{{ faultRules.length }} fault rule(s) identified</span>
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
                <span class="font-bold text-slate-800">Fix Strategies</span>
              </div>
            </div>
            
            <div class="p-4">
              <!-- Strategy Buttons -->
              <div class="flex gap-2 mb-4">
                <button
                  v-for="(label, key) in strategyLabels"
                  :key="key"
                  @click="switchStrategy(key)"
                  class="flex-1 px-4 py-3 rounded-lg font-medium text-sm transition-all flex items-center justify-center gap-2"
                  :class="selectedStrategy === key 
                    ? 'bg-blue-500 text-white shadow-md' 
                    : 'bg-slate-100 text-slate-600 hover:bg-slate-200'"
                >
                  <span class="material-symbols-outlined text-lg">
                    {{ key === 'parameter' ? 'tune' : key === 'condition' ? 'checklist' : 'block' }}
                  </span>
                  {{ label }}
                </button>
              </div>

              <!-- Strategy Description -->
              <div class="text-sm text-slate-500 mb-4 pl-1">
                {{ strategyDescriptions[selectedStrategy] }}
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
                        {{ currentSuggestion.verified ? 'Verified Solution' : 'Not Verified' }}
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
                    Parameter Adjustments ({{ currentSuggestion.parameterAdjustments.length }})
                  </div>
                  <div class="space-y-2">
                    <div
                      v-for="(adj, idx) in currentSuggestion.parameterAdjustments"
                      :key="idx"
                      class="bg-blue-50 border border-blue-200 rounded-lg p-3"
                    >
                      <div class="flex items-center justify-between">
                        <div class="flex items-center gap-2">
                          <span class="px-2 py-0.5 bg-blue-500 text-white text-xs rounded font-bold">Rule {{ adj.ruleIndex + 1 }}</span>
                          <code class="text-sm font-mono text-slate-700">{{ adj.attribute }} {{ adj.relation }}</code>
                        </div>
                        <span class="text-xs text-slate-500">Range: [{{ adj.lowerBound }}, {{ adj.upperBound }}]</span>
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
                    Condition Adjustments ({{ currentSuggestion.conditionAdjustments.length }})
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
                        {{ adj.action }}
                      </span>
                    </div>
                  </div>
                </div>

                <!-- Disabled Rules -->
                <div v-if="currentSuggestion.disabledRuleIndices?.length" class="mb-4">
                  <div class="flex items-center gap-2 mb-2 text-sm font-bold text-slate-700">
                    <span class="material-symbols-outlined text-orange-500">block</span>
                    Rules to Disable ({{ currentSuggestion.disabledRuleIndices.length }})
                  </div>
                  <div class="bg-orange-50 border border-orange-200 rounded-lg p-3">
                    <div class="flex flex-wrap gap-2">
                      <span 
                        v-for="idx in currentSuggestion.disabledRuleIndices" 
                        :key="idx"
                        class="px-3 py-1 bg-orange-500 text-white rounded-lg text-sm font-medium"
                      >
                        Rule {{ idx + 1 }}
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
                    {{ applyingFix ? 'Applying...' : 'Apply This Fix' }}
                  </button>
                </div>
                <div v-else class="pt-4 border-t border-slate-200 text-center">
                  <div class="flex items-center justify-center gap-2 text-red-600">
                    <span class="material-symbols-outlined">info</span>
                    <span class="font-medium">This solution did not pass verification</span>
                  </div>
                  <p class="text-xs text-red-500 mt-1">Try another strategy or wait for the system to find a verified solution</p>
                </div>
              </div>

              <div v-else class="text-center py-8 text-slate-400">
                <span class="material-symbols-outlined text-4xl mb-2 block">help</span>
                <p>No fix suggestions available for this strategy</p>
              </div>
            </div>
          </div>

          <!-- Fault Rules Section -->
          <div class="border border-slate-200 rounded-xl overflow-hidden">
            <div class="bg-slate-50 px-4 py-3 border-b border-slate-200">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-slate-600">search</span>
                <span class="font-bold text-slate-800">Fault Localization</span>
                <span class="ml-auto px-2 py-0.5 bg-red-100 text-red-700 text-xs rounded-full">{{ faultRules.length }} rule(s)</span>
              </div>
            </div>
            
            <div class="p-4">
              <div v-if="faultRules.length === 0" class="text-center py-8 text-slate-400">
                <span class="material-symbols-outlined text-4xl mb-2 block">check_circle</span>
                <p>No fault rules found in counterexample trace</p>
                <p class="text-xs mt-1">The violation may be caused by device transitions</p>
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
                      Conflicts
                    </span>
                  </div>
                  <div class="grid grid-cols-3 gap-2 text-xs text-slate-600">
                    <div>Step: <span class="font-medium">{{ getStepLabel(rule.triggerStep) }}</span></div>
                    <div>Device: <span class="font-medium">{{ rule.targetDevice }}</span></div>
                    <div>Action: <span class="font-medium">{{ rule.targetAction }}</span></div>
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
              Other Available Strategies
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
                  {{ s.strategy === 'parameter' ? 'tune' : s.strategy === 'condition' ? 'checklist' : 'block' }}
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
            @click="closeDialog"
            class="px-6 py-2 bg-slate-200 hover:bg-slate-300 text-slate-700 rounded-lg font-medium transition-colors flex items-center gap-2"
          >
            <span class="material-symbols-outlined text-sm">close</span>
            Close
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
