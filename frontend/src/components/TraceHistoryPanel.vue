<script setup lang="ts">
import type { Trace } from '@/types/verify'
import type { SimulationTraceSummary } from '@/types/simulation'
import { useI18n } from 'vue-i18n'

type HistoryTab = 'verification' | 'simulation'

defineProps<{
  activeTab: HistoryTab
  verificationTraces: Trace[]
  simulationTraces: SimulationTraceSummary[]
  loadingVerification: boolean
  loadingSimulation: boolean
  actionLocked: boolean
}>()

const emit = defineEmits<{
  (e: 'update:activeTab', value: HistoryTab): void
  (e: 'close'): void
  (e: 'refresh-verification'): void
  (e: 'refresh-simulation'): void
  (e: 'view-verification', id: number): void
  (e: 'fix-verification', trace: Trace): void
  (e: 'delete-verification', id: number): void
  (e: 'view-simulation', id: number): void
  (e: 'delete-simulation', id: number): void
}>()

const { t } = useI18n()

const formatDate = (value?: string) => {
  if (!value) return ''
  const date = new Date(value)
  return Number.isNaN(date.getTime()) ? value : date.toLocaleString()
}
</script>

<template>
  <div class="board-floating-panel fixed top-20 z-30 w-[420px] max-w-[calc(100vw-2rem)] bg-white dark:bg-slate-900 rounded-2xl shadow-2xl border border-slate-200/60 dark:border-slate-700 overflow-hidden">
    <div class="relative overflow-hidden">
      <div class="absolute inset-0 bg-gradient-to-br from-slate-700 to-cyan-700"></div>
      <div class="relative flex items-center justify-between p-4">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-cyan-600 rounded-xl flex items-center justify-center shadow-lg">
            <span class="material-symbols-outlined text-white text-xl">history</span>
          </div>
          <div>
            <h3 class="text-white font-bold text-base">{{ t('app.runHistory') }}</h3>
            <p class="text-white/75 text-xs">{{ t('app.runHistorySubtitle') }}</p>
          </div>
        </div>
        <button
          @click="emit('close')"
          class="w-8 h-8 flex items-center justify-center rounded-lg text-white/75 hover:text-white hover:bg-white/10 transition-all"
          :title="t('app.close')"
        >
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>
    </div>

    <div class="p-3 bg-slate-50 dark:bg-slate-950 border-b border-slate-200 dark:border-slate-700">
      <div class="grid grid-cols-2 gap-1 rounded-lg bg-slate-200 dark:bg-slate-800 p-1">
        <button
          type="button"
          @click="emit('update:activeTab', 'verification')"
          class="px-3 py-2 rounded-md text-xs font-bold transition-colors flex items-center justify-center gap-1"
          :class="activeTab === 'verification' ? 'bg-white dark:bg-slate-700 text-cyan-700 dark:text-cyan-200 shadow-sm' : 'text-slate-600 dark:text-slate-300 hover:text-slate-800 dark:hover:text-white'"
        >
          <span class="material-symbols-outlined text-sm">verified_user</span>
          {{ t('app.verification') }}
        </button>
        <button
          type="button"
          @click="emit('update:activeTab', 'simulation')"
          class="px-3 py-2 rounded-md text-xs font-bold transition-colors flex items-center justify-center gap-1"
          :class="activeTab === 'simulation' ? 'bg-white dark:bg-slate-700 text-cyan-700 dark:text-cyan-200 shadow-sm' : 'text-slate-600 dark:text-slate-300 hover:text-slate-800 dark:hover:text-white'"
        >
          <span class="material-symbols-outlined text-sm">play_circle</span>
          {{ t('app.simulation') }}
        </button>
      </div>
    </div>

    <div class="p-3 bg-white dark:bg-slate-900 max-h-[560px] overflow-y-auto">
      <div v-if="activeTab === 'verification'" class="space-y-3">
        <div class="flex items-center justify-between px-1">
          <span class="text-xs font-medium text-slate-500 dark:text-slate-400">
            {{ t('app.traceCount', { count: verificationTraces.length }) }}
          </span>
          <button
            type="button"
            @click="emit('refresh-verification')"
            class="text-xs text-cyan-700 dark:text-cyan-300 hover:text-cyan-800 dark:hover:text-cyan-200 font-medium flex items-center gap-1"
            :disabled="loadingVerification"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingVerification ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingVerification" class="flex flex-col items-center justify-center py-10 text-slate-500 dark:text-slate-400">
          <span class="material-symbols-outlined text-4xl animate-spin text-cyan-600">sync</span>
          <p class="text-sm mt-3">{{ t('app.loadingVerificationTraces') }}</p>
        </div>

        <div v-else-if="verificationTraces.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-14 h-14 bg-slate-100 dark:bg-slate-800 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 dark:text-slate-500 text-3xl">rule</span>
          </div>
          <p class="text-slate-600 dark:text-slate-300 text-sm font-medium">{{ t('app.noVerificationTraces') }}</p>
          <p class="text-slate-400 dark:text-slate-500 text-xs mt-1 text-center px-4">{{ t('app.noVerificationTracesHint') }}</p>
        </div>

        <div v-else class="space-y-2">
          <div
            v-for="trace in verificationTraces"
            :key="trace.id"
            class="bg-white dark:bg-slate-800 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm p-3 hover:border-cyan-200 dark:hover:border-cyan-600 transition-colors"
          >
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0">
                <div class="flex items-center gap-2">
                  <span class="text-xs font-bold text-cyan-700 dark:text-cyan-300">{{ t('app.traceNumber', { id: trace.id }) }}</span>
                  <span class="px-2 py-0.5 bg-red-50 dark:bg-red-950/50 text-red-600 dark:text-red-300 rounded-full text-[11px] font-medium">
                    {{ t('app.statesCount', { count: trace.states?.length || 0 }) }}
                  </span>
                </div>
                <div class="text-xs text-slate-600 dark:text-slate-300 mt-1 truncate">
                  {{ t('app.specPrefix') }}: {{ trace.violatedSpecId }}
                </div>
                <div class="text-xs text-slate-400 dark:text-slate-500 mt-1">{{ formatDate(trace.createdAt) }}</div>
              </div>
              <div class="flex flex-wrap justify-end gap-1 shrink-0">
                <button
                  type="button"
                  @click="emit('view-verification', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.view') }}
                </button>
                <button
                  type="button"
                  @click="emit('fix-verification', trace)"
                  :disabled="actionLocked || !trace.violatedSpecId"
                  :title="t('app.historicalFixMayFailIfBoardChanged')"
                  class="px-2 py-1 bg-blue-600 hover:bg-blue-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.fix') }}
                </button>
                <button
                  type="button"
                  @click="emit('delete-verification', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-slate-100 dark:bg-slate-700 hover:bg-red-50 dark:hover:bg-red-950/50 text-slate-700 dark:text-slate-200 hover:text-red-700 dark:hover:text-red-300 rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.delete') }}
                </button>
              </div>
            </div>
          </div>
        </div>
      </div>

      <div v-else class="space-y-3">
        <div class="flex items-center justify-between px-1">
          <span class="text-xs font-medium text-slate-500 dark:text-slate-400">
            {{ t('app.runCount', { count: simulationTraces.length }) }}
          </span>
          <button
            type="button"
            @click="emit('refresh-simulation')"
            class="text-xs text-cyan-700 dark:text-cyan-300 hover:text-cyan-800 dark:hover:text-cyan-200 font-medium flex items-center gap-1"
            :disabled="loadingSimulation"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingSimulation ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingSimulation" class="flex flex-col items-center justify-center py-10 text-slate-500 dark:text-slate-400">
          <span class="material-symbols-outlined text-4xl animate-spin text-cyan-600">sync</span>
          <p class="text-sm mt-3">{{ t('app.loadingSimulationRuns') }}</p>
        </div>

        <div v-else-if="simulationTraces.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="w-14 h-14 bg-slate-100 dark:bg-slate-800 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 dark:text-slate-500 text-3xl">timeline</span>
          </div>
          <p class="text-slate-600 dark:text-slate-300 text-sm font-medium">{{ t('app.noSimulationRuns') }}</p>
          <p class="text-slate-400 dark:text-slate-500 text-xs mt-1 text-center px-4">{{ t('app.noSimulationRunsHint') }}</p>
        </div>

        <div v-else class="space-y-2">
          <div
            v-for="trace in simulationTraces"
            :key="trace.id"
            class="bg-white dark:bg-slate-800 rounded-lg border border-slate-200 dark:border-slate-700 shadow-sm p-3 hover:border-cyan-200 dark:hover:border-cyan-600 transition-colors"
          >
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0">
                <div class="flex items-center gap-2">
                  <span class="text-xs font-bold text-cyan-700 dark:text-cyan-300">{{ t('app.runNumber', { id: trace.id }) }}</span>
                  <span class="px-2 py-0.5 bg-blue-50 dark:bg-blue-950/50 text-blue-600 dark:text-blue-300 rounded-full text-[11px] font-medium">
                    {{ t('app.stepsCount', { steps: trace.steps, requestedSteps: trace.requestedSteps }) }}
                  </span>
                </div>
                <div class="text-xs text-slate-400 dark:text-slate-500 mt-1">{{ formatDate(trace.createdAt) }}</div>
              </div>
              <div class="flex flex-wrap justify-end gap-1 shrink-0">
                <button
                  type="button"
                  @click="emit('view-simulation', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.replay') }}
                </button>
                <button
                  type="button"
                  @click="emit('delete-simulation', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-slate-100 dark:bg-slate-700 hover:bg-red-50 dark:hover:bg-red-950/50 text-slate-700 dark:text-slate-200 hover:text-red-700 dark:hover:text-red-300 rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.delete') }}
                </button>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>
