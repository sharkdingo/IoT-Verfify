<script setup lang="ts">
import { computed } from 'vue'
import type { Trace, VerificationTaskSummary } from '@/types/verify'
import type { SimulationTaskSummary, SimulationTraceSummary } from '@/types/simulation'
import { useI18n } from 'vue-i18n'

type HistoryTab = 'tasks' | 'verification' | 'simulation'
type TaskKind = 'verification' | 'simulation'
type TaskStatus = 'PENDING' | 'RUNNING' | 'COMPLETED' | 'FAILED' | 'CANCELLED'

type TaskItem =
  | (VerificationTaskSummary & { kind: 'verification' })
  | (SimulationTaskSummary & { kind: 'simulation' })

const props = defineProps<{
  activeTab: HistoryTab
  verificationTasks: VerificationTaskSummary[]
  simulationTasks: SimulationTaskSummary[]
  verificationTraces: Trace[]
  simulationTraces: SimulationTraceSummary[]
  loadingTasks: boolean
  loadingVerification: boolean
  loadingSimulation: boolean
  actionLocked: boolean
}>()

const emit = defineEmits<{
  (e: 'update:activeTab', value: HistoryTab): void
  (e: 'close'): void
  (e: 'refresh-tasks'): void
  (e: 'refresh-verification'): void
  (e: 'refresh-simulation'): void
  (e: 'watch-verification-task', id: number): void
  (e: 'watch-simulation-task', id: number): void
  (e: 'view-verification-task', id: number): void
  (e: 'view-simulation-task', id: number): void
  (e: 'cancel-verification-task', id: number): void
  (e: 'cancel-simulation-task', id: number): void
  (e: 'view-verification', id: number): void
  (e: 'fix-verification', trace: Trace): void
  (e: 'delete-verification', id: number): void
  (e: 'view-simulation', id: number): void
  (e: 'delete-simulation', id: number): void
}>()

const { t } = useI18n()

const taskItems = computed<TaskItem[]>(() => [
  ...props.verificationTasks.map(task => ({ ...task, kind: 'verification' as const })),
  ...props.simulationTasks.map(task => ({ ...task, kind: 'simulation' as const }))
].sort((a, b) => timestamp(b.createdAt) - timestamp(a.createdAt)))

const activeTaskCount = computed(() =>
  taskItems.value.filter(task => isActiveStatus(task.status)).length
)

const formatDate = (value?: string) => {
  if (!value) return ''
  const date = new Date(value)
  return Number.isNaN(date.getTime()) ? value : date.toLocaleString()
}

const timestamp = (value?: string) => {
  if (!value) return 0
  const parsed = new Date(value).getTime()
  return Number.isNaN(parsed) ? 0 : parsed
}

const isActiveStatus = (status?: string) => status === 'PENDING' || status === 'RUNNING'
const isCompletedStatus = (status?: string) => status === 'COMPLETED'
const taskProgress = (task: TaskItem) => {
  const fallback = isActiveStatus(task.status) ? 0 : 100
  const numeric = typeof task.progress === 'number' ? task.progress : fallback
  if (!Number.isFinite(numeric)) return fallback
  return Math.min(100, Math.max(0, Math.round(numeric)))
}

const formatStatus = (status?: string) => {
  switch (status as TaskStatus | undefined) {
    case 'PENDING':
      return t('app.taskStatusPending')
    case 'RUNNING':
      return t('app.taskStatusRunning')
    case 'COMPLETED':
      return t('app.taskStatusCompleted')
    case 'FAILED':
      return t('app.taskStatusFailed')
    case 'CANCELLED':
      return t('app.taskStatusCancelled')
    default:
      return status || t('app.taskInitializing')
  }
}

const taskKindLabel = (kind: TaskKind) =>
  kind === 'verification' ? t('app.verification') : t('app.simulation')

const statusClass = (status?: string) => {
  switch (status) {
    case 'COMPLETED':
      return 'bg-green-50 text-green-700 border-green-200'
    case 'FAILED':
      return 'bg-red-50 text-red-700 border-red-200'
    case 'CANCELLED':
      return 'bg-slate-100 text-slate-600 border-slate-200'
    case 'PENDING':
    case 'RUNNING':
      return 'bg-blue-50 text-blue-700 border-blue-200'
    default:
      return 'bg-slate-100 text-slate-600 border-slate-200'
  }
}

const emitWatchTask = (task: TaskItem) => {
  if (task.kind === 'verification') {
    emit('watch-verification-task', task.id)
  } else {
    emit('watch-simulation-task', task.id)
  }
}

const emitViewTask = (task: TaskItem) => {
  if (task.kind === 'verification') {
    emit('view-verification-task', task.id)
  } else {
    emit('view-simulation-task', task.id)
  }
}

const emitCancelTask = (task: TaskItem) => {
  if (task.kind === 'verification') {
    emit('cancel-verification-task', task.id)
  } else {
    emit('cancel-simulation-task', task.id)
  }
}

const taskSecondaryText = (task: TaskItem) => {
  if (task.kind === 'verification') {
    if (task.status === 'COMPLETED') {
      return task.isSafe
        ? t('app.verificationPassed')
        : t('app.verificationFailedWithViolations', { count: task.violatedSpecCount || 0 })
    }
    return task.errorMessage || ''
  }

  if (task.status === 'COMPLETED') {
    return task.simulationTraceId
      ? t('app.savedTraceNumber', { id: task.simulationTraceId })
      : t('app.taskCompletedNoTraceFound')
  }
  return task.errorMessage || ''
}
</script>

<template>
  <div
    class="board-floating-panel board-surface-panel fixed top-20 z-30 w-[440px] max-w-[calc(100vw-2rem)] rounded-2xl shadow-2xl border overflow-hidden"
    data-testid="trace-history-panel"
  >
    <div class="relative overflow-hidden">
      <div class="absolute inset-0 bg-gradient-to-br from-slate-700 to-cyan-700"></div>
      <div class="relative flex items-center justify-between p-4">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-cyan-600 rounded-xl flex items-center justify-center shadow-lg">
            <span class="material-symbols-outlined text-white text-xl">inventory_2</span>
          </div>
          <div>
            <h3 class="text-white font-bold text-base">{{ t('app.runHistory') }}</h3>
            <p class="text-white/75 text-xs">{{ t('app.runHistorySubtitle') }}</p>
          </div>
        </div>
        <button
          @click="emit('close')"
          data-testid="close-history-panel"
          class="w-8 h-8 flex items-center justify-center rounded-lg text-white/75 hover:text-white hover:bg-white/10 transition-all"
          :title="t('app.close')"
        >
          <span class="material-symbols-outlined">close</span>
        </button>
      </div>
    </div>

    <div class="board-panel-tabs p-3 border-b">
      <div class="board-segmented grid grid-cols-3 gap-1 rounded-lg p-1">
        <button
          type="button"
          data-testid="history-tab-tasks"
          @click="emit('update:activeTab', 'tasks')"
          class="px-2 py-2 rounded-md text-xs font-bold transition-colors flex items-center justify-center gap-1"
          :class="activeTab === 'tasks' ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-600 hover:text-slate-800'"
        >
          <span class="material-symbols-outlined text-sm">inbox</span>
          {{ t('app.taskInbox') }}
        </button>
        <button
          type="button"
          data-testid="history-tab-verification"
          @click="emit('update:activeTab', 'verification')"
          class="px-2 py-2 rounded-md text-xs font-bold transition-colors flex items-center justify-center gap-1"
          :class="activeTab === 'verification' ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-600 hover:text-slate-800'"
        >
          <span class="material-symbols-outlined text-sm">verified_user</span>
          {{ t('app.savedVerificationTraces') }}
        </button>
        <button
          type="button"
          data-testid="history-tab-simulation"
          @click="emit('update:activeTab', 'simulation')"
          class="px-2 py-2 rounded-md text-xs font-bold transition-colors flex items-center justify-center gap-1"
          :class="activeTab === 'simulation' ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-600 hover:text-slate-800'"
        >
          <span class="material-symbols-outlined text-sm">play_circle</span>
          {{ t('app.savedSimulationRuns') }}
        </button>
      </div>
    </div>

    <div class="board-panel-body p-3 max-h-[560px] overflow-y-auto">
      <div
        v-if="actionLocked"
        class="mb-3 flex items-start gap-2 rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs text-amber-800"
      >
        <span class="material-symbols-outlined text-sm">lock</span>
        <span>{{ t('app.historyActionsLockedHint') }}</span>
      </div>

      <div v-if="activeTab === 'tasks'" class="space-y-3">
        <div class="flex items-center justify-between px-1">
          <span class="text-xs font-medium text-slate-500">
            {{ t('app.taskCount', { count: taskItems.length }) }}
            <span v-if="activeTaskCount > 0" class="ml-1 text-blue-600">
              {{ t('app.activeTaskCount', { count: activeTaskCount }) }}
            </span>
          </span>
          <button
            type="button"
            @click="emit('refresh-tasks')"
            class="text-xs text-cyan-700 hover:text-cyan-800 font-medium flex items-center gap-1"
            :disabled="loadingTasks"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingTasks ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingTasks" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined text-4xl animate-spin text-cyan-600">sync</span>
          <p class="text-sm mt-3">{{ t('app.loadingTasks') }}</p>
        </div>

        <div v-else-if="taskItems.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="board-muted-surface w-14 h-14 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">inbox</span>
          </div>
          <p class="text-slate-600 text-sm font-medium">{{ t('app.noTasks') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.noTasksHint') }}</p>
        </div>

        <div v-else class="space-y-2">
          <div
            v-for="task in taskItems"
            :key="`${task.kind}-${task.id}`"
            class="board-card-surface rounded-lg border shadow-sm p-3 hover:border-cyan-200 transition-colors"
          >
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0 flex-1">
                <div class="flex flex-wrap items-center gap-2">
                  <span class="text-xs font-bold text-cyan-700">
                    {{ taskKindLabel(task.kind) }} #{{ task.id }}
                  </span>
                  <span class="inline-flex items-center rounded-full border px-2 py-0.5 text-[11px] font-semibold" :class="statusClass(task.status)">
                    {{ formatStatus(task.status) }}
                  </span>
                </div>
                <div v-if="isActiveStatus(task.status)" class="mt-2">
                  <div class="h-2 w-full rounded-full bg-slate-100 overflow-hidden">
                    <div
                      class="h-full rounded-full bg-cyan-600 transition-all"
                      :style="{ width: `${taskProgress(task)}%` }"
                    ></div>
                  </div>
                  <div class="mt-1 text-[11px] text-slate-500">
                    {{ taskProgress(task) }}%
                  </div>
                </div>
                <div v-if="taskSecondaryText(task)" class="text-xs text-slate-600 mt-1 truncate">
                  {{ taskSecondaryText(task) }}
                </div>
                <div class="text-xs text-slate-400 mt-1">{{ formatDate(task.createdAt) }}</div>
              </div>
              <div class="flex flex-wrap justify-end gap-1 shrink-0">
                <button
                  v-if="isActiveStatus(task.status)"
                  type="button"
                  :data-testid="`watch-${task.kind}-task-${task.id}`"
                  @click="emitWatchTask(task)"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium"
                >
                  {{ t('app.watchTask') }}
                </button>
                <button
                  v-if="isActiveStatus(task.status)"
                  type="button"
                  :data-testid="`cancel-${task.kind}-task-${task.id}`"
                  @click="emitCancelTask(task)"
                  class="px-2 py-1 bg-slate-100 hover:bg-red-50 text-slate-700 hover:text-red-700 rounded text-xs font-medium"
                >
                  {{ t('app.cancel') }}
                </button>
                <button
                  v-if="isCompletedStatus(task.status)"
                  type="button"
                  :data-testid="`view-${task.kind}-task-${task.id}`"
                  @click="emitViewTask(task)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ task.kind === 'verification' ? t('app.openResult') : t('app.replay') }}
                </button>
              </div>
            </div>
          </div>
        </div>
      </div>

      <div v-else-if="activeTab === 'verification'" class="space-y-3">
        <div class="flex items-center justify-between px-1">
          <span class="text-xs font-medium text-slate-500">
            {{ t('app.traceCount', { count: verificationTraces.length }) }}
          </span>
          <button
            type="button"
            @click="emit('refresh-verification')"
            class="text-xs text-cyan-700 hover:text-cyan-800 font-medium flex items-center gap-1"
            :disabled="loadingVerification"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingVerification ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingVerification" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined text-4xl animate-spin text-cyan-600">sync</span>
          <p class="text-sm mt-3">{{ t('app.loadingVerificationTraces') }}</p>
        </div>

        <div v-else-if="verificationTraces.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="board-muted-surface w-14 h-14 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">rule</span>
          </div>
          <p class="text-slate-600 text-sm font-medium">{{ t('app.noVerificationTraces') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.noVerificationTracesHint') }}</p>
        </div>

        <div v-else class="space-y-2">
          <div
            v-for="trace in verificationTraces"
            :key="trace.id"
            class="board-card-surface rounded-lg border shadow-sm p-3 hover:border-cyan-200 transition-colors"
          >
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0">
                <div class="flex items-center gap-2">
                  <span class="text-xs font-bold text-cyan-700">{{ t('app.traceNumber', { id: trace.id }) }}</span>
                  <span class="px-2 py-0.5 bg-red-50 text-red-600 rounded-full text-[11px] font-medium">
                    {{ t('app.statesCount', { count: trace.states?.length || 0 }) }}
                  </span>
                </div>
                <div class="text-xs text-slate-600 mt-1 truncate">
                  {{ t('app.specPrefix') }}: {{ trace.violatedSpecId }}
                </div>
                <div class="text-xs text-slate-400 mt-1">{{ formatDate(trace.createdAt) }}</div>
              </div>
              <div class="flex flex-wrap justify-end gap-1 shrink-0">
                <button
                  type="button"
                  :data-testid="`view-verification-trace-${trace.id}`"
                  @click="emit('view-verification', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.view') }}
                </button>
                <button
                  type="button"
                  :data-testid="`fix-verification-trace-${trace.id}`"
                  @click="emit('fix-verification', trace)"
                  :disabled="actionLocked || !trace.violatedSpecId"
                  :title="t('app.historicalFixMayFailIfBoardChanged')"
                  class="px-2 py-1 bg-blue-600 hover:bg-blue-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.fix') }}
                </button>
                <button
                  type="button"
                  :data-testid="`delete-verification-trace-${trace.id}`"
                  @click="emit('delete-verification', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-slate-100 hover:bg-red-50 text-slate-700 hover:text-red-700 rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
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
          <span class="text-xs font-medium text-slate-500">
            {{ t('app.runCount', { count: simulationTraces.length }) }}
          </span>
          <button
            type="button"
            @click="emit('refresh-simulation')"
            class="text-xs text-cyan-700 hover:text-cyan-800 font-medium flex items-center gap-1"
            :disabled="loadingSimulation"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingSimulation ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingSimulation" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined text-4xl animate-spin text-cyan-600">sync</span>
          <p class="text-sm mt-3">{{ t('app.loadingSimulationRuns') }}</p>
        </div>

        <div v-else-if="simulationTraces.length === 0" class="flex flex-col items-center justify-center py-10">
          <div class="board-muted-surface w-14 h-14 rounded-full flex items-center justify-center mb-3">
            <span class="material-symbols-outlined text-slate-300 text-3xl">timeline</span>
          </div>
          <p class="text-slate-600 text-sm font-medium">{{ t('app.noSimulationRuns') }}</p>
          <p class="text-slate-400 text-xs mt-1 text-center px-4">{{ t('app.noSimulationRunsHint') }}</p>
        </div>

        <div v-else class="space-y-2">
          <div
            v-for="trace in simulationTraces"
            :key="trace.id"
            class="board-card-surface rounded-lg border shadow-sm p-3 hover:border-cyan-200 transition-colors"
          >
            <div class="flex items-start justify-between gap-3">
              <div class="min-w-0">
                <div class="flex items-center gap-2">
                  <span class="text-xs font-bold text-cyan-700">{{ t('app.runNumber', { id: trace.id }) }}</span>
                  <span class="px-2 py-0.5 bg-blue-50 text-blue-600 rounded-full text-[11px] font-medium">
                    {{ t('app.stepsCount', { steps: trace.steps, requestedSteps: trace.requestedSteps }) }}
                  </span>
                </div>
                <div class="text-xs text-slate-400 mt-1">{{ formatDate(trace.createdAt) }}</div>
              </div>
              <div class="flex flex-wrap justify-end gap-1 shrink-0">
                <button
                  type="button"
                  :data-testid="`replay-simulation-trace-${trace.id}`"
                  @click="emit('view-simulation', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-cyan-600 hover:bg-cyan-700 text-white rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
                >
                  {{ t('app.replay') }}
                </button>
                <button
                  type="button"
                  :data-testid="`delete-simulation-trace-${trace.id}`"
                  @click="emit('delete-simulation', trace.id)"
                  :disabled="actionLocked"
                  class="px-2 py-1 bg-slate-100 hover:bg-red-50 text-slate-700 hover:text-red-700 rounded text-xs font-medium disabled:opacity-50 disabled:cursor-not-allowed"
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
