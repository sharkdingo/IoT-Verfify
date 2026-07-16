<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, onMounted, ref } from 'vue'
import { useI18n } from 'vue-i18n'
import type {
  ModelGenerationIssue,
  AvailableVerificationRunSummary,
  TraceSummary,
  VerificationRunSummary,
  VerificationTaskSummary
} from '@/types/verify'
import type {
  AvailableSimulationTraceSummary,
  SimulationTaskSummary,
  SimulationTraceSummary
} from '@/types/simulation'
import type {
  AvailableFuzzingRunSummary,
  FuzzingExplorationMode,
  FuzzingFindingSummary,
  FuzzingRunSummary,
  FuzzingTaskSummary
} from '@/types/fuzzing'
import { formatTraceSpec } from '@/utils/traceView'
import { generationIssueReasonKey } from '@/utils/generationIssue'

type HistoryLayer = 'tasks' | 'results'
type ResultFilter = 'all' | 'verification' | 'fuzzing' | 'simulation'
type ResultSource = Exclude<ResultFilter, 'all'>
type TaskKind = 'verification' | 'fuzzing' | 'simulation'
type TaskStatus = 'PENDING' | 'RUNNING' | 'FAILED' | 'CANCELLED'
type CurrentBoardScope = {
  deviceCount: number
  ruleCount: number
  specificationCount: number
  environmentVariableCount: number
  deviceTemplateCount: number
}

type TaskItem =
  | (VerificationTaskSummary & { kind: 'verification' })
  | (FuzzingTaskSummary & { kind: 'fuzzing' })
  | (SimulationTaskSummary & { kind: 'simulation' })

type ResultItem =
  | { kind: 'verification'; run: VerificationRunSummary }
  | { kind: 'fuzzing'; run: FuzzingRunSummary }
  | { kind: 'simulation'; run: SimulationTraceSummary }

const props = defineProps<{
  activeLayer: HistoryLayer
  resultFilter: ResultFilter
  verificationTasks: VerificationTaskSummary[]
  fuzzingTasks: FuzzingTaskSummary[]
  simulationTasks: SimulationTaskSummary[]
  verificationRuns: VerificationRunSummary[]
  fuzzingRuns: FuzzingRunSummary[]
  simulationRuns: SimulationTraceSummary[]
  loadingTasks: boolean
  loadingResults: boolean
  resultErrors?: Partial<Record<ResultSource, string | null>>
  hasMoreFuzzingRuns: boolean
  loadingMoreFuzzingRuns: boolean
  pendingTaskActionKeys?: ReadonlySet<string>
  actionLocked: boolean
  currentBoardScope?: CurrentBoardScope
}>()

const emit = defineEmits<{
  (e: 'update:activeLayer', value: HistoryLayer): void
  (e: 'update:resultFilter', value: ResultFilter): void
  (e: 'close'): void
  (e: 'refresh-tasks'): void
  (e: 'refresh-results'): void
  (e: 'load-more-fuzzing-runs'): void
  (e: 'watch-verification-task', id: number): void
  (e: 'watch-fuzzing-task', id: number): void
  (e: 'watch-simulation-task', id: number): void
  (e: 'cancel-verification-task', id: number): void
  (e: 'cancel-fuzzing-task', id: number): void
  (e: 'cancel-simulation-task', id: number): void
  (e: 'dismiss-verification-task', id: number): void
  (e: 'dismiss-fuzzing-task', id: number): void
  (e: 'dismiss-simulation-task', id: number): void
  (e: 'open-verification-run', id: number): void
  (e: 'delete-verification-run', run: VerificationRunSummary): void
  (e: 'view-verification-trace', id: number): void
  (e: 'fix-verification-trace', trace: TraceSummary): void
  (e: 'view-simulation-run', id: number): void
  (e: 'delete-simulation-run', run: SimulationTraceSummary): void
  (e: 'open-fuzzing-run', id: number): void
  (e: 'delete-fuzzing-run', run: FuzzingRunSummary): void
  (e: 'view-fuzzing-finding', id: number, runId: number): void
  (e: 'verify-fuzzing-finding', finding: FuzzingFindingSummary): void
}>()

const closeButtonRef = ref<HTMLButtonElement | null>(null)
let previousActiveElement: HTMLElement | null = null

onMounted(async () => {
  previousActiveElement = document.activeElement as HTMLElement | null
  await nextTick()
  closeButtonRef.value?.focus()
})

onBeforeUnmount(() => {
  if (previousActiveElement
    && previousActiveElement !== document.body
    && document.contains(previousActiveElement)) {
    previousActiveElement.focus()
  }
  previousActiveElement = null
})

const { t, locale } = useI18n()

const timestamp = (value?: string) => {
  if (!value) return 0
  const parsed = new Date(value).getTime()
  return Number.isNaN(parsed) ? 0 : parsed
}

const formatDate = (value?: string) => {
  if (!value) return ''
  const date = new Date(value)
  return Number.isNaN(date.getTime())
    ? value
    : date.toLocaleString(locale.value.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US')
}

const taskItems = computed<TaskItem[]>(() => [
  ...props.verificationTasks
    .filter(task => task.status !== 'COMPLETED')
    .map(task => ({ ...task, kind: 'verification' as const })),
  ...props.fuzzingTasks
    .filter(task => task.status !== 'COMPLETED')
    .map(task => ({ ...task, kind: 'fuzzing' as const })),
  ...props.simulationTasks
    .filter(task => task.status !== 'COMPLETED')
    .map(task => ({ ...task, kind: 'simulation' as const }))
].sort((a, b) => timestamp(b.createdAt) - timestamp(a.createdAt)))

const activeTasks = computed(() => taskItems.value.filter(task => isActiveStatus(task.status)))
const unresolvedTasks = computed(() => taskItems.value.filter(task => !isActiveStatus(task.status)))

const resultItems = computed<ResultItem[]>(() => {
  const all: ResultItem[] = [
    ...props.verificationRuns.map(run => ({ kind: 'verification' as const, run })),
    ...props.fuzzingRuns.map(run => ({ kind: 'fuzzing' as const, run })),
    ...props.simulationRuns.map(run => ({ kind: 'simulation' as const, run }))
  ]
  return all
    .filter(item => props.resultFilter === 'all' || item.kind === props.resultFilter)
    .sort((a, b) => {
      const left = a.kind === 'simulation' ? a.run.createdAt : (a.run.completedAt || a.run.createdAt)
      const right = b.kind === 'simulation' ? b.run.createdAt : (b.run.completedAt || b.run.createdAt)
      return timestamp(right) - timestamp(left)
    })
})

const tracesForRun = (run: VerificationRunSummary) => run.counterexamples || []
const isActiveStatus = (status?: string) => status === 'PENDING' || status === 'RUNNING'

const taskProgress = (task: TaskItem) => {
  const fallback = isActiveStatus(task.status) ? 0 : 100
  const numeric = typeof task.progress === 'number' ? task.progress : fallback
  return Number.isFinite(numeric) ? Math.min(100, Math.max(0, Math.round(numeric))) : fallback
}

const formatStatus = (status?: string) => {
  switch (status as TaskStatus | undefined) {
    case 'PENDING': return t('app.taskStatusPending')
    case 'RUNNING': return t('app.taskStatusRunning')
    case 'FAILED': return t('app.taskStatusFailed')
    case 'CANCELLED': return t('app.taskStatusCancelled')
    default: return status || t('app.taskInitializing')
  }
}

const statusClass = (status?: string) => {
  if (status === 'FAILED') return 'border-red-200 bg-red-50 text-red-700'
  if (status === 'CANCELLED') return 'border-slate-200 bg-slate-100 text-slate-600'
  return 'border-blue-200 bg-blue-50 text-blue-700'
}

const taskKindLabel = (kind: TaskKind) => {
  if (kind === 'verification') return t('app.verification')
  if (kind === 'fuzzing') return t('app.fuzzSearch')
  return t('app.simulation')
}

const emitWatchTask = (task: TaskItem) => {
  if (task.kind === 'verification') emit('watch-verification-task', task.id)
  else if (task.kind === 'fuzzing') emit('watch-fuzzing-task', task.id)
  else emit('watch-simulation-task', task.id)
}

const emitCancelTask = (task: TaskItem) => {
  if (task.kind === 'verification') emit('cancel-verification-task', task.id)
  else if (task.kind === 'fuzzing') emit('cancel-fuzzing-task', task.id)
  else emit('cancel-simulation-task', task.id)
}

const emitDismissTask = (task: TaskItem) => {
  if (task.kind === 'verification') emit('dismiss-verification-task', task.id)
  else if (task.kind === 'fuzzing') emit('dismiss-fuzzing-task', task.id)
  else emit('dismiss-simulation-task', task.id)
}

const taskActionPending = (action: 'cancel' | 'dismiss', task: TaskItem) =>
  props.pendingTaskActionKeys?.has(`${action}:${task.kind}:${task.id}`) === true

const traceSpecTitle = (trace: TraceSummary) => {
  if (!trace.dataAvailable) return t('app.historyItemUnavailable')
  const summary = trace.violatedSpec ? formatTraceSpec(trace.violatedSpec, t) : ''
  return summary || t('app.unknownSpecification')
}

const fuzzFindingTitle = (finding: FuzzingFindingSummary) => {
  if (finding.dataAvailable === false) return t('app.historyItemUnavailable')
  const summary = finding.violatedSpec ? formatTraceSpec(finding.violatedSpec, t) : ''
  return summary || finding.specificationLabel || finding.violatedSpecId || t('app.unknownSpecification')
}

const displayStep = (zeroBasedStep: number) => zeroBasedStep + 1

const fuzzingModeLabel = (mode: FuzzingExplorationMode) => t(
  mode === 'PAPER_COMPATIBLE' ? 'app.fuzzModePaper' : 'app.fuzzModeBoard'
)

const fuzzingModeDescription = (mode: FuzzingExplorationMode) => t(
  mode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzModePaperDescription'
    : 'app.fuzzModeBoardDescription'
)

const fuzzRunHasBoardDrift = (run: AvailableFuzzingRunSummary) => {
  const current = props.currentBoardScope
  if (!current) return false
  return run.modelSnapshot.deviceCount !== current.deviceCount
    || run.modelSnapshot.ruleCount !== current.ruleCount
    || run.modelSnapshot.specificationCount !== current.specificationCount
    || run.modelSnapshot.environmentVariableCount !== current.environmentVariableCount
    || run.modelSnapshot.deviceTemplateCount !== current.deviceTemplateCount
}

const resultErrorEntries = computed(() => {
  const errors = props.resultErrors || {}
  const visibleSources: readonly ResultSource[] = props.resultFilter === 'all'
    ? ['verification', 'fuzzing', 'simulation']
    : [props.resultFilter]
  return visibleSources
    .filter(source => Boolean(errors[source]))
    .map(source => ({ source, message: errors[source] as string }))
})

const resultSourceLabel = (source: ResultSource) => {
  if (source === 'verification') return t('app.verificationRunResult')
  if (source === 'fuzzing') return t('app.fuzzRunResult')
  return t('app.simulationRunResult')
}

const emitDeleteResult = (item: ResultItem) => {
  if (item.kind === 'verification') emit('delete-verification-run', item.run)
  else if (item.kind === 'fuzzing') emit('delete-fuzzing-run', item.run)
  else emit('delete-simulation-run', item.run)
}

const generationIssuesFor = (item: { generationIssues?: ModelGenerationIssue[] }) =>
  Array.isArray(item.generationIssues) ? item.generationIssues : []

const verificationOutcomeBadge = (run: AvailableVerificationRunSummary) => {
  if (run.outcome === 'VIOLATED') {
    return {
      label: t('app.verificationFailedWithViolations', { count: run.violatedSpecCount }),
      className: 'border-red-200 bg-red-50 text-red-700'
    }
  }
  if (run.outcome === 'SATISFIED' && run.modelComplete) {
    return {
      label: t('app.verificationPassed'),
      className: 'border-green-200 bg-green-50 text-green-700'
    }
  }
  if (run.outcome === 'SATISFIED') {
    return {
      label: t('app.verificationPassedWithGenerationWarnings'),
      className: 'border-amber-200 bg-amber-50 text-amber-800'
    }
  }
  return {
    label: t('app.verificationInconclusiveSummary'),
    className: 'border-amber-200 bg-amber-50 text-amber-800'
  }
}

const simulationOutcomeBadge = (run: AvailableSimulationTraceSummary) => run.modelComplete
  ? {
      label: t('app.allRulesModeled'),
      className: 'border-blue-200 bg-blue-50 text-blue-700'
    }
  : {
      label: t('app.incompleteModel'),
      className: 'border-amber-200 bg-amber-50 text-amber-800'
    }

const fuzzingOutcomeBadge = (run: AvailableFuzzingRunSummary) => {
  if (run.outcome === 'FOUND_VIOLATION') {
    return {
      label: t('app.fuzzViolationFound'),
      className: 'border-red-200 bg-red-50 text-red-700'
    }
  }
  if (run.outcome === 'BUDGET_EXHAUSTED') {
    return {
      label: t('app.fuzzBudgetExhausted'),
      className: 'border-sky-200 bg-sky-50 text-sky-800'
    }
  }
  return {
    label: t('app.fuzzInconclusive'),
    className: 'border-amber-200 bg-amber-50 text-amber-800'
  }
}
</script>

<template>
  <div
    class="board-floating-panel history-panel board-surface-panel fixed top-20 z-30 flex w-[480px] max-w-[calc(100vw-2rem)] flex-col overflow-hidden rounded-xl border shadow-2xl"
    data-testid="trace-history-panel"
    role="dialog"
    aria-labelledby="trace-history-title"
    tabindex="-1"
    @keydown.esc.stop.prevent="emit('close')"
  >
    <div class="flex shrink-0 items-center justify-between bg-slate-800 p-4">
      <div class="flex min-w-0 items-center gap-3">
        <div class="flex h-10 w-10 shrink-0 items-center justify-center rounded-lg bg-cyan-600 shadow-lg">
          <span class="material-symbols-outlined text-xl text-white">history</span>
        </div>
        <div class="min-w-0">
          <h3 id="trace-history-title" class="text-base font-bold text-white">{{ t('app.runHistory') }}</h3>
          <p class="truncate text-xs text-white/75">{{ t('app.runHistorySubtitle') }}</p>
        </div>
      </div>
      <button
        ref="closeButtonRef"
        type="button"
        data-testid="close-history-panel"
        class="flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-white/75 transition-colors hover:bg-white/10 hover:text-white"
        :title="t('app.close')"
        :aria-label="t('app.close')"
        @click="emit('close')"
      >
        <span class="material-symbols-outlined">close</span>
      </button>
    </div>

    <div class="board-panel-tabs shrink-0 border-b p-3">
      <div class="board-segmented grid grid-cols-2 gap-1 rounded-lg p-1">
        <button
          type="button"
          data-testid="history-layer-tasks"
          class="flex min-h-11 items-center justify-center gap-1 rounded-md px-3 py-2 text-xs font-bold transition-colors"
          :class="activeLayer === 'tasks' ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-600 hover:text-slate-800'"
          :aria-pressed="activeLayer === 'tasks'"
          @click="emit('update:activeLayer', 'tasks')"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">pending_actions</span>
          {{ t('app.taskStatusLayer') }}
          <span v-if="activeTasks.length" class="rounded-full bg-cyan-100 px-1.5 text-[10px] text-cyan-800">
            {{ activeTasks.length }}
          </span>
        </button>
        <button
          type="button"
          data-testid="history-layer-results"
          class="flex min-h-11 items-center justify-center gap-1 rounded-md px-3 py-2 text-xs font-bold transition-colors"
          :class="activeLayer === 'results' ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-600 hover:text-slate-800'"
          :aria-pressed="activeLayer === 'results'"
          @click="emit('update:activeLayer', 'results')"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">fact_check</span>
          {{ t('app.historyResultsLayer') }}
        </button>
      </div>
    </div>

    <div class="board-panel-body min-h-0 flex-1 overflow-y-auto p-3">
      <div
        v-if="actionLocked"
        class="mb-3 flex items-start gap-2 rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs text-amber-800"
      >
        <span class="material-symbols-outlined text-sm">lock</span>
        <span>{{ t('app.historyActionsLockedHint') }}</span>
      </div>

      <div v-if="activeLayer === 'tasks'" class="space-y-3">
        <div class="flex items-center justify-between px-1">
          <span class="text-xs font-medium text-slate-500">
            {{ t('app.pendingTaskSummary', { active: activeTasks.length, unresolved: unresolvedTasks.length }) }}
          </span>
          <button
            type="button"
            class="flex min-h-11 items-center gap-1 px-2 text-xs font-medium text-cyan-700 hover:text-cyan-800"
            :disabled="loadingTasks"
            @click="emit('refresh-tasks')"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingTasks ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingTasks" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined animate-spin text-4xl text-cyan-600">sync</span>
          <p class="mt-3 text-sm">{{ t('app.loadingTasks') }}</p>
        </div>

        <div v-else-if="taskItems.length === 0" class="flex flex-col items-center justify-center py-10 text-center">
          <div class="board-muted-surface mb-3 flex h-14 w-14 items-center justify-center rounded-full">
            <span class="material-symbols-outlined text-3xl text-slate-300">task_alt</span>
          </div>
          <p class="text-sm font-medium text-slate-600">{{ t('app.noPendingTasks') }}</p>
          <p class="mt-1 px-4 text-xs text-slate-400">{{ t('app.noPendingTasksHint') }}</p>
        </div>

        <template v-else>
          <section v-if="activeTasks.length" class="space-y-2">
            <h4 class="px-1 text-xs font-bold text-slate-600">{{ t('app.runningTasks') }}</h4>
            <div
              v-for="task in activeTasks"
              :key="`${task.kind}-${task.id}`"
              class="board-card-surface rounded-lg border p-3 shadow-sm"
            >
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex flex-wrap items-center gap-2">
                    <span class="text-xs font-bold text-cyan-700">{{ taskKindLabel(task.kind) }}</span>
                    <span class="rounded-full border px-2 py-0.5 text-[11px] font-semibold" :class="statusClass(task.status)">
                      {{ formatStatus(task.status) }}
                    </span>
                    <span
                      v-if="task.kind === 'fuzzing'"
                      :data-testid="`fuzzing-task-mode-${task.id}`"
                      class="max-w-full rounded-full border border-indigo-100 bg-indigo-50 px-2 py-0.5 text-[10px] font-semibold text-indigo-800"
                      :title="fuzzingModeDescription(task.explorationMode)"
                    >
                      {{ fuzzingModeLabel(task.explorationMode) }}
                    </span>
                  </div>
                  <div
                    class="mt-2 h-2 w-full overflow-hidden rounded-full bg-slate-100"
                    role="progressbar"
                    :aria-label="`${taskKindLabel(task.kind)} ${t('app.progress')}`"
                    aria-valuemin="0"
                    aria-valuemax="100"
                    :aria-valuenow="taskProgress(task)"
                  >
                    <div class="h-full rounded-full bg-cyan-600 transition-all" :style="{ width: `${taskProgress(task)}%` }"></div>
                  </div>
                  <div class="mt-1 flex justify-between text-[11px] text-slate-500">
                    <span>{{ taskProgress(task) }}%</span>
                    <span>{{ formatDate(task.createdAt) }}</span>
                  </div>
                </div>
                <div class="flex shrink-0 flex-col gap-1">
                  <button
                    type="button"
                    class="min-h-11 rounded bg-cyan-600 px-2 py-1 text-xs font-medium text-white hover:bg-cyan-700"
                    @click="emitWatchTask(task)"
                  >
                    {{ t('app.watchTask') }}
                  </button>
                  <button
                    type="button"
                    class="inline-flex min-h-11 items-center justify-center gap-1 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-red-50 hover:text-red-700 disabled:cursor-wait disabled:opacity-60"
                    :disabled="taskActionPending('cancel', task)"
                    :aria-busy="taskActionPending('cancel', task)"
                    @click="emitCancelTask(task)"
                  >
                    <span
                      v-if="taskActionPending('cancel', task)"
                      class="material-symbols-outlined animate-spin text-sm"
                      aria-hidden="true"
                    >sync</span>
                    {{ t('app.cancel') }}
                  </button>
                </div>
              </div>
            </div>
          </section>

          <section v-if="unresolvedTasks.length" class="space-y-2">
            <h4 class="px-1 text-xs font-bold text-slate-600">{{ t('app.tasksWithoutResults') }}</h4>
            <div
              v-for="task in unresolvedTasks"
              :key="`${task.kind}-${task.id}`"
              class="board-card-surface rounded-lg border p-3 shadow-sm"
            >
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex flex-wrap items-center gap-2">
                    <span class="text-xs font-bold text-cyan-700">{{ taskKindLabel(task.kind) }}</span>
                    <span class="rounded-full border px-2 py-0.5 text-[11px] font-semibold" :class="statusClass(task.status)">
                      {{ formatStatus(task.status) }}
                    </span>
                    <span
                      v-if="task.kind === 'fuzzing'"
                      :data-testid="`fuzzing-task-mode-${task.id}`"
                      class="max-w-full rounded-full border border-indigo-100 bg-indigo-50 px-2 py-0.5 text-[10px] font-semibold text-indigo-800"
                      :title="fuzzingModeDescription(task.explorationMode)"
                    >
                      {{ fuzzingModeLabel(task.explorationMode) }}
                    </span>
                  </div>
                  <p class="mt-2 text-xs leading-5 text-slate-600">
                    {{ task.status === 'CANCELLED' ? t('app.cancelledTaskNoResult') : t('app.failedTaskNoResult') }}
                  </p>
                  <details v-if="task.errorMessage" class="mt-2 text-[11px] text-slate-500">
                    <summary class="flex min-h-11 cursor-pointer items-center font-semibold">{{ t('app.technicalDetails') }}</summary>
                    <code class="mt-1 block whitespace-pre-wrap break-words rounded bg-slate-950 px-2 py-1.5 text-slate-100">{{ task.errorMessage }}</code>
                  </details>
                  <div class="mt-1 text-[11px] text-slate-400">{{ formatDate(task.completedAt || task.createdAt) }}</div>
                </div>
                <button
                  type="button"
                  class="inline-flex min-h-11 shrink-0 items-center justify-center gap-1 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-slate-200 disabled:cursor-wait disabled:opacity-60"
                  :disabled="taskActionPending('dismiss', task)"
                  :aria-busy="taskActionPending('dismiss', task)"
                  @click="emitDismissTask(task)"
                >
                  <span
                    v-if="taskActionPending('dismiss', task)"
                    class="material-symbols-outlined animate-spin text-sm"
                    aria-hidden="true"
                  >sync</span>
                  {{ t('app.dismissTask') }}
                </button>
              </div>
            </div>
          </section>
        </template>
      </div>

      <div v-else class="space-y-3">
        <div class="flex items-center justify-between gap-3 px-1">
          <div class="board-segmented grid min-w-0 flex-1 grid-cols-4 gap-1 rounded-lg p-1">
            <button
              v-for="filter in (['all', 'verification', 'fuzzing', 'simulation'] as const)"
              :key="filter"
              type="button"
              :data-testid="`history-result-filter-${filter}`"
              class="min-h-11 rounded-md px-2 py-1.5 text-[11px] font-bold transition-colors"
              :class="resultFilter === filter ? 'bg-white text-cyan-700 shadow-sm' : 'text-slate-500 hover:text-slate-700'"
              :aria-pressed="resultFilter === filter"
              @click="emit('update:resultFilter', filter)"
            >
              {{ filter === 'all'
                ? t('app.allResults')
                : filter === 'verification'
                  ? t('app.verification')
                  : filter === 'fuzzing' ? t('app.fuzzSearch') : t('app.simulation') }}
            </button>
          </div>
          <button
            type="button"
            class="flex min-h-11 shrink-0 items-center gap-1 px-2 text-xs font-medium text-cyan-700 hover:text-cyan-800"
            :disabled="loadingResults"
            @click="emit('refresh-results')"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingResults ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingResults" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined animate-spin text-4xl text-cyan-600">sync</span>
          <p class="mt-3 text-sm">{{ t('app.loadingRunResults') }}</p>
        </div>

        <div
          v-if="!loadingResults && resultErrorEntries.length > 0"
          data-testid="history-results-load-error"
          class="rounded-lg border border-amber-300 bg-amber-50 px-3 py-2.5 text-xs leading-5 text-amber-950"
          role="alert"
        >
          <div class="flex items-start gap-2">
            <span class="material-symbols-outlined mt-0.5 text-base text-amber-700" aria-hidden="true">warning</span>
            <div class="min-w-0 flex-1">
              <p class="font-bold">{{ t('app.historyResultsPartialFailure') }}</p>
              <ul class="mt-1 list-disc space-y-0.5 pl-4">
                <li v-for="entry in resultErrorEntries" :key="entry.source">
                  {{ resultSourceLabel(entry.source) }}: {{ entry.message }}
                </li>
              </ul>
              <button
                type="button"
                class="mt-2 inline-flex min-h-11 items-center gap-1 rounded-md border border-amber-300 bg-white px-2 py-1 text-[11px] font-semibold text-amber-900 hover:bg-amber-100 disabled:opacity-50"
                :disabled="loadingResults"
                @click="emit('refresh-results')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">refresh</span>
                {{ t('app.retry') }}
              </button>
            </div>
          </div>
        </div>

        <div v-if="!loadingResults && resultErrorEntries.length === 0 && resultItems.length === 0" class="flex flex-col items-center justify-center py-10 text-center">
          <div class="board-muted-surface mb-3 flex h-14 w-14 items-center justify-center rounded-full">
            <span class="material-symbols-outlined text-3xl text-slate-300">fact_check</span>
          </div>
          <p class="text-sm font-medium text-slate-600">{{ t('app.noRunResults') }}</p>
          <p class="mt-1 px-4 text-xs text-slate-400">{{ t('app.noRunResultsHint') }}</p>
        </div>

        <div v-if="!loadingResults && resultItems.length > 0" class="space-y-3">
          <article
            v-for="item in resultItems"
            :key="`${item.kind}-${item.run.id}`"
            class="board-card-surface rounded-lg border p-3 shadow-sm transition-colors hover:border-cyan-200"
          >
            <template v-if="item.run.dataAvailable === false">
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex items-center gap-2 text-amber-800">
                    <span class="material-symbols-outlined text-base" aria-hidden="true">warning</span>
                    <span class="text-xs font-bold">{{ t('app.historyItemUnavailable') }}</span>
                  </div>
                  <p class="mt-1 text-[11px] leading-4 text-slate-600">
                    {{ t('app.historyItemUnavailableDetail') }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-400">
                    {{ formatDate(item.kind === 'simulation' ? item.run.createdAt : (item.run.completedAt || item.run.createdAt)) }}
                  </p>
                </div>
                <button
                  type="button"
                  class="min-h-11 shrink-0 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-red-50 hover:text-red-700 disabled:opacity-50"
                  :disabled="actionLocked"
                  @click="emitDeleteResult(item)"
                >
                  {{ t('app.delete') }}
                </button>
              </div>
            </template>

            <template v-else-if="item.kind === 'verification'">
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex flex-wrap items-center gap-2">
                    <span class="text-xs font-bold text-cyan-700">{{ t('app.verificationRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full border px-2 py-0.5 text-[11px] font-semibold"
                      :class="verificationOutcomeBadge(item.run).className"
                      :title="verificationOutcomeBadge(item.run).label"
                    >
                      <span class="truncate">{{ verificationOutcomeBadge(item.run).label }}</span>
                    </span>
                  </div>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.runScopeCounts', {
                      devices: item.run.modelSnapshot.deviceCount,
                      rules: item.run.modelSnapshot.ruleCount,
                      specs: item.run.modelSnapshot.specificationCount
                    }) }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-400">{{ formatDate(item.run.completedAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`open-verification-run-${item.run.id}`"
                    class="min-h-11 rounded bg-cyan-600 px-2 py-1 text-xs font-medium text-white hover:bg-cyan-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('open-verification-run', item.run.id)"
                  >
                    {{ t('app.openResult') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-verification-run-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-red-50 hover:text-red-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('delete-verification-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>

              <ul v-if="generationIssuesFor(item.run).length" class="mt-2 space-y-1.5">
                <li
                  v-for="(issue, index) in generationIssuesFor(item.run)"
                  :key="`${issue.itemLabel}-${index}`"
                  class="border-l-2 border-amber-300 pl-2 text-[11px] leading-4 text-amber-800"
                >
                  <span class="font-semibold">{{ issue.itemLabel || t('app.unknownModelItem') }}</span>
                  <span>: {{ t(generationIssueReasonKey(issue)) }}</span>
                </li>
              </ul>

              <div v-if="item.run.outcome === 'VIOLATED'" class="mt-3 rounded-lg border border-red-100 bg-red-50/60 p-2.5">
                <div class="flex flex-wrap items-center justify-between gap-2">
                  <span class="text-xs font-semibold text-red-800">
                    {{ t('app.violationEvidenceSummary', {
                      violations: item.run.violatedSpecCount,
                      counterexamples: item.run.counterexampleCount
                    }) }}
                  </span>
                </div>
                <p
                  v-if="item.run.counterexampleCount < item.run.violatedSpecCount"
                  class="mt-1 text-[11px] leading-4 text-amber-800"
                >
                  {{ t('app.someViolationsHaveNoReplayableCounterexample') }}
                </p>
                <div v-if="tracesForRun(item.run).length" class="mt-2 space-y-1.5">
                  <div
                    v-for="trace in tracesForRun(item.run)"
                    :key="trace.id"
                    class="flex items-center justify-between gap-2 rounded-md border border-red-100 bg-white px-2 py-1.5"
                  >
                    <div class="min-w-0">
                      <p class="truncate text-[11px] font-medium text-slate-700" :title="traceSpecTitle(trace)">
                        {{ traceSpecTitle(trace) }}
                      </p>
                      <p v-if="trace.dataAvailable" class="text-[10px] text-slate-400">
                        {{ t('app.statesCount', { count: trace.stateCount || 0 }) }}
                      </p>
                      <p v-else class="text-[10px] font-medium text-amber-700">
                        {{ t('app.historyTraceUnavailableDetail') }}
                      </p>
                    </div>
                    <div class="flex shrink-0 gap-1">
                      <button
                        type="button"
                        :data-testid="`view-verification-trace-${trace.id}`"
                        class="min-h-11 rounded bg-cyan-600 px-2 py-1 text-[11px] font-medium text-white hover:bg-cyan-700 disabled:opacity-50"
                        :disabled="actionLocked || !trace.dataAvailable"
                        @click="emit('view-verification-trace', trace.id)"
                      >
                        {{ t('app.replay') }}
                      </button>
                      <button
                        type="button"
                        :data-testid="`fix-verification-trace-${trace.id}`"
                        class="min-h-11 rounded bg-amber-100 px-2 py-1 text-[11px] font-medium text-amber-800 hover:bg-amber-200 disabled:opacity-50"
                        :disabled="actionLocked || !trace.dataAvailable"
                        @click="emit('fix-verification-trace', trace)"
                      >
                        {{ t('app.fix') }}
                      </button>
                    </div>
                  </div>
                </div>
              </div>
            </template>

            <template v-else-if="item.kind === 'fuzzing'">
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex flex-wrap items-center gap-2">
                    <span class="text-xs font-bold text-indigo-700">{{ t('app.fuzzRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full border px-2 py-0.5 text-[11px] font-semibold"
                      :class="fuzzingOutcomeBadge(item.run).className"
                    >
                      <span class="truncate">{{ fuzzingOutcomeBadge(item.run).label }}</span>
                    </span>
                    <span
                      :data-testid="`fuzzing-history-mode-${item.run.id}`"
                      class="max-w-full rounded-full border border-indigo-100 bg-indigo-50 px-2 py-0.5 text-[10px] font-semibold text-indigo-800"
                      :title="fuzzingModeDescription(item.run.explorationMode)"
                    >
                      {{ fuzzingModeLabel(item.run.explorationMode) }}
                    </span>
                  </div>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.fuzzRunCounts', {
                      iterations: item.run.iterations,
                      paths: item.run.generatedPaths,
                      elapsed: Math.round(item.run.elapsedMs / 1000)
                    }) }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.runScopeCounts', {
                      devices: item.run.modelSnapshot.deviceCount,
                      rules: item.run.modelSnapshot.ruleCount,
                      specs: item.run.modelSnapshot.specificationCount
                    }) }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-400">{{ formatDate(item.run.completedAt || item.run.createdAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`open-fuzzing-run-${item.run.id}`"
                    class="min-h-11 rounded bg-indigo-600 px-2 py-1 text-xs font-medium text-white hover:bg-indigo-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('open-fuzzing-run', item.run.id)"
                  >
                    {{ t('app.openResult') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-fuzzing-run-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-red-50 hover:text-red-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('delete-fuzzing-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>

              <p
                v-if="fuzzRunHasBoardDrift(item.run)"
                class="mt-2 rounded-md border border-amber-200 bg-amber-50 px-2 py-1.5 text-[11px] font-semibold leading-4 text-amber-900"
                data-testid="fuzzing-history-board-drift"
              >
                {{ t('app.fuzzBoardScopeChanged') }}
              </p>

              <p
                v-if="item.run.outcome === 'BUDGET_EXHAUSTED'"
                class="mt-2 rounded-md border border-sky-200 bg-sky-50 px-2 py-1.5 text-[11px] leading-4 text-sky-900"
              >
                {{ t('app.fuzzNoViolationWithinBudget') }}
              </p>

              <div
                v-if="item.run.outcome === 'FOUND_VIOLATION' && item.run.findings?.length"
                class="mt-3 rounded-lg border border-red-100 bg-red-50/60 p-2.5"
              >
                <div class="text-xs font-semibold text-red-800">
                  {{ t('app.fuzzFindingsCount', { count: item.run.findings.length }) }}
                </div>
                <div class="mt-2 space-y-1.5">
                  <div
                    v-for="finding in item.run.findings"
                    :key="finding.id"
                    class="flex items-center justify-between gap-2 rounded-md border border-red-100 bg-white px-2 py-1.5"
                  >
                    <div class="min-w-0">
                      <p class="truncate text-[11px] font-medium text-slate-700" :title="fuzzFindingTitle(finding)">
                        {{ fuzzFindingTitle(finding) }}
                      </p>
                      <p class="text-[10px] text-slate-400">
                        {{ t('app.fuzzFirstViolationStep', { step: displayStep(finding.firstViolationStep) }) }}
                      </p>
                    </div>
                    <div class="flex shrink-0 gap-1">
                      <button
                        type="button"
                        :data-testid="`view-fuzzing-finding-${finding.id}`"
                        class="min-h-11 rounded bg-indigo-600 px-2 py-1 text-[11px] font-medium text-white hover:bg-indigo-700 disabled:opacity-50"
                        :disabled="actionLocked || finding.dataAvailable === false"
                        @click="emit('view-fuzzing-finding', finding.id, item.run.id)"
                      >
                        {{ t('app.replay') }}
                      </button>
                      <button
                        type="button"
                        :data-testid="`verify-fuzzing-finding-${finding.id}`"
                        class="min-h-11 rounded bg-emerald-100 px-2 py-1 text-[11px] font-medium text-emerald-800 hover:bg-emerald-200 disabled:opacity-50"
                        :disabled="actionLocked || finding.dataAvailable === false"
                        @click="emit('verify-fuzzing-finding', finding)"
                      >
                        {{ t('app.verifyFormally') }}
                      </button>
                    </div>
                  </div>
                </div>
              </div>
            </template>

            <template v-else>
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex flex-wrap items-center gap-2">
                    <span class="text-xs font-bold text-cyan-700">{{ t('app.simulationRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full border px-2 py-0.5 text-[11px] font-semibold"
                      :class="simulationOutcomeBadge(item.run).className"
                    >
                      <span class="truncate">{{ simulationOutcomeBadge(item.run).label }}</span>
                    </span>
                  </div>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.simulationHistoryCounts', {
                      requested: item.run.requestedSteps,
                      steps: item.run.steps,
                      states: item.run.steps + 1
                    }) }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-400">{{ formatDate(item.run.createdAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`replay-simulation-trace-${item.run.id}`"
                    class="min-h-11 rounded bg-cyan-600 px-2 py-1 text-xs font-medium text-white hover:bg-cyan-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('view-simulation-run', item.run.id)"
                  >
                    {{ t('app.replay') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-simulation-trace-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-red-50 hover:text-red-700 disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('delete-simulation-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>
              <ul v-if="generationIssuesFor(item.run).length" class="mt-2 space-y-1.5">
                <li
                  v-for="(issue, index) in generationIssuesFor(item.run)"
                  :key="`${issue.itemLabel}-${index}`"
                  class="border-l-2 border-amber-300 pl-2 text-[11px] leading-4 text-amber-800"
                >
                  <span class="font-semibold">{{ issue.itemLabel || t('app.unknownModelItem') }}</span>
                  <span>: {{ t(generationIssueReasonKey(issue)) }}</span>
                </li>
              </ul>
            </template>
          </article>

          <button
            v-if="resultFilter === 'fuzzing' && hasMoreFuzzingRuns"
            type="button"
            data-testid="load-more-fuzzing-runs"
            class="flex min-h-11 w-full items-center justify-center gap-1 rounded-md border border-slate-200 bg-white px-3 py-2 text-xs font-semibold text-cyan-700 hover:border-cyan-200 hover:bg-cyan-50 disabled:cursor-not-allowed disabled:opacity-50"
            :disabled="actionLocked || loadingMoreFuzzingRuns"
            @click="emit('load-more-fuzzing-runs')"
          >
            <span
              v-if="loadingMoreFuzzingRuns"
              class="material-symbols-outlined animate-spin text-sm"
              aria-hidden="true"
            >sync</span>
            {{ loadingMoreFuzzingRuns ? t('app.loadingMoreFuzzingResults') : t('app.loadMoreFuzzingResults') }}
          </button>
        </div>
      </div>
    </div>
  </div>
</template>
