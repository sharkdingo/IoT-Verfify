<script setup lang="ts">
import { formatRunTimestamp } from '@/utils/runTimestamp'
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
import RunInitiatorBadge from '@/components/RunInitiatorBadge.vue'
import HintTooltip from '@/components/common/HintTooltip.vue'

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
  modelFingerprint?: string | null
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
  pendingResultDeleteKeys?: ReadonlySet<string>
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
  /**
   * Open the panel that owns launching this kind of run, so a failed job is not a dead end.
   *
   * Deliberately not a one-click "retry": the board may have changed since the run, so the settings
   * must be re-validated against the current scene rather than silently re-submitted. The owning
   * panel already holds the previous configuration for the session and re-checks eligibility.
   */
  (e: 'reopen-task-settings', kind: TaskKind): void
  (e: 'open-verification-run', id: number): void
  (e: 'delete-verification-run', run: VerificationRunSummary): void
  (e: 'download-verification-run-smv', id: number): void
  (e: 'view-verification-trace', id: number): void
  (e: 'fix-verification-trace', trace: TraceSummary): void
  (e: 'view-simulation-run', id: number): void
  (e: 'delete-simulation-run', run: SimulationTraceSummary): void
  (e: 'download-simulation-trace-smv', id: number): void
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

/* One owner in `utils/runTimestamp.ts`. This copy returned a blank for a missing timestamp, which cannot be told
   apart from a rendering failure — the shared version says "unknown" instead. */
const formatDate = (value?: string) => formatRunTimestamp(value, locale.value, t)

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
const isResultDeletePending = (kind: ResultSource, id: number) =>
  props.pendingResultDeleteKeys?.has(`${kind}:${id}`) === true
const resultDeleteTestId = (kind: ResultSource, id: number) => {
  if (kind === 'simulation') return `delete-simulation-trace-${id}`
  return `delete-${kind === 'fuzzing' ? 'fuzzing' : 'verification'}-run-${id}`
}

/**
 * How much of an in-flight task's work is done. Only ever rendered for PENDING/RUNNING tasks, so a
 * missing value means "not reported yet" and 0 is the honest fallback — never 100, which would claim
 * completed work for a task that has not finished.
 */
const taskProgress = (task: TaskItem) => {
  const numeric = typeof task.progress === 'number' ? task.progress : 0
  return Number.isFinite(numeric) ? Math.min(100, Math.max(0, Math.round(numeric))) : 0
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
  if (status === 'FAILED') return 'board-surface-danger board-text-danger'
  if (status === 'CANCELLED') return 'border-slate-200 bg-slate-100 text-slate-600'
  return 'board-border-subtle board-chip-info board-text-info'
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

/**
 * Drift, where an un-comparable fingerprint counts as drift rather than as a match.
 *
 * The bare `!==` carries that: a persisted fuzz run always has a 64-hex fingerprint (`FuzzMapper`
 * rejects a snapshot without one), so an absent or nulled current fingerprint compares unequal and the
 * row warns. `Board.vue`'s copy relies on the same property, and
 * `TraceHistoryPanel.spec.ts`'s "does not claim a fingerprinted run is unchanged when the current
 * fingerprint is unavailable" pins it — that case reaches here with a scope object that carries counts
 * but no fingerprint.
 *
 * Do not add a three-valued `UNAVAILABLE` branch here on the theory that unknown deserves its own
 * notice: the only unknown states reachable are already reported as drift, which is the conservative
 * answer, and splitting them turned that guarded behaviour into silence.
 */
const fuzzRunHasBoardDrift = (run: AvailableFuzzingRunSummary) => {
  const current = props.currentBoardScope
  if (!current) return false
  return run.modelSnapshot.modelFingerprint !== current.modelFingerprint
}

/**
 * How a verification or simulation history row compares to the current canvas — three-valued, because
 * this comparison cannot answer "unchanged".
 *
 * It compares five integers. Every semantic edit that keeps them equal is invisible to it: inverting a
 * rule's relation operator, changing an environment variable's value, moving a specification's
 * threshold, swapping one device's template for another. (A device *rename* is deliberately not drift
 * anywhere in this product — `FuzzModelFingerprint.PRESENTATION_FIELDS` strips `deviceLabel`, and
 * `FuzzServiceImplTest` asserts a rename leaves the fingerprint equal.)
 *
 * It used to return a boolean, and the template read `false` as "no warning" — which a reader takes as
 * an affirmative "this verdict still describes my canvas". That is the one thing the product is careful
 * never to claim: `runBoardNotCompared` says the result applies only to its snapshot, the open result
 * withdraws its Fix action when the board changes, and the comment on `fuzzRunHasBoardDrift` above
 * states the rule that an un-comparable state must read as drift rather than as a match. This predicate
 * was the one place violating it.
 *
 * Why not a real fingerprint, like fuzz has: `modelFingerprint` is fuzz-only *by contract*, not by
 * omission. `PersistedModelContextIntegrity` (backend, ~line 500) rejects a verification or simulation
 * snapshot whose `modelFingerprint` is non-null, so populating it would make every existing row
 * unreadable. Closing the gap properly is a persisted-format decision, not a frontend one.
 */
type RunScopeComparison = 'COUNTS_CHANGED' | 'COUNTS_ONLY_MATCH' | 'NOT_COMPARED'

const runScopeComparison = (
  run: AvailableVerificationRunSummary | AvailableSimulationTraceSummary,
  includeSpecifications: boolean
): RunScopeComparison => {
  const current = props.currentBoardScope
  if (!current) return 'NOT_COMPARED'
  const snapshot = run.modelSnapshot
  const countsDiffer = snapshot.deviceCount !== current.deviceCount
    || snapshot.ruleCount !== current.ruleCount
    || snapshot.environmentVariableCount !== current.environmentVariableCount
    || snapshot.deviceTemplateCount !== current.deviceTemplateCount
    || (includeSpecifications && snapshot.specificationCount !== current.specificationCount)
  return countsDiffer ? 'COUNTS_CHANGED' : 'COUNTS_ONLY_MATCH'
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

/**
 * The assumptions that decide what a verdict actually covers.
 *
 * A verdict alone is not comparable between runs: attack modeling off and exhaustive compromise up
 * to a budget produce identical badges and identical device/rule/spec counts. History is the surface
 * users scan to decide whether their home is safe, so the scope has to be legible here and not only
 * one click away in the opened result.
 */
const runAssumptions = (run: AvailableVerificationRunSummary): string[] => {
  const assumptions: string[] = []
  const points = run.modelSemantics?.modeledAttackPointCount
  if (!run.isAttack) {
    assumptions.push(t('app.runAssumptionNoAttack'))
  } else if (run.modelSemantics?.attackSelectionPolicy === 'EXACT_ATTACK_POINTS') {
    // The mode comes from the policy, never from `attackBudget`: the backend reports
    // `effectiveBudget() == points.size()` for an exact-points run, so inferring the mode from a
    // positive budget would label two pinned points as an exhaustive search over two.
    assumptions.push(t('app.runAssumptionAttackPoints', {
      count: typeof points === 'number' ? points : (run.attackBudget ?? '?')
    }))
  } else if (typeof run.attackBudget === 'number' && run.attackBudget > 0) {
    assumptions.push(t('app.runAssumptionAttackBudget', {
      count: run.attackBudget,
      total: typeof points === 'number' ? points : '?'
    }))
  }
  if (run.enablePrivacy) assumptions.push(t('app.runAssumptionPrivacy'))
  return assumptions
}

const verificationOutcomeBadge = (run: AvailableVerificationRunSummary) => {
  if (run.outcome === 'VIOLATED') {
    return {
      label: t('app.verificationFailedWithViolations', { count: run.violatedSpecCount }),
      className: 'board-surface-danger board-text-danger'
    }
  }
  if (run.outcome === 'SATISFIED' && run.modelComplete) {
    return {
      label: t('app.verificationPassed'),
      className: 'board-surface-success board-text-success'
    }
  }
  if (run.outcome === 'SATISFIED') {
    return {
      label: t('app.verificationPassedWithGenerationWarnings'),
      className: 'board-surface-warning board-text-warning'
    }
  }
  return {
    label: t('app.verificationInconclusiveSummary'),
    className: 'board-surface-warning board-text-warning'
  }
}

const simulationOutcomeBadge = (run: AvailableSimulationTraceSummary) => run.modelComplete
  ? {
      label: t('app.allRulesModeled'),
      className: 'board-border-subtle board-chip-info board-text-info'
    }
  : {
      label: t('app.incompleteModel'),
      className: 'board-surface-warning board-text-warning'
    }

const fuzzingOutcomeBadge = (run: AvailableFuzzingRunSummary) => {
  if (run.outcome === 'FOUND_VIOLATION') {
    return {
      label: t('app.fuzzViolationFound'),
      className: 'board-surface-danger board-text-danger'
    }
  }
  if (run.outcome === 'BUDGET_EXHAUSTED') {
    return {
      label: t('app.fuzzBudgetExhausted'),
      className: 'board-border-subtle board-chip-info board-text-info'
    }
  }
  return {
    label: t('app.fuzzInconclusive'),
    className: 'board-surface-warning board-text-warning'
  }
}
</script>

<template>
  <div
    class="board-floating-panel history-panel board-surface-panel fixed top-20 z-30 flex w-[480px] max-w-[calc(100vw-2rem)] flex-col overflow-hidden rounded-xl border shadow-2xl"
    data-testid="trace-history-panel"
    role="region"
    aria-labelledby="trace-history-title"
    tabindex="-1"
    @keydown.esc.stop.prevent="emit('close')"
  >
    <div class="flex shrink-0 items-center justify-between bg-slate-800 p-4">
      <div class="flex min-w-0 items-center gap-3">
        <div class="flex h-10 w-10 shrink-0 items-center justify-center rounded-lg bg-[color:var(--accent-fill)] shadow-lg">
          <span class="material-symbols-outlined text-xl text-white">history</span>
        </div>
        <div class="min-w-0">
          <h3 id="trace-history-title" class="text-base font-bold text-white">{{ t('app.runHistory') }}</h3>
          <p class="truncate text-xs text-white/75">{{ t('app.runHistorySubtitle') }}</p>
        </div>
      </div>
      <HintTooltip :content="t('app.close')">
        <button
          ref="closeButtonRef"
          type="button"
          data-testid="close-history-panel"
          class="board-card flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-white/75 transition-colors hover:/10 hover:text-white"
          :aria-label="t('app.close')"
          @click="emit('close')"
        >
          <span class="material-symbols-outlined">close</span>
        </button>
      </HintTooltip>
    </div>

    <div class="board-panel-tabs shrink-0 border-b p-3">
      <div class="board-segmented grid grid-cols-2 gap-1 rounded-lg p-1">
        <button
          type="button"
          data-testid="history-layer-tasks"
          class="flex min-h-11 items-center justify-center gap-1 rounded-md px-3 py-2 text-xs font-bold transition-colors"
          :class="activeLayer === 'tasks' ? 'bg-white board-text-info shadow-sm' : 'text-slate-600 hover:text-slate-800'"
          :aria-pressed="activeLayer === 'tasks'"
          @click="emit('update:activeLayer', 'tasks')"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">pending_actions</span>
          {{ t('app.taskStatusLayer') }}
          <span v-if="activeTasks.length" class="rounded-full board-chip-info px-1.5 text-[length:var(--iot-font-min)] board-text-info">
            {{ activeTasks.length }}
          </span>
        </button>
        <button
          type="button"
          data-testid="history-layer-results"
          class="flex min-h-11 items-center justify-center gap-1 rounded-md px-3 py-2 text-xs font-bold transition-colors"
          :class="activeLayer === 'results' ? 'bg-white board-text-info shadow-sm' : 'text-slate-600 hover:text-slate-800'"
          :aria-pressed="activeLayer === 'results'"
          @click="emit('update:activeLayer', 'results')"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">fact_check</span>
          {{ t('app.historyResultsLayer') }}
        </button>
      </div>
    </div>

    <div class="iot-scroll-region board-panel-body min-h-0 flex-1 p-3">
      <div
        v-if="actionLocked"
        class="mb-3 flex items-start gap-2 rounded-lg board-surface-warning px-3 py-2 text-xs board-text-warning"
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
            class="flex min-h-11 items-center gap-1 px-2 text-xs font-medium board-text-info hover:board-text-strong"
            :disabled="loadingTasks"
            @click="emit('refresh-tasks')"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingTasks ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingTasks" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined animate-spin text-4xl board-text-progress">sync</span>
          <p class="mt-3 text-sm">{{ t('app.loadingTasks') }}</p>
        </div>

        <div v-else-if="taskItems.length === 0" class="flex flex-col items-center justify-center py-10 text-center">
          <div class="board-muted-surface mb-3 flex h-14 w-14 items-center justify-center rounded-full">
            <span class="material-symbols-outlined text-3xl text-slate-500">task_alt</span>
          </div>
          <p class="text-sm font-medium text-slate-600">{{ t('app.noPendingTasks') }}</p>
          <p class="mt-1 px-4 text-xs text-slate-500">{{ t('app.noPendingTasksHint') }}</p>
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
                    <span class="text-xs font-bold board-text-info">{{ taskKindLabel(task.kind) }}</span>
                    <span class="rounded-full border px-2 py-0.5 text-[11px] font-semibold" :class="statusClass(task.status)">
                      {{ formatStatus(task.status) }}
                    </span>
                    <RunInitiatorBadge :initiator="task.initiator" />
                    <span
                      v-if="task.kind === 'fuzzing'"
                      :data-testid="`fuzzing-task-mode-${task.id}`"
                      class="max-w-full rounded-full board-surface-info px-2 py-0.5 text-[length:var(--iot-font-min)] font-semibold board-text-info"
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
                    <div class="h-full rounded-full bg-[color:var(--accent)] transition-all" :style="{ width: `${taskProgress(task)}%` }"></div>
                  </div>
                  <div class="mt-1 flex justify-between text-[11px] text-slate-500">
                    <span>{{ taskProgress(task) }}%</span>
                    <span>{{ formatDate(task.createdAt) }}</span>
                  </div>
                </div>
                <div class="flex shrink-0 flex-col gap-1">
                  <button
                    type="button"
                    class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-xs font-medium text-white"
                    @click="emitWatchTask(task)"
                  >
                    {{ t('app.watchTask') }}
                  </button>
                  <button
                    type="button"
                    class="inline-flex min-h-11 items-center justify-center gap-1 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:board-chip-danger hover:board-text-danger disabled:cursor-wait disabled:opacity-60"
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
                    <span class="text-xs font-bold board-text-info">{{ taskKindLabel(task.kind) }}</span>
                    <span class="rounded-full border px-2 py-0.5 text-[11px] font-semibold" :class="statusClass(task.status)">
                      {{ formatStatus(task.status) }}
                    </span>
                    <RunInitiatorBadge :initiator="task.initiator" />
                    <span
                      v-if="task.kind === 'fuzzing'"
                      :data-testid="`fuzzing-task-mode-${task.id}`"
                      class="max-w-full rounded-full board-surface-info px-2 py-0.5 text-[length:var(--iot-font-min)] font-semibold board-text-info"
                      :title="fuzzingModeDescription(task.explorationMode)"
                    >
                      {{ fuzzingModeLabel(task.explorationMode) }}
                    </span>
                  </div>
                  <p class="mt-2 text-xs leading-5 text-slate-600">
                    {{ task.status === 'CANCELLED' ? t('app.cancelledTaskNoResult') : t('app.failedTaskNoResult') }}
                  </p>
                  <!-- The reported cause is shown, not hidden behind a disclosure. A failure whose
                       only visible text is "it produced no result" tells the user nothing they can
                       act on, and two independent reviews of a real failed run reported exactly
                       that: "the failure cause is missing". The raw text stays a technical
                       diagnostic, so it is labelled as one rather than presented as guidance. -->
                  <div
                    v-if="task.errorMessage"
                    :data-testid="`task-failure-reason-${task.kind}-${task.id}`"
                    class="mt-2 rounded board-surface-danger board-text-danger px-2 py-1.5 text-[11px] leading-5"
                  >
                    <span class="font-semibold">{{ t('app.technicalDetails') }}:</span>
                    <span class="ml-1 break-words">{{ task.errorMessage }}</span>
                  </div>
                  <div class="mt-1 text-[11px] text-slate-500">{{ formatDate(task.completedAt || task.createdAt) }}</div>
                </div>
                <div class="flex shrink-0 flex-col items-stretch gap-1">
                  <!-- A failed run needs a way forward, not just a way to hide it. This opens the
                       panel that owns launching the run so the settings can be checked against the
                       current board first; it is not a blind re-submit of stale parameters. -->
                  <button
                    type="button"
                    :data-testid="`reopen-task-settings-${task.kind}-${task.id}`"
                    class="inline-flex min-h-11 items-center justify-center gap-1 rounded board-panel-submit px-2 py-1 text-xs font-medium"
                    @click="emit('reopen-task-settings', task.kind)"
                  >
                    {{ t('app.adjustAndRunAgain') }}
                  </button>
                  <button
                    type="button"
                    class="inline-flex min-h-11 items-center justify-center gap-1 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:bg-slate-200 disabled:cursor-wait disabled:opacity-60"
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
              :class="resultFilter === filter ? 'bg-white board-text-info shadow-sm' : 'text-slate-500 hover:text-slate-700'"
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
            class="flex min-h-11 shrink-0 items-center gap-1 px-2 text-xs font-medium board-text-info hover:board-text-strong"
            :disabled="loadingResults"
            @click="emit('refresh-results')"
          >
            <span class="material-symbols-outlined text-sm" :class="loadingResults ? 'animate-spin' : ''">refresh</span>
            {{ t('app.refresh') }}
          </button>
        </div>

        <div v-if="loadingResults" class="flex flex-col items-center justify-center py-10 text-slate-500">
          <span class="material-symbols-outlined animate-spin text-4xl board-text-progress">sync</span>
          <p class="mt-3 text-sm">{{ t('app.loadingRunResults') }}</p>
        </div>

        <div
          v-if="!loadingResults && resultErrorEntries.length > 0"
          data-testid="history-results-load-error"
          class="rounded-lg board-surface-warning px-3 py-2.5 text-xs leading-5 board-text-warning"
          role="alert"
        >
          <div class="flex items-start gap-2">
            <span class="material-symbols-outlined mt-0.5 text-base board-text-warning" aria-hidden="true">warning</span>
            <div class="min-w-0 flex-1">
              <p class="font-bold">{{ t('app.historyResultsPartialFailure') }}</p>
              <ul class="mt-1 list-disc space-y-0.5 pl-4">
                <li v-for="entry in resultErrorEntries" :key="entry.source">
                  {{ resultSourceLabel(entry.source) }}: {{ entry.message }}
                </li>
              </ul>
              <button
                type="button"
                class="mt-2 inline-flex min-h-11 items-center gap-1 rounded-md border board-border-subtle bg-white px-2 py-1 text-[11px] font-semibold board-text-warning hover:board-chip-warning disabled:opacity-50"
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
            <!-- Decoration: the two lines below carry the whole message, so this glyph adds no information a
                 screen reader needs and SC 1.4.3 does not apply to it. It measured 1.42:1 without the
                 attribute, which read as a contrast defect on an illustration that is meant to be faint. -->
            <span class="material-symbols-outlined text-3xl text-slate-300" aria-hidden="true">fact_check</span>
          </div>
          <p class="text-sm font-medium text-slate-600">{{ t('app.noRunResults') }}</p>
          <!-- slate-500, not slate-400: this hint is real text explaining an empty state, and slate-400 is
               2.56:1 on white. slate-500 is 4.76 and reads as the same de-emphasised step. -->
          <p class="mt-1 px-4 text-xs text-slate-500">{{ t('app.noRunResultsHint') }}</p>
        </div>

        <div v-if="!loadingResults && resultItems.length > 0" class="space-y-3">
          <article
            v-for="item in resultItems"
            :key="`${item.kind}-${item.run.id}`"
            class="board-card-surface rounded-lg border p-3 shadow-sm transition-colors hover:border-[color:var(--accent)]"
          >
            <template v-if="item.run.dataAvailable === false">
              <div class="flex items-start justify-between gap-3">
                <div class="min-w-0 flex-1">
                  <div class="flex items-center gap-2 board-text-warning">
                    <span class="material-symbols-outlined text-base" aria-hidden="true">warning</span>
                    <span class="text-xs font-bold">{{ t('app.historyItemUnavailable') }}</span>
                    <RunInitiatorBadge :initiator="item.run.initiator" />
                  </div>
                  <p class="mt-1 text-[11px] leading-4 text-slate-600">
                    {{ t('app.historyItemUnavailableDetail') }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ formatDate(item.kind === 'simulation' ? item.run.createdAt : (item.run.completedAt || item.run.createdAt)) }}
                  </p>
                </div>
                <button
                  type="button"
                  :data-testid="resultDeleteTestId(item.kind, item.run.id)"
                  class="min-h-11 shrink-0 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:board-chip-danger hover:board-text-danger disabled:opacity-50"
                  :disabled="actionLocked || isResultDeletePending(item.kind, item.run.id)"
                  :aria-busy="isResultDeletePending(item.kind, item.run.id)"
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
                    <span class="text-xs font-bold board-text-info">{{ t('app.verificationRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full px-2 py-0.5 text-[11px] font-semibold"
                      :class="verificationOutcomeBadge(item.run).className"
                      :title="verificationOutcomeBadge(item.run).label"
                    >
                      <span class="truncate">{{ verificationOutcomeBadge(item.run).label }}</span>
                    </span>
                    <RunInitiatorBadge :initiator="item.run.initiator" />
                  </div>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.runScopeCounts', {
                      devices: item.run.modelSnapshot.deviceCount,
                      rules: item.run.modelSnapshot.ruleCount,
                      specs: item.run.modelSnapshot.specificationCount
                    }) }}
                  </p>
                  <ul
                    v-if="runAssumptions(item.run).length"
                    class="mt-1 flex flex-wrap gap-1"
                    :aria-label="t('app.runAssumptionsLabel')"
                    :data-testid="`verification-run-assumptions-${item.run.id}`"
                  >
                    <li
                      v-for="assumption in runAssumptions(item.run)"
                      :key="assumption"
                      class="rounded border border-slate-300 px-1.5 py-0.5 text-[length:var(--iot-font-min)] text-slate-600 dark:border-slate-600 dark:text-slate-300"
                    >{{ assumption }}</li>
                  </ul>
                  <!-- A run reopened from history has no client submission to compare against, so its
                       board-comparison chip reads "not compared" while Fix stays enabled. The backend's
                       drift guards make that fail safe, but an enabled button reads as "this repair
                       applies to my current board" — say otherwise up front. Stated once per run: one
                       warning per counterexample would be the same sentence repeated N times. -->
                  <p
                    v-if="item.run.counterexamples.length"
                    :id="`historical-fix-caveat-${item.run.id}`"
                    :data-testid="`historical-fix-caveat-${item.run.id}`"
                    class="mt-1 text-[length:var(--iot-font-min)] board-text-warning"
                  >
                    {{ t('app.historicalFixMayFailIfBoardChanged') }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-500">{{ formatDate(item.run.completedAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`open-verification-run-${item.run.id}`"
                    class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-xs font-medium text-white disabled:cursor-not-allowed board-action-disarmed"
                    :disabled="actionLocked"
                    @click="emit('open-verification-run', item.run.id)"
                  >
                    {{ t('app.openResult') }}
                  </button>
                  <!--
                    Hidden when the run holds no model, unlike the result dialogs, which disable the
                    control and state the reason. The difference is deliberate: this is a dense list of
                    every retained run, so a disabled button plus an explanation on each row would
                    repeat the same notice many times over. The dialog is a single run the user opened
                    on purpose, and there the absence needs saying — the whole feature read as missing
                    while nothing explained why no button appeared.
                  -->
                  <button
                    v-if="item.run.hasSmvModel"
                    type="button"
                    :data-testid="`download-verification-run-smv-${item.run.id}`"
                    class="min-h-11 rounded board-chip-info px-2 py-1 text-xs font-medium board-text-info hover:bg-[color:var(--info-surface)] disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('download-verification-run-smv', item.run.id)"
                  >
                    {{ t('app.downloadSmvModel') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-verification-run-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:board-chip-danger hover:board-text-danger disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked || isResultDeletePending('verification', item.run.id)"
                    :aria-busy="isResultDeletePending('verification', item.run.id)"
                    @click="emit('delete-verification-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>

              <p
                v-if="runScopeComparison(item.run, true) === 'COUNTS_CHANGED'"
                class="mt-2 rounded-md board-surface-warning px-2 py-1.5 text-[11px] font-semibold leading-4 board-text-warning"
                data-testid="verification-history-board-drift"
              >
                {{ t('app.historicalRunBoardScopeChanged') }}
              </p>
              <!--
                Matching counts are not a match. Stated quietly (muted, not a warning) because it is a
                limit of the comparison rather than a problem with the run — but stated, because the
                previous silence read as "this verdict still describes your canvas".
              -->
              <p
                v-else-if="runScopeComparison(item.run, true) === 'COUNTS_ONLY_MATCH'"
                class="mt-2 text-[11px] leading-4 text-slate-500"
                data-testid="verification-history-scope-counts-only"
              >
                {{ t('app.historicalRunScopeCountsOnly') }}
              </p>

              <ul v-if="generationIssuesFor(item.run).length" class="mt-2 space-y-1.5">
                <li
                  v-for="(issue, index) in generationIssuesFor(item.run)"
                  :key="`${issue.itemLabel}-${index}`"
                  class="border-l-2 board-border-subtle pl-2 text-[11px] leading-4 board-text-warning"
                >
                  <span class="font-semibold">{{ issue.itemLabel || t('app.unknownModelItem') }}</span>
                  <span>: {{ t(generationIssueReasonKey(issue)) }}</span>
                </li>
              </ul>

              <!--
                Gated on the run having evidence to describe, NOT on the trace list being non-empty.

                It used to require `tracesForRun(item.run).length`, which hid the whole block in exactly
                the case its own inner warning exists to explain: a run can count a specification as
                violated and produce no replayable counterexample at all — `VerificationServiceImpl`
                logs "violated (no counterexample)" for an unparseable one, and skips the trace when the
                parsed state list comes back empty. That left "3 violations" on screen with nothing
                saying why none of them could be replayed, and the sentence written for it
                (`counterexampleCount < violatedSpecCount`, true at zero) could never render.
              -->
              <div
                v-if="tracesForRun(item.run).length
                  || item.run.violatedSpecCount > 0
                  || item.run.counterexampleCount > 0"
                class="mt-3 rounded-lg border p-2.5"
                :class="item.run.outcome === 'VIOLATED'
                  ? 'board-surface-danger'
                  : 'board-surface-warning'"
              >
                <div class="flex flex-wrap items-center justify-between gap-2">
                  <span
                    class="text-xs font-semibold"
                    :class="item.run.outcome === 'VIOLATED' ? 'board-text-danger' : 'board-text-warning'"
                  >
                    {{ item.run.outcome === 'VIOLATED'
                      ? t('app.violationEvidenceSummary', {
                        violations: item.run.violatedSpecCount,
                        counterexamples: item.run.counterexampleCount
                      })
                      : t('app.inconclusiveEvidenceSummary', {
                        counterexamples: item.run.counterexampleCount
                      }) }}
                  </span>
                </div>
                <p
                  v-if="item.run.outcome === 'VIOLATED'
                    && item.run.counterexampleCount < item.run.violatedSpecCount"
                  class="mt-1 text-[11px] leading-4 board-text-warning"
                >
                  {{ t('app.someViolationsHaveNoReplayableCounterexample') }}
                </p>
                <div v-if="tracesForRun(item.run).length" class="mt-2 space-y-1.5">
                  <div
                    v-for="trace in tracesForRun(item.run)"
                    :key="trace.id"
                    class="flex items-center justify-between gap-2 rounded-md border board-border-subtle bg-white px-2 py-1.5"
                  >
                    <div class="min-w-0">
                      <p class="truncate text-[11px] font-medium text-slate-700" :title="traceSpecTitle(trace)">
                        {{ traceSpecTitle(trace) }}
                      </p>
                      <p v-if="trace.dataAvailable" class="text-[length:var(--iot-font-min)] text-slate-500">
                        {{ t('app.statesCount', { count: trace.stateCount || 0 }) }}
                      </p>
                      <p v-else class="text-[length:var(--iot-font-min)] font-medium board-text-warning">
                        {{ t('app.historyTraceUnavailableDetail') }}
                      </p>
                    </div>
                    <div class="flex shrink-0 gap-1">
                      <button
                        type="button"
                        :data-testid="`view-verification-trace-${trace.id}`"
                        class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-[11px] font-medium text-white board-action-disarmed"
                        :disabled="actionLocked || !trace.dataAvailable"
                        @click="emit('view-verification-trace', trace.id)"
                      >
                        {{ t('app.replay') }}
                      </button>
                      <!--
                        No per-counterexample SMV download here. One model is checked per run and every
                        counterexample under it came from that model, so a button on each row offered
                        the same file N times under a name implying N different models. The run row
                        above carries it once (`download-verification-run-smv-<runId>`), which is also
                        the only copy that exists for a run where every specification held.
                      -->
                      <button
                        type="button"
                        :data-testid="`fix-verification-trace-${trace.id}`"
                        class="min-h-11 rounded board-chip-warning px-2 py-1 text-[11px] font-medium board-text-warning hover:bg-[color:var(--warning-surface)] disabled:opacity-50"
                        :disabled="actionLocked || !trace.dataAvailable"
                        :aria-describedby="trace.dataAvailable ? `historical-fix-caveat-${item.run.id}` : undefined"
                        @click="emit('fix-verification-trace', trace)"
                      >
                        {{ t('app.fixRules') }}
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
                    <span class="text-xs font-bold board-text-info">{{ t('app.fuzzRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full px-2 py-0.5 text-[11px] font-semibold"
                      :class="fuzzingOutcomeBadge(item.run).className"
                    >
                      <span class="truncate">{{ fuzzingOutcomeBadge(item.run).label }}</span>
                    </span>
                    <span
                      :data-testid="`fuzzing-history-mode-${item.run.id}`"
                      class="max-w-full rounded-full board-surface-info px-2 py-0.5 text-[length:var(--iot-font-min)] font-semibold board-text-info"
                      :title="fuzzingModeDescription(item.run.explorationMode)"
                    >
                      {{ fuzzingModeLabel(item.run.explorationMode) }}
                    </span>
                    <RunInitiatorBadge :initiator="item.run.initiator" />
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
                  <p class="mt-1 text-[11px] text-slate-500">{{ formatDate(item.run.completedAt || item.run.createdAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`open-fuzzing-run-${item.run.id}`"
                    class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-xs font-medium text-white hover:bg-[color:var(--accent-fill-hover)] disabled:cursor-not-allowed board-action-disarmed"
                    :disabled="actionLocked"
                    @click="emit('open-fuzzing-run', item.run.id)"
                  >
                    {{ t('app.openResult') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-fuzzing-run-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:board-chip-danger hover:board-text-danger disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked || isResultDeletePending('fuzzing', item.run.id)"
                    :aria-busy="isResultDeletePending('fuzzing', item.run.id)"
                    @click="emit('delete-fuzzing-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>

              <p
                v-if="fuzzRunHasBoardDrift(item.run)"
                class="mt-2 rounded-md board-surface-warning px-2 py-1.5 text-[11px] font-semibold leading-4 board-text-warning"
                data-testid="fuzzing-history-board-drift"
              >
                {{ t('app.fuzzBoardScopeChanged') }}
              </p>

              <p
                v-if="item.run.outcome === 'BUDGET_EXHAUSTED'"
                class="mt-2 rounded-md board-surface-info px-2 py-1.5 text-[11px] leading-4"
              >
                {{ t('app.fuzzNoViolationWithinBudget') }}
              </p>

              <div
                v-if="item.run.outcome === 'FOUND_VIOLATION' && item.run.findings?.length"
                class="mt-3 rounded-lg border board-surface-danger p-2.5"
              >
                <div class="text-xs font-semibold board-text-danger">
                  {{ t('app.fuzzFindingsCount', { count: item.run.findings.length }) }}
                </div>
                <div class="mt-2 space-y-1.5">
                  <div
                    v-for="finding in item.run.findings"
                    :key="finding.id"
                    class="flex items-center justify-between gap-2 rounded-md border board-border-subtle bg-white px-2 py-1.5"
                  >
                    <div class="min-w-0">
                      <p class="truncate text-[11px] font-medium text-slate-700" :title="fuzzFindingTitle(finding)">
                        {{ fuzzFindingTitle(finding) }}
                      </p>
                      <p v-if="finding.dataAvailable !== false" class="text-[length:var(--iot-font-min)] text-slate-500">
                        {{ t('app.fuzzFirstViolationStep', { step: displayStep(finding.firstViolationStep) }) }}
                      </p>
                      <p v-else class="text-[length:var(--iot-font-min)] font-medium board-text-warning">
                        {{ t('app.historyFindingUnavailableDetail') }}
                      </p>
                    </div>
                    <div class="flex shrink-0 gap-1">
                      <button
                        type="button"
                        :data-testid="`view-fuzzing-finding-${finding.id}`"
                        class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-[11px] font-medium text-white hover:bg-[color:var(--accent-fill-hover)] board-action-disarmed"
                        :disabled="actionLocked || finding.dataAvailable === false"
                        @click="emit('view-fuzzing-finding', finding.id, item.run.id)"
                      >
                        {{ t('app.replay') }}
                      </button>
                      <button
                        type="button"
                        :data-testid="`verify-fuzzing-finding-${finding.id}`"
                        class="min-h-11 rounded board-chip-success px-2 py-1 text-[11px] font-medium board-text-success hover:bg-[color:var(--success-surface)] disabled:opacity-50"
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
                    <span class="text-xs font-bold board-text-info">{{ t('app.simulationRunResult') }}</span>
                    <span
                      class="inline-flex min-w-0 max-w-full items-center rounded-full px-2 py-0.5 text-[11px] font-semibold"
                      :class="simulationOutcomeBadge(item.run).className"
                    >
                      <span class="truncate">{{ simulationOutcomeBadge(item.run).label }}</span>
                    </span>
                    <RunInitiatorBadge :initiator="item.run.initiator" />
                  </div>
                  <p class="mt-1 text-[11px] text-slate-500">
                    {{ t('app.simulationHistoryCounts', {
                      requested: item.run.requestedSteps,
                      steps: item.run.steps,
                      states: item.run.steps + 1
                    }) }}
                  </p>
                  <p class="mt-1 text-[11px] text-slate-500">{{ formatDate(item.run.createdAt) }}</p>
                </div>
                <div class="flex shrink-0 flex-wrap justify-end gap-1">
                  <button
                    type="button"
                    :data-testid="`replay-simulation-trace-${item.run.id}`"
                    class="min-h-11 rounded bg-[color:var(--accent-fill)] px-2 py-1 text-xs font-medium text-white disabled:cursor-not-allowed board-action-disarmed"
                    :disabled="actionLocked"
                    @click="emit('view-simulation-run', item.run.id)"
                  >
                    {{ t('app.replay') }}
                  </button>
                  <button
                    v-if="item.run.hasSmvModel"
                    type="button"
                    :data-testid="`download-simulation-trace-smv-${item.run.id}`"
                    class="min-h-11 rounded board-chip-info px-2 py-1 text-xs font-medium board-text-info hover:bg-[color:var(--info-surface)] disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked"
                    @click="emit('download-simulation-trace-smv', item.run.id)"
                  >
                    {{ t('app.downloadSmvModel') }}
                  </button>
                  <button
                    type="button"
                    :data-testid="`delete-simulation-trace-${item.run.id}`"
                    class="min-h-11 rounded bg-slate-100 px-2 py-1 text-xs font-medium text-slate-700 hover:board-chip-danger hover:board-text-danger disabled:cursor-not-allowed disabled:opacity-50"
                    :disabled="actionLocked || isResultDeletePending('simulation', item.run.id)"
                    :aria-busy="isResultDeletePending('simulation', item.run.id)"
                    @click="emit('delete-simulation-run', item.run)"
                  >
                    {{ t('app.delete') }}
                  </button>
                </div>
              </div>
              <p
                v-if="runScopeComparison(item.run, false) === 'COUNTS_CHANGED'"
                class="mt-2 rounded-md board-surface-warning px-2 py-1.5 text-[11px] font-semibold leading-4 board-text-warning"
                data-testid="simulation-history-board-drift"
              >
                {{ t('app.historicalRunBoardScopeChanged') }}
              </p>
              <!-- `false` for specifications: a trajectory checks none, so a spec edit is not drift for it. -->
              <p
                v-else-if="runScopeComparison(item.run, false) === 'COUNTS_ONLY_MATCH'"
                class="mt-2 text-[11px] leading-4 text-slate-500"
                data-testid="simulation-history-scope-counts-only"
              >
                {{ t('app.historicalRunScopeCountsOnly') }}
              </p>
              <ul v-if="generationIssuesFor(item.run).length" class="mt-2 space-y-1.5">
                <li
                  v-for="(issue, index) in generationIssuesFor(item.run)"
                  :key="`${issue.itemLabel}-${index}`"
                  class="border-l-2 board-border-subtle pl-2 text-[11px] leading-4 board-text-warning"
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
            class="flex min-h-11 w-full items-center justify-center gap-1 rounded-md border border-slate-200 bg-white px-3 py-2 text-xs font-semibold board-text-info hover:border-[color:var(--accent)] hover:board-chip-info disabled:cursor-not-allowed disabled:opacity-50"
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
