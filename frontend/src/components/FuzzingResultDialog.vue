<script setup lang="ts">
import { computed, toRef } from 'vue'
import { useI18n } from 'vue-i18n'
import type { AvailableFuzzingRunSummary, FuzzingFinding, FuzzingFindingSummary, FuzzingRun } from '@/types/fuzzing'
import { formatTraceSpec } from '@/utils/traceView'
import { useModalAccessibility } from '@/composables/useModalAccessibility'
import { fuzzingLimitationKey } from '@/utils/fuzzingPresentation'

const props = defineProps<{
  visible: boolean
  run: AvailableFuzzingRunSummary | FuzzingRun | null
  loading?: boolean
  error?: string | null
  actionLocked?: boolean
  boardDrifted?: boolean
}>()

const emit = defineEmits<{
  close: []
  replay: [findingId: number]
  verify: [finding: FuzzingFindingSummary | FuzzingFinding]
  verifyCurrentBoard: []
  reuseSettings: []
}>()

const { t, locale } = useI18n()

const closeDialog = () => emit('close')
const { setDialogRef, handleModalKeydown } = useModalAccessibility(
  toRef(props, 'visible'),
  closeDialog,
  () => document.querySelector<HTMLElement>('[data-testid="open-fuzzing-panel"]')
)

const outcome = computed(() => {
  if (props.run?.outcome === 'FOUND_VIOLATION') {
    return {
      icon: 'warning',
      label: t('app.fuzzViolationFound'),
      detail: t('app.fuzzViolationFoundDetail'),
      className: 'border-red-200 bg-red-50 text-red-900 dark:border-red-800 dark:bg-red-950/50 dark:text-red-100',
      iconClass: 'bg-red-100 text-red-700 dark:bg-red-900/70 dark:text-red-200'
    }
  }
  if (props.run?.outcome === 'BUDGET_EXHAUSTED') {
    return {
      icon: 'search_off',
      label: t('app.fuzzBudgetExhausted'),
      detail: t('app.fuzzNoViolationWithinBudget'),
      className: 'border-sky-200 bg-sky-50 text-sky-950 dark:border-sky-800 dark:bg-sky-950/50 dark:text-sky-100',
      iconClass: 'bg-sky-100 text-sky-700 dark:bg-sky-900/70 dark:text-sky-200'
    }
  }
  return {
    icon: 'help',
    label: t('app.fuzzInconclusive'),
    detail: t('app.fuzzInconclusiveDetail'),
    className: 'border-amber-200 bg-amber-50 text-amber-950 dark:border-amber-800 dark:bg-amber-950/50 dark:text-amber-100',
    iconClass: 'bg-amber-100 text-amber-700 dark:bg-amber-900/70 dark:text-amber-200'
  }
})

const findingTitle = (finding: FuzzingFindingSummary | FuzzingFinding) => {
  const formatted = finding.violatedSpec ? formatTraceSpec(finding.violatedSpec, t) : ''
  return formatted
    || ('specificationLabel' in finding ? finding.specificationLabel : '')
    || finding.violatedSpecId
    || t('app.unknownSpecification')
}

const findingDataAvailable = (finding: FuzzingFindingSummary | FuzzingFinding) =>
  !('dataAvailable' in finding) || finding.dataAvailable !== false

const elapsedSeconds = computed(() => Math.max(0, Math.round((props.run?.elapsedMs || 0) / 1000)))
const elapsedLabel = computed(() => t(
  elapsedSeconds.value === 1 ? 'app.fuzzElapsedSecond' : 'app.fuzzElapsedSeconds',
  { count: elapsedSeconds.value }
))
const explorationModeLabel = computed(() => t(
  props.run?.explorationMode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzModePaper'
    : 'app.fuzzModeBoard'
))
const explorationModeDescription = computed(() => t(
  props.run?.explorationMode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzModePaperDescription'
    : 'app.fuzzModeBoardDescription'
))
const displayStep = (zeroBasedStep: number) => zeroBasedStep + 1
const formatDate = (value: string) => {
  const date = new Date(value)
  return Number.isNaN(date.getTime())
    ? value
    : date.toLocaleString(locale.value.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US')
}

const eligibilityReasonKeys: Record<string, string> = {
  UNSUPPORTED_TEMPLATE: 'app.fuzzEligibilityUnsupportedTemplate',
  TRUST_PRIVACY_UNSUPPORTED: 'app.fuzzEligibilityTrustPrivacyUnsupported',
  ATTACK_CONCEPT_UNSUPPORTED: 'app.fuzzEligibilityAttackUnsupported',
  CONTENT_COMMAND_UNSUPPORTED: 'app.fuzzEligibilityContentCommandUnsupported',
  MODEL_INVALID: 'app.fuzzEligibilityModelInvalid',
  INVALID_SPECIFICATION: 'app.fuzzEligibilityInvalidSpecification'
}

const eligibilityReason = (reasonCode: string) =>
  t(eligibilityReasonKeys[reasonCode] || 'app.fuzzEligibilityUnknown')

const limitationText = (code: string) =>
  t(fuzzingLimitationKey(code))

const capabilityBoundaryHeading = computed(() => t(
  props.run?.explorationMode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzPaperCapabilitiesAndBoundaries'
    : 'app.fuzzLimitations'
))

const findingBySpecification = computed(() => new Map(
  (props.run?.findings || []).map(finding => [finding.violatedSpecId, finding])
))

const targetResults = computed(() => (props.run?.eligibility.eligibleSpecIds || []).map(specId => ({
  specId,
  label: props.run?.eligibility.eligibleSpecLabels[specId] || specId,
  finding: findingBySpecification.value.get(specId)
})))

const requestedTargetIds = computed(() => {
  const run = props.run
  return run && 'targetSpecIds' in run ? run.targetSpecIds : []
})

const targetScopeText = computed(() => requestedTargetIds.value.length > 0
  ? t('app.fuzzReproductionSelectedTargets', { count: requestedTargetIds.value.length })
  : t('app.fuzzReproductionAllTargets', { count: props.run?.eligibility.requestedSpecCount || 0 }))
</script>

<template>
  <div
    v-if="visible"
    class="fixed inset-0 z-[2400] flex items-center justify-center bg-black/60 p-4 backdrop-blur-sm"
    data-testid="fuzzing-result-dialog"
    @keydown="handleModalKeydown"
  >
    <section
      :ref="setDialogRef"
      class="flex max-h-[90vh] w-[760px] max-w-[95vw] flex-col overflow-hidden rounded-lg border border-slate-200 bg-white shadow-2xl dark:border-slate-700 dark:bg-slate-900"
      role="dialog"
      aria-modal="true"
      aria-labelledby="fuzzing-result-title"
      aria-describedby="fuzzing-result-description"
      tabindex="-1"
    >
      <header class="flex items-center justify-between gap-4 border-b border-slate-200 bg-slate-50 px-5 py-4 dark:border-slate-700 dark:bg-slate-950">
        <div class="flex min-w-0 items-center gap-3">
          <div class="flex h-10 w-10 shrink-0 items-center justify-center rounded-lg bg-indigo-100 text-indigo-700 dark:bg-indigo-900/60 dark:text-indigo-200">
            <span class="material-symbols-outlined" aria-hidden="true">radar</span>
          </div>
          <div class="min-w-0">
            <h3 id="fuzzing-result-title" class="text-base font-bold text-slate-900 dark:text-slate-100">{{ t('app.fuzzRunResult') }}</h3>
            <p id="fuzzing-result-description" class="mt-0.5 text-xs leading-5 text-slate-600 dark:text-slate-300">{{ t('app.fuzzResultHeuristicNotice') }}</p>
          </div>
        </div>
        <button
          type="button"
          data-testid="close-fuzzing-result"
          class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-lg text-slate-500 hover:bg-slate-200 hover:text-slate-800 dark:text-slate-300 dark:hover:bg-slate-800 dark:hover:text-white"
          :title="t('app.close')"
          :aria-label="t('app.close')"
          @click="closeDialog"
        >
          <span class="material-symbols-outlined" aria-hidden="true">close</span>
        </button>
      </header>

      <div class="min-h-0 flex-1 space-y-4 overflow-y-auto p-5">
        <div v-if="loading" class="flex flex-col items-center justify-center py-16 text-slate-500 dark:text-slate-300">
          <span class="material-symbols-outlined animate-spin text-4xl text-indigo-600 dark:text-indigo-300" aria-hidden="true">sync</span>
          <p class="mt-3 text-sm">{{ t('app.loadingFuzzRun') }}</p>
        </div>

        <div v-else-if="error" class="rounded-lg border border-red-200 bg-red-50 p-4 text-sm leading-6 text-red-800 dark:border-red-800 dark:bg-red-950/50 dark:text-red-100" role="alert">
          {{ error }}
        </div>

        <template v-else-if="run">
          <div class="rounded-lg border p-4" :class="outcome.className">
            <div class="flex items-start gap-3">
              <span class="material-symbols-outlined flex h-9 w-9 shrink-0 items-center justify-center rounded-lg" :class="outcome.iconClass" aria-hidden="true">{{ outcome.icon }}</span>
              <div>
                <div class="text-sm font-bold">{{ outcome.label }}</div>
                <p class="mt-1 text-xs leading-5 opacity-90">{{ outcome.detail }}</p>
              </div>
            </div>
          </div>

          <section
            data-testid="fuzzing-result-mode"
            class="rounded-lg border px-3 py-2.5"
            :class="run.explorationMode === 'PAPER_COMPATIBLE'
              ? 'border-amber-200 bg-amber-50 text-amber-950 dark:border-amber-800 dark:bg-amber-950/50 dark:text-amber-100'
              : 'border-indigo-100 bg-indigo-50 text-indigo-950 dark:border-indigo-800 dark:bg-indigo-950/50 dark:text-indigo-100'"
            :aria-label="t('app.fuzzExplorationMode')"
          >
            <div class="flex flex-wrap items-center gap-2">
              <span class="text-[10px] font-bold uppercase text-slate-500 dark:text-slate-300">{{ t('app.fuzzExplorationMode') }}</span>
              <span class="max-w-full rounded-full bg-white px-2 py-0.5 text-[11px] font-bold shadow-sm dark:bg-slate-800">
                {{ explorationModeLabel }}
              </span>
            </div>
            <p class="mt-1 break-words text-[11px] leading-5">{{ explorationModeDescription }}</p>
          </section>

          <section aria-labelledby="fuzz-run-summary-title">
            <h4 id="fuzz-run-summary-title" class="text-sm font-bold text-slate-800 dark:text-slate-100">{{ t('app.runSummary') }}</h4>
            <div class="mt-2 grid grid-cols-2 gap-px overflow-hidden rounded-lg border border-slate-200 bg-slate-200 sm:grid-cols-4 dark:border-slate-700 dark:bg-slate-700">
              <div class="bg-white p-3 dark:bg-slate-800">
                <div class="text-[10px] font-bold uppercase text-slate-500 dark:text-slate-400">{{ t('app.fuzzIterations') }}</div>
                <div class="mt-1 text-lg font-bold text-slate-900 dark:text-slate-100">{{ run.iterations }}</div>
              </div>
              <div class="bg-white p-3 dark:bg-slate-800">
                <div class="text-[10px] font-bold uppercase text-slate-500 dark:text-slate-400">{{ t('app.fuzzGeneratedPaths') }}</div>
                <div class="mt-1 text-lg font-bold text-slate-900 dark:text-slate-100">{{ run.generatedPaths }}</div>
              </div>
              <div class="bg-white p-3 dark:bg-slate-800">
                <div class="text-[10px] font-bold uppercase text-slate-500 dark:text-slate-400">{{ t('app.fuzzElapsed') }}</div>
                <div class="mt-1 text-lg font-bold text-slate-900 dark:text-slate-100">{{ elapsedLabel }}</div>
              </div>
              <div class="bg-white p-3 dark:bg-slate-800">
                <div class="text-[10px] font-bold uppercase text-slate-500 dark:text-slate-400">{{ t('app.fuzzEffectiveSeed') }}</div>
                <div class="mt-1 truncate font-mono text-sm font-bold text-slate-900 dark:text-slate-100" :title="String(run.effectiveSeed)">{{ run.effectiveSeed }}</div>
              </div>
            </div>
          </section>

          <section class="rounded-lg border border-slate-200 bg-white px-3 py-3 dark:border-slate-700 dark:bg-slate-800" aria-labelledby="fuzz-reproduction-title">
            <div class="flex flex-wrap items-start justify-between gap-2">
              <div class="min-w-0">
                <h4 id="fuzz-reproduction-title" class="text-xs font-bold text-slate-800 dark:text-slate-100">{{ t('app.fuzzReproductionSettings') }}</h4>
                <p class="mt-1 text-[11px] leading-4 text-slate-500 dark:text-slate-400">{{ t('app.fuzzReproductionHint') }}</p>
              </div>
              <button
                type="button"
                data-testid="reuse-fuzzing-settings"
                class="inline-flex min-h-11 shrink-0 items-center gap-1 rounded-md border border-indigo-200 bg-indigo-50 px-2.5 py-1.5 text-[11px] font-semibold text-indigo-800 hover:bg-indigo-100 disabled:opacity-50 dark:border-indigo-700 dark:bg-indigo-950/60 dark:text-indigo-200 dark:hover:bg-indigo-900/70"
                :disabled="actionLocked"
                @click="emit('reuseSettings')"
              >
                <span class="material-symbols-outlined text-sm" aria-hidden="true">settings_backup_restore</span>{{ t('app.fuzzReuseSettings') }}
              </button>
            </div>
            <dl class="mt-2 grid grid-cols-2 gap-x-4 gap-y-2 text-[11px] sm:grid-cols-3">
              <div>
                <dt class="text-slate-500 dark:text-slate-400">{{ t('app.fuzzEffectiveSeed') }}</dt>
                <dd class="break-all font-mono font-semibold text-slate-800 dark:text-slate-100">{{ run.effectiveSeed }}</dd>
              </div>
              <div>
                <dt class="text-slate-500 dark:text-slate-400">{{ t('app.fuzzMaxIterations') }}</dt>
                <dd class="font-semibold text-slate-800 dark:text-slate-100">{{ run.maxIterations }}</dd>
              </div>
              <div>
                <dt class="text-slate-500 dark:text-slate-400">{{ t('app.fuzzPathLength') }}</dt>
                <dd class="font-semibold text-slate-800 dark:text-slate-100">{{ run.pathLength }}</dd>
              </div>
              <div>
                <dt class="text-slate-500 dark:text-slate-400">{{ t('app.fuzzPopulationSize') }}</dt>
                <dd class="font-semibold text-slate-800 dark:text-slate-100">{{ run.populationSize }}</dd>
              </div>
              <div class="col-span-2">
                <dt class="text-slate-500 dark:text-slate-400">{{ t('app.fuzzTargetSpecifications') }}</dt>
                <dd class="font-semibold text-slate-800 dark:text-slate-100">{{ targetScopeText }}</dd>
              </div>
            </dl>
          </section>

          <section class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 dark:border-slate-700 dark:bg-slate-800" aria-labelledby="fuzz-snapshot-title">
            <h4 id="fuzz-snapshot-title" class="text-xs font-bold text-slate-800 dark:text-slate-100">{{ t('app.runScopeAndSnapshot') }}</h4>
            <p class="mt-1 text-[11px] leading-5 text-slate-600 dark:text-slate-300">
              {{ t('app.modelRunSnapshotSummary', {
                time: formatDate(run.modelSnapshot.capturedAt),
                devices: run.modelSnapshot.deviceCount,
                rules: run.modelSnapshot.ruleCount,
                specs: run.modelSnapshot.specificationCount,
                variables: run.modelSnapshot.environmentVariableCount,
                templates: run.modelSnapshot.deviceTemplateCount
              }) }}
            </p>
            <p
              v-if="boardDrifted"
              class="mt-2 rounded-md border border-amber-200 bg-amber-50 px-2 py-1.5 text-[11px] font-semibold leading-4 text-amber-900 dark:border-amber-800 dark:bg-amber-950/50 dark:text-amber-100"
              data-testid="fuzzing-board-drift-warning"
            >
              {{ t('app.fuzzBoardScopeChanged') }}
            </p>
            <p v-else class="mt-1 text-[11px] leading-4 text-slate-500 dark:text-slate-400">{{ t('app.fuzzBoardScopeCurrent') }}</p>
          </section>

          <div
            v-if="run.eligibility.ineligibleSpecs.length > 0"
            class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs leading-5 text-amber-900 dark:border-amber-800 dark:bg-amber-950/50 dark:text-amber-100"
          >
            <div class="font-bold">{{ t('app.fuzzIneligibleSpecifications', { count: run.eligibility.ineligibleSpecs.length }) }}</div>
            <ul class="mt-1 list-disc space-y-1 pl-4">
              <li v-for="(issue, index) in run.eligibility.ineligibleSpecs" :key="`${issue.specId || index}-${issue.reasonCode}`">
                <span>{{ issue.specificationLabel || issue.specId || t('app.unknownSpecification') }}: {{ eligibilityReason(issue.reasonCode) }}</span>
              </li>
            </ul>
          </div>

          <div
            v-if="run.limitations.length > 0"
            class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2 text-xs leading-5 text-slate-700 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-200"
          >
            <div class="font-bold">{{ capabilityBoundaryHeading }}</div>
            <ul class="mt-1 list-disc space-y-1 pl-4">
              <li v-for="(limitation, index) in run.limitations" :key="index">{{ limitationText(limitation) }}</li>
            </ul>
          </div>

          <section v-if="targetResults.length > 0" aria-labelledby="fuzz-target-results-title">
            <div class="flex items-center justify-between gap-3">
              <h4 id="fuzz-target-results-title" class="text-sm font-bold text-slate-800 dark:text-slate-100">{{ t('app.fuzzTargetResults') }}</h4>
              <span class="text-[11px] text-slate-500 dark:text-slate-400">{{ t('app.fuzzTargetResultsSummary', { found: run.findings.length, total: targetResults.length }) }}</span>
            </div>
            <ul class="mt-2 divide-y divide-slate-100 overflow-hidden rounded-lg border border-slate-200 dark:divide-slate-700 dark:border-slate-700">
              <li v-for="target in targetResults" :key="target.specId" class="flex items-start gap-2 bg-white px-3 py-2.5 dark:bg-slate-800">
                <span
                  class="material-symbols-outlined mt-0.5 text-base"
                  :class="target.finding ? 'text-red-600 dark:text-red-300' : 'text-sky-600 dark:text-sky-300'"
                  aria-hidden="true"
                >{{ target.finding ? 'warning' : 'search_off' }}</span>
                <div class="min-w-0 flex-1">
                  <p class="truncate text-xs font-semibold text-slate-800 dark:text-slate-100" :title="target.finding ? findingTitle(target.finding) : target.label">
                    {{ target.finding ? findingTitle(target.finding) : target.label }}
                  </p>
                  <p class="mt-0.5 text-[11px] leading-4" :class="target.finding ? 'text-red-700 dark:text-red-300' : 'text-sky-800 dark:text-sky-300'">
                    {{ target.finding ? t('app.fuzzTargetCandidateFound') : t('app.fuzzTargetNoCandidateWithinBudget') }}
                  </p>
                </div>
              </li>
            </ul>
          </section>

          <p
            data-testid="fuzz-formal-verification-current-board-notice"
            class="rounded-lg border border-indigo-200 bg-indigo-50 px-3 py-2 text-xs leading-5 text-indigo-950 dark:border-indigo-800 dark:bg-indigo-950/50 dark:text-indigo-100"
          >
            {{ t('app.fuzzFormalVerificationCurrentBoardNotice') }}
          </p>

          <section aria-labelledby="fuzz-findings-title">
            <div class="flex items-center justify-between gap-3">
              <h4 id="fuzz-findings-title" class="text-sm font-bold text-slate-800 dark:text-slate-100">{{ t('app.fuzzFindings') }}</h4>
              <span class="rounded-full bg-slate-100 px-2 py-0.5 text-xs font-semibold text-slate-600 dark:bg-slate-700 dark:text-slate-200">{{ run.findings.length }}</span>
            </div>

            <div v-if="run.findings.length === 0" class="mt-2 rounded-lg border border-slate-200 bg-slate-50 px-3 py-6 text-center text-xs leading-5 text-slate-600 dark:border-slate-700 dark:bg-slate-800 dark:text-slate-300">
              {{ run.outcome === 'BUDGET_EXHAUSTED' ? t('app.fuzzNoViolationWithinBudget') : t('app.fuzzNoReplayableFindings') }}
            </div>

            <div v-else class="mt-2 divide-y divide-slate-100 overflow-hidden rounded-lg border border-slate-200 dark:divide-slate-700 dark:border-slate-700">
              <article v-for="finding in run.findings" :key="finding.id" class="bg-white p-3 dark:bg-slate-800">
                <div class="flex flex-wrap items-start justify-between gap-3">
                  <div class="min-w-0 flex-1">
                    <p class="truncate text-xs font-bold text-slate-800 dark:text-slate-100" :title="findingTitle(finding)">{{ findingTitle(finding) }}</p>
                    <p class="mt-1 text-[11px] text-slate-500 dark:text-slate-400">{{ t('app.fuzzFindingMeta', { step: displayStep(finding.firstViolationStep), seed: finding.seed }) }}</p>
                  </div>
                  <div class="flex shrink-0 gap-1.5">
                    <button
                      type="button"
                      :data-testid="`replay-fuzzing-finding-${finding.id}`"
                      class="inline-flex min-h-11 items-center gap-1 rounded-md bg-indigo-600 px-2.5 py-1.5 text-[11px] font-semibold text-white hover:bg-indigo-700 disabled:opacity-50"
                      :disabled="actionLocked || !findingDataAvailable(finding)"
                      @click="emit('replay', finding.id)"
                    >
                      <span class="material-symbols-outlined text-sm" aria-hidden="true">play_arrow</span>{{ t('app.replay') }}
                    </button>
                    <button
                      type="button"
                      :data-testid="`verify-fuzzing-finding-${finding.id}`"
                      class="inline-flex min-h-11 items-center gap-1 rounded-md bg-emerald-100 px-2.5 py-1.5 text-[11px] font-semibold text-emerald-800 hover:bg-emerald-200 disabled:opacity-50 dark:bg-emerald-900/60 dark:text-emerald-100 dark:hover:bg-emerald-800"
                      :disabled="actionLocked || !findingDataAvailable(finding)"
                      @click="emit('verify', finding)"
                    >
                        <span class="material-symbols-outlined text-sm" aria-hidden="true">fact_check</span>{{ t('app.verifyCurrentBoard') }}
                      </button>
                  </div>
                </div>
              </article>
            </div>
          </section>

          <button
            v-if="run.findings.length === 0"
            type="button"
            data-testid="verify-current-board-without-finding"
            class="inline-flex min-h-11 w-full items-center justify-center gap-1.5 rounded-lg bg-emerald-600 px-3 py-2.5 text-sm font-bold text-white hover:bg-emerald-700 disabled:opacity-50"
            :disabled="actionLocked"
            @click="emit('verifyCurrentBoard')"
          >
            <span class="material-symbols-outlined text-base" aria-hidden="true">fact_check</span>{{ t('app.verifyCurrentBoard') }}
          </button>

          <p class="rounded-lg border border-indigo-100 bg-indigo-50 px-3 py-2 text-xs leading-5 text-indigo-900 dark:border-indigo-800 dark:bg-indigo-950/50 dark:text-indigo-100">
            {{ t('app.fuzzFindingNotFixable') }}
          </p>
        </template>
      </div>
    </section>
  </div>
</template>
