<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, onMounted, ref } from 'vue'
import { useI18n } from 'vue-i18n'
import type { Specification } from '@/types/spec'
import type {
  FuzzingExplorationMode,
  FuzzPaperDomainPreview,
  FuzzingTaskSummary
} from '@/types/fuzzing'
import { isValidFuzzPaperDomainFingerprint } from '@/types/fuzzing'
import { formatTraceSpec } from '@/utils/traceView'
import {
  FUZZ_ITERATIONS_MAX,
  FUZZ_ITERATIONS_MIN,
  FUZZ_PATH_LENGTH_MAX,
  FUZZ_PATH_LENGTH_MIN,
  FUZZ_POPULATION_MAX,
  FUZZ_POPULATION_MIN,
  FUZZ_TARGET_SPEC_MAX,
  getKnownFuzzingSpecificationIssue,
  isKnownFuzzingSpecificationSupported
} from '@/utils/fuzzingConfig'
import { fuzzingLimitationKey } from '@/utils/fuzzingPresentation'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'
import { normalizeNuSmvDeviceName } from '@/utils/modelRequest'

export type FuzzingPanelForm = {
  explorationMode: FuzzingExplorationMode
  targetSelectionMode?: 'ALL' | 'EXPLICIT'
  targetSpecIds: string[]
  maxIterations: number
  pathLength: number
  populationSize: number
  seed: number | null
}

const props = withDefaults(defineProps<{
  form: FuzzingPanelForm
  specifications: Specification[]
  running: boolean
  progress: number
  status: string
  taskId: number | null
  cancelling: boolean
  error?: string | null
  configurationError?: string
  workload?: number
  workloadLimit?: number
  workloadReady?: boolean
  workloadLoading?: boolean
  workloadError?: string | null
  paperDomainPreview?: FuzzPaperDomainPreview | null
  paperDomainLoading?: boolean
  paperDomainError?: string | null
  bundledDeviceIds?: string[]
  bundledEnvironmentNames?: string[]
  notice?: string | null
  preflightBlocked?: boolean
  preflightMessage?: string | null
  frozenTask?: FuzzingTaskSummary | null
}>(), {
  workloadReady: true,
  bundledDeviceIds: () => [],
  bundledEnvironmentNames: () => []
})

const emit = defineEmits<{
  submit: []
  cancel: []
  close: []
  refreshPaperDomain: []
  refreshWorkload: []
}>()

const { t, te, locale } = useI18n()
const formatBundledModelToken = (value: unknown) => formatBuiltInModelToken(
  value,
  key => te(key) ? t(key) : key
)
const bundledDeviceIdSet = computed(() => new Set(
  props.bundledDeviceIds.map(normalizeNuSmvDeviceName)
))
const bundledEnvironmentNameSet = computed(() => new Set(props.bundledEnvironmentNames))
const isBundledDevice = (targetId: string) => bundledDeviceIdSet.value.has(
  normalizeNuSmvDeviceName(targetId)
)
const formatDeviceStateProperty = (targetId: string, property: unknown) =>
  property === 'workingState' || isBundledDevice(targetId)
    ? formatBundledModelToken(property)
    : String(property ?? '')
const formatDeviceVariableProperty = (targetId: string, property: unknown) =>
  isBundledDevice(targetId) ? formatBundledModelToken(property) : String(property ?? '')
const formatDeviceValue = (targetId: string, value: unknown) =>
  isBundledDevice(targetId) ? formatBundledModelToken(value) : String(value ?? '')
const formatEnvironmentToken = (name: string, value: unknown) =>
  bundledEnvironmentNameSet.value.has(name)
    ? formatBundledModelToken(value)
    : String(value ?? '')

const formatNumber = (value: number) => value.toLocaleString(
  locale.value.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US'
)

const closeButtonRef = ref<HTMLButtonElement | null>(null)
const previouslyFocused = typeof document !== 'undefined' && document.activeElement instanceof HTMLElement
  ? document.activeElement
  : null

const closePanel = () => emit('close')

const updateSeed = (event: Event) => {
  const input = event.target as HTMLInputElement
  props.form.seed = input.value === '' ? null : input.valueAsNumber
}

onMounted(() => {
  void nextTick(() => closeButtonRef.value?.focus())
})

onBeforeUnmount(() => {
  const fallback = document.querySelector<HTMLElement>('[data-testid="open-fuzzing-panel"]')
  const target = previouslyFocused?.isConnected ? previouslyFocused : fallback
  target?.focus()
})

const eligibleSpecifications = computed(() =>
  props.specifications.filter(isKnownFuzzingSpecificationSupported))
const eligibleIds = computed(() => new Set(eligibleSpecifications.value.map(spec => spec.id)))
const normalizedSelectedIds = computed(() =>
  props.form.targetSpecIds.filter(id => eligibleIds.value.has(id)))
const invalidSelectedIds = computed(() =>
  props.form.targetSpecIds.filter(id => !eligibleIds.value.has(id)))
const targetSelectionMode = computed(() => props.form.targetSelectionMode
  ?? (props.form.targetSpecIds.length > 0 ? 'EXPLICIT' : 'ALL'))
const preflightBlocked = computed(() => props.preflightBlocked === true)

const implicitAll = computed(() =>
  eligibleSpecifications.value.length > 0 &&
  eligibleSpecifications.value.length <= FUZZ_TARGET_SPEC_MAX &&
  targetSelectionMode.value === 'ALL'
)

const selectedAll = computed(() =>
  implicitAll.value || (
    eligibleSpecifications.value.length > 0 &&
    normalizedSelectedIds.value.length === eligibleSpecifications.value.length &&
    eligibleSpecifications.value.every(spec => normalizedSelectedIds.value.includes(spec.id))
  )
)

const selectedEligibleCount = computed(() =>
  implicitAll.value ? eligibleSpecifications.value.length : normalizedSelectedIds.value.length)

const explorationModeDescription = computed(() => t(
  props.form.explorationMode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzModePaperDescription'
    : 'app.fuzzModeBoardDescription'
))

const paperDomainReady = computed(() =>
  props.form.explorationMode !== 'PAPER_COMPATIBLE' || (
    !props.paperDomainLoading &&
    !props.paperDomainError &&
    props.paperDomainPreview?.pathLength === props.form.pathLength &&
    isValidFuzzPaperDomainFingerprint(props.paperDomainPreview?.modelFingerprint)
  ))

const selectExplorationMode = (mode: FuzzingExplorationMode) => {
  if (!props.running) props.form.explorationMode = mode
}

const toggleAll = () => {
  if (props.running || preflightBlocked.value || implicitAll.value) return
  props.form.targetSelectionMode = 'ALL'
  props.form.targetSpecIds = []
}

const toggleSpec = (id: string, checked: boolean) => {
  if (preflightBlocked.value || !eligibleIds.value.has(id)) return
  const selected = new Set(normalizedSelectedIds.value)
  if (implicitAll.value) {
    if (checked) return
    eligibleSpecifications.value.forEach(spec => selected.add(spec.id))
    selected.delete(id)
  } else if (checked) {
    selected.add(id)
  } else {
    if (selected.size <= 1) return
    selected.delete(id)
  }
  const next = eligibleSpecifications.value.filter(spec => selected.has(spec.id)).map(spec => spec.id)
  if (next.length === eligibleSpecifications.value.length) {
    props.form.targetSelectionMode = 'ALL'
    props.form.targetSpecIds = []
  } else {
    props.form.targetSelectionMode = 'EXPLICIT'
    props.form.targetSpecIds = [...next, ...invalidSelectedIds.value]
  }
}

const resolveInvalidTargets = () => {
  if (props.running || invalidSelectedIds.value.length === 0) return
  if (normalizedSelectedIds.value.length > 0) {
    props.form.targetSelectionMode = 'EXPLICIT'
    props.form.targetSpecIds = [...normalizedSelectedIds.value]
  } else {
    props.form.targetSelectionMode = 'ALL'
    props.form.targetSpecIds = []
  }
}

const isSpecChecked = (id: string) =>
  eligibleIds.value.has(id) && (implicitAll.value || normalizedSelectedIds.value.includes(id))

const isOnlySelectedSpec = (id: string) =>
  (implicitAll.value && eligibleSpecifications.value.length === 1 && eligibleSpecifications.value[0]?.id === id) ||
  (!implicitAll.value && normalizedSelectedIds.value.length === 1 && normalizedSelectedIds.value[0] === id)

const isSpecEligible = (spec: Specification) => eligibleIds.value.has(spec.id)

const specIneligibilityMessageKey = (spec: Specification) =>
  getKnownFuzzingSpecificationIssue(spec) === 'TRUST_PRIVACY_UNSUPPORTED'
    ? 'app.fuzzEligibilityTrustPrivacyUnsupported'
    : 'app.fuzzEligibilityUnsupportedTemplate'

const onSpecChange = (id: string, event: Event) => {
  toggleSpec(id, (event.target as HTMLInputElement).checked)
}

const specTitle = (spec: Specification) =>
  formatTraceSpec(spec, t) || spec.templateLabel || spec.formula || t('app.unknownSpecification')

const formatDomainValues = (
  values: string[],
  stripRatePrefix = false,
  formatter: (value: unknown) => string = value => String(value ?? '')
) => values
  .map(value => stripRatePrefix && value.startsWith('rate:') ? value.slice(5) : value)
  .map(formatter)
  .join(', ')

const formatDomain = (
  values: string[],
  lower?: number | null,
  upper?: number | null,
  stripRatePrefix = false,
  formatter?: (value: unknown) => string
) => Number.isSafeInteger(lower) && Number.isSafeInteger(upper)
  ? `${lower}..${upper}`
  : formatDomainValues(values, stripRatePrefix, formatter)

const frozenModeLabel = computed(() => t(
  props.frozenTask?.explorationMode === 'PAPER_COMPATIBLE'
    ? 'app.fuzzModePaper'
    : 'app.fuzzModeBoard'
))

const frozenTargetScope = computed(() => {
  const task = props.frozenTask
  if (!task) return ''
  return task.targetSpecIds.length > 0
    ? t('app.fuzzReproductionSelectedTargets', { count: task.targetSpecIds.length })
    : t('app.fuzzReproductionAllTargets', {
      count: task.modelSnapshot.specificationCount
    })
})
</script>

<template>
  <section
    data-testid="fuzzing-panel"
    class="board-floating-panel fuzzing-panel board-surface-panel fixed top-20 z-30 flex w-[30rem] max-w-[calc(100vw-2rem)] flex-col overflow-hidden rounded-lg border shadow-2xl"
    role="dialog"
    aria-labelledby="fuzzing-panel-title"
    tabindex="-1"
    @keydown.esc.stop.prevent="closePanel"
  >
    <header class="flex items-start justify-between gap-3 border-b border-indigo-100 bg-indigo-50 px-4 py-3">
      <div class="flex min-w-0 items-start gap-3">
        <div class="flex h-10 w-10 shrink-0 items-center justify-center rounded-lg bg-indigo-600 text-white shadow-sm">
          <span class="material-symbols-outlined" aria-hidden="true">radar</span>
        </div>
        <div class="min-w-0">
          <h3 id="fuzzing-panel-title" class="text-base font-bold text-indigo-950">{{ t('app.fuzzSearch') }}</h3>
          <p class="mt-0.5 text-xs leading-5 text-indigo-800/80">{{ t('app.fuzzSearchSubtitle') }}</p>
        </div>
      </div>
      <button
        ref="closeButtonRef"
        type="button"
        data-testid="close-fuzzing-panel"
        class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-md text-indigo-700 hover:bg-indigo-100"
        :title="t('app.close')"
        :aria-label="t('app.close')"
        @click="closePanel"
      >
        <span class="material-symbols-outlined" aria-hidden="true">close</span>
      </button>
    </header>

    <div class="min-h-0 flex-1 space-y-3 overflow-y-auto p-4">
      <section
        v-if="frozenTask"
        data-testid="fuzz-frozen-task-summary"
        class="rounded-lg border border-indigo-200 bg-indigo-50 px-3 py-3 text-[11px] leading-4 text-indigo-950"
        aria-labelledby="fuzz-frozen-task-title"
      >
        <h4 id="fuzz-frozen-task-title" class="text-xs font-bold">
          {{ t('app.fuzzWatchingFrozenTask', { id: frozenTask.id }) }}
        </h4>
        <p class="mt-1 text-indigo-900">{{ t('app.fuzzWatchingFrozenTaskDetail') }}</p>
        <dl class="mt-3 grid grid-cols-2 gap-x-4 gap-y-2 sm:grid-cols-3">
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzExplorationMode') }}</dt>
            <dd class="mt-0.5 font-bold text-indigo-950">{{ frozenModeLabel }}</dd>
          </div>
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzMaxIterations') }}</dt>
            <dd class="mt-0.5 font-bold text-indigo-950">{{ frozenTask.maxIterations }}</dd>
          </div>
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzPathLength') }}</dt>
            <dd class="mt-0.5 font-bold text-indigo-950">{{ frozenTask.pathLength }}</dd>
          </div>
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzPopulationSize') }}</dt>
            <dd class="mt-0.5 font-bold text-indigo-950">{{ frozenTask.populationSize }}</dd>
          </div>
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzSeed') }}</dt>
            <dd class="mt-0.5 break-all font-mono font-bold text-indigo-950">
              {{ frozenTask.seed ?? t('app.fuzzSeedAuto') }}
            </dd>
          </div>
          <div>
            <dt class="text-indigo-700">{{ t('app.fuzzTargetSpecifications') }}</dt>
            <dd class="mt-0.5 font-bold text-indigo-950">{{ frozenTargetScope }}</dd>
          </div>
        </dl>
        <p class="mt-2 text-[10px] leading-4 text-indigo-800">
          {{ t('app.fuzzFrozenTaskSnapshotSummary', {
            devices: frozenTask.modelSnapshot.deviceCount,
            rules: frozenTask.modelSnapshot.ruleCount,
            specs: frozenTask.modelSnapshot.specificationCount,
            variables: frozenTask.modelSnapshot.environmentVariableCount,
            templates: frozenTask.modelSnapshot.deviceTemplateCount
          }) }}
        </p>
      </section>

      <fieldset v-if="!frozenTask" class="min-w-0" :disabled="running">
        <legend class="text-xs font-bold uppercase tracking-wide text-slate-600">
          {{ t('app.fuzzExplorationMode') }}
        </legend>
        <div
          class="mt-1 grid grid-cols-2 gap-1 rounded-lg bg-slate-100 p-1"
          role="radiogroup"
          :aria-label="t('app.fuzzExplorationMode')"
          aria-describedby="fuzz-exploration-mode-help"
        >
          <label
            class="flex min-h-11 min-w-0 cursor-pointer items-center justify-center rounded-md px-2 py-1.5 text-center text-[11px] font-bold leading-4 transition-colors focus-within:ring-2 focus-within:ring-indigo-500 focus-within:ring-offset-1"
            :class="form.explorationMode === 'BOARD_SNAPSHOT'
              ? 'bg-white text-indigo-800 shadow-sm'
              : 'text-slate-600 hover:text-slate-800'"
          >
            <input
              v-model="form.explorationMode"
              data-testid="fuzz-mode-board"
              class="sr-only"
              type="radio"
              name="fuzz-exploration-mode"
              value="BOARD_SNAPSHOT"
              :disabled="running"
              :aria-label="t('app.fuzzModeBoard')"
              aria-describedby="fuzz-exploration-mode-help"
              @change="selectExplorationMode('BOARD_SNAPSHOT')"
            />
            <span class="min-w-0 whitespace-normal break-words">{{ t('app.fuzzModeBoard') }}</span>
          </label>
          <label
            class="flex min-h-11 min-w-0 cursor-pointer items-center justify-center rounded-md px-2 py-1.5 text-center text-[11px] font-bold leading-4 transition-colors focus-within:ring-2 focus-within:ring-indigo-500 focus-within:ring-offset-1"
            :class="form.explorationMode === 'PAPER_COMPATIBLE'
              ? 'bg-white text-indigo-800 shadow-sm'
              : 'text-slate-600 hover:text-slate-800'"
          >
            <input
              v-model="form.explorationMode"
              data-testid="fuzz-mode-paper"
              class="sr-only"
              type="radio"
              name="fuzz-exploration-mode"
              value="PAPER_COMPATIBLE"
              :disabled="running"
              :aria-label="t('app.fuzzModePaper')"
              aria-describedby="fuzz-exploration-mode-help"
              @change="selectExplorationMode('PAPER_COMPATIBLE')"
            />
            <span class="min-w-0 whitespace-normal break-words">{{ t('app.fuzzModePaper') }}</span>
          </label>
        </div>
        <p id="fuzz-exploration-mode-help" class="mt-1.5 break-words text-[10px] leading-4 text-slate-500">
          {{ explorationModeDescription }}
        </p>
      </fieldset>

      <section
        v-if="!frozenTask && form.explorationMode === 'PAPER_COMPATIBLE' && eligibleSpecifications.length > 0"
        data-testid="paper-domain-preview"
        class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2.5"
        aria-labelledby="paper-domain-preview-title"
      >
        <div class="flex items-start justify-between gap-3">
          <div class="min-w-0">
            <h4 id="paper-domain-preview-title" class="text-xs font-bold text-amber-950">{{ t('app.fuzzPaperDomainTitle') }}</h4>
            <p class="mt-1 text-[10px] leading-4 text-amber-900">{{ t('app.fuzzPaperDomainDescription') }}</p>
          </div>
          <button
            type="button"
            class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-md text-amber-800 hover:bg-amber-100 disabled:opacity-50"
            :disabled="running || paperDomainLoading"
            :title="t('app.refresh')"
            :aria-label="t('app.refresh')"
            @click="emit('refreshPaperDomain')"
          >
            <span class="material-symbols-outlined text-base" :class="paperDomainLoading ? 'animate-spin' : ''" aria-hidden="true">refresh</span>
          </button>
        </div>

        <div v-if="paperDomainLoading" class="mt-2 flex items-center gap-2 text-[11px] text-amber-800" role="status">
          <span class="material-symbols-outlined animate-spin text-sm" aria-hidden="true">sync</span>{{ t('app.fuzzPaperDomainLoading') }}
        </div>
        <div v-else-if="paperDomainError" class="mt-2 flex items-start justify-between gap-2 rounded-md border border-red-200 bg-red-50 px-2.5 py-2 text-[11px] leading-4 text-red-800" role="alert">
          <span>{{ paperDomainError }}</span>
          <button
            type="button"
            data-testid="refresh-paper-domain"
            class="min-h-11 shrink-0 px-2 font-bold text-red-900 underline underline-offset-2 disabled:opacity-50"
            :disabled="running || paperDomainLoading"
            @click="emit('refreshPaperDomain')"
          >
            {{ t('app.retry') }}
          </button>
        </div>
        <template v-else-if="paperDomainPreview">
          <p class="mt-2 text-[10px] font-semibold leading-4 text-amber-950">
            {{ t('app.fuzzPaperDomainSummary', {
              devices: paperDomainPreview.deviceDomains.length,
              locals: paperDomainPreview.localVariableDomains.length,
              environments: paperDomainPreview.environmentDomains.length,
              length: paperDomainPreview.pathLength
            }) }}
          </p>
          <details class="mt-2 border-t border-amber-200 pt-2">
            <summary class="flex min-h-11 cursor-pointer items-center text-[11px] font-bold text-amber-950">{{ t('app.fuzzPaperInspectDomains') }}</summary>
            <div class="mt-2 space-y-2 text-[10px] leading-4 text-amber-950">
              <div v-if="paperDomainPreview.deviceDomains.length">
                <p class="font-bold">{{ t('app.fuzzPaperDeviceStateDomains') }}</p>
                <ul class="mt-1 space-y-1">
                  <li v-for="domain in paperDomainPreview.deviceDomains" :key="`${domain.targetId}-${domain.property}`" class="break-words">
                    <span class="font-semibold">{{ domain.label }}.{{ formatDeviceStateProperty(domain.targetId, domain.property) }}</span>:
                    <span class="font-mono">{{ formatDomain(
                      domain.legalValues, domain.lowerBound, domain.upperBound, false,
                      value => formatDeviceValue(domain.targetId, value)
                    ) }}</span>
                  </li>
                </ul>
              </div>
              <div
                v-if="paperDomainPreview.localVariableDomains.length"
                data-testid="paper-local-variable-domains"
              >
                <p class="font-bold">{{ t('app.fuzzPaperLocalVariableDomains') }}</p>
                <ul class="mt-1 space-y-1">
                  <li v-for="domain in paperDomainPreview.localVariableDomains" :key="`${domain.targetId}-${domain.property}`" class="break-words">
                    <span class="font-semibold">{{ domain.label }}.{{ formatDeviceVariableProperty(domain.targetId, domain.property) }}</span>:
                    <span class="font-mono">{{ formatDomain(
                      domain.legalValues, domain.lowerBound, domain.upperBound, false,
                      value => formatDeviceValue(domain.targetId, value)
                    ) }}</span>
                  </li>
                </ul>
              </div>
              <div v-if="paperDomainPreview.environmentDomains.length">
                <p class="font-bold">{{ t('app.fuzzPaperEnvironmentDomains') }}</p>
                <ul class="mt-1 space-y-1.5">
                  <li v-for="domain in paperDomainPreview.environmentDomains" :key="domain.name" class="break-words">
                    <span class="font-semibold">{{ formatEnvironmentToken(domain.name, domain.name) }}</span>:
                    {{ t('app.fuzzPaperInitialValues') }} <span class="font-mono">{{ formatDomain(
                      domain.initialValues, domain.initialLowerBound, domain.initialUpperBound, false,
                      value => formatEnvironmentToken(domain.name, value)
                    ) }}</span>;
                    {{ domain.eventValueKind === 'CHANGE_RATE' ? t('app.fuzzPaperRateEvents') : t('app.fuzzPaperDirectValueEvents') }}
                    <span class="font-mono">{{ formatDomain(
                      domain.eventValues,
                      domain.eventRateLowerBound,
                      domain.eventRateUpperBound,
                      domain.eventValueKind === 'CHANGE_RATE',
                      value => formatEnvironmentToken(domain.name, value)
                    ) }}</span>
                  </li>
                </ul>
              </div>
            </div>
          </details>
          <details class="mt-2 border-t border-amber-200 pt-2">
            <summary class="flex min-h-11 cursor-pointer items-center text-[11px] font-bold text-amber-950">{{ t('app.fuzzPaperCoverageAndBoundaries') }}</summary>
            <ul class="mt-1 list-disc space-y-1 pl-4 text-[10px] leading-4 text-amber-900">
              <li v-for="code in paperDomainPreview.paperSemanticsCodes" :key="code">{{ t(fuzzingLimitationKey(code)) }}</li>
            </ul>
          </details>
          <p class="mt-2 border-t border-amber-200 pt-2 text-[10px] font-semibold leading-4 text-amber-950">
            {{ t('app.fuzzPaperUnimplementedScope') }}
          </p>
        </template>
      </section>

      <div v-if="!frozenTask" class="rounded-lg border border-indigo-100 bg-white p-3">
        <div class="flex items-center justify-between gap-2">
          <label class="text-xs font-bold uppercase tracking-wide text-slate-600">{{ t('app.fuzzTargetSpecifications') }}</label>
          <button
            v-if="eligibleSpecifications.length <= FUZZ_TARGET_SPEC_MAX"
            type="button"
            class="min-h-11 px-2 text-[11px] font-semibold text-indigo-700 hover:text-indigo-900 disabled:opacity-50"
            :disabled="running || eligibleSpecifications.length === 0 || implicitAll"
            @click="toggleAll"
          >
            {{ selectedAll ? t('app.allSpecificationsSelected') : t('app.selectAll') }}
          </button>
        </div>
        <p class="mt-1 text-[11px] leading-4 text-slate-500">{{ t('app.fuzzTargetSpecificationsHint') }}</p>
        <p
          v-if="preflightBlocked"
          data-testid="fuzz-eligibility-blocked"
          class="mt-1 rounded-md border border-amber-300 bg-amber-50 px-2 py-1.5 text-[11px] font-semibold leading-4 text-amber-950"
          role="alert"
        >
          {{ preflightMessage || t('app.fuzzEligibilityPreflightBlocked') }}
        </p>
        <p v-else class="mt-1 text-[11px] font-semibold text-indigo-700" data-testid="fuzz-eligibility-summary">
          {{ t('app.fuzzEligibilitySummary', {
            eligible: eligibleSpecifications.length,
            total: specifications.length,
            selected: selectedEligibleCount
          }) }}
        </p>
        <div
          v-if="invalidSelectedIds.length > 0"
          data-testid="fuzz-invalid-target-selection"
          class="mt-2 rounded-md border border-amber-300 bg-amber-50 px-2.5 py-2 text-[11px] leading-4 text-amber-950"
          role="alert"
        >
          <p>{{ t('app.fuzzTargetSelectionChanged', { count: invalidSelectedIds.length }) }}</p>
          <button
            type="button"
            class="mt-1.5 min-h-11 px-2 font-bold text-amber-900 underline decoration-amber-500 underline-offset-2 hover:text-amber-700 disabled:opacity-50"
            :disabled="running"
            @click="resolveInvalidTargets"
          >
            {{ normalizedSelectedIds.length > 0
              ? t('app.fuzzRemoveUnavailableTargets')
              : t('app.fuzzSelectCurrentTargets') }}
          </button>
        </div>
        <div v-if="specifications.length === 0" class="mt-3 rounded-md border border-amber-200 bg-amber-50 px-2.5 py-2 text-xs text-amber-800">
          {{ t('app.noSpecsToFuzz') }}
        </div>
        <div v-else-if="eligibleSpecifications.length === 0" class="mt-3 rounded-md border border-amber-200 bg-amber-50 px-2.5 py-2 text-xs text-amber-900" role="alert">
          {{ t('app.noEligibleSpecsToFuzz') }}
        </div>
        <div v-else class="mt-3 space-y-1.5">
          <label
            v-for="spec in specifications"
            :key="spec.id"
            class="flex min-h-11 items-start gap-2 rounded-md border px-2 py-1.5 text-xs"
            :class="isSpecEligible(spec)
              ? 'cursor-pointer border-slate-100 hover:border-indigo-200 hover:bg-indigo-50/40'
              : 'cursor-not-allowed border-slate-200 bg-slate-50 text-slate-400'"
          >
            <input
              type="checkbox"
              class="mt-0.5 accent-indigo-600"
              :checked="isSpecChecked(spec.id)"
              :disabled="running || preflightBlocked || !isSpecEligible(spec) || isOnlySelectedSpec(spec.id)"
              :title="isOnlySelectedSpec(spec.id) ? t('app.fuzzAtLeastOneTarget') : undefined"
              @change="onSpecChange(spec.id, $event)"
            />
            <span class="min-w-0 flex-1 leading-4" :class="isSpecEligible(spec) ? 'text-slate-700' : 'text-slate-500'">
              <span class="block">{{ specTitle(spec) }}</span>
              <span v-if="!isSpecEligible(spec)" class="mt-0.5 block text-[10px] leading-4 text-slate-500">
                {{ t(specIneligibilityMessageKey(spec)) }}
              </span>
            </span>
            <span
              v-if="!isSpecEligible(spec)"
              class="shrink-0 rounded bg-slate-200 px-1.5 py-0.5 text-[9px] font-bold text-slate-600"
            >
              {{ t('app.fuzzFormalOnly') }}
            </span>
          </label>
        </div>
      </div>

      <div v-if="!frozenTask" class="grid grid-cols-2 gap-2">
        <label class="rounded-lg border border-slate-200 bg-white p-2 text-xs font-semibold text-slate-600">
          {{ t('app.fuzzMaxIterations') }}
          <input
            v-model.number="form.maxIterations"
            data-testid="fuzz-max-iterations"
            type="number"
            min="1"
            :max="FUZZ_ITERATIONS_MAX"
            step="1"
            :disabled="running"
            class="mt-1 w-full rounded-md border border-slate-200 px-2 py-1.5 text-sm font-semibold text-slate-800 outline-none focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 disabled:bg-slate-100"
          />
          <span class="mt-1 block text-[10px] font-normal text-slate-400">{{ FUZZ_ITERATIONS_MIN }}-{{ FUZZ_ITERATIONS_MAX }}</span>
        </label>
        <label class="rounded-lg border border-slate-200 bg-white p-2 text-xs font-semibold text-slate-600">
          {{ t('app.fuzzPathLength') }}
          <input
            v-model.number="form.pathLength"
            data-testid="fuzz-path-length"
            type="number"
            min="1"
            :max="FUZZ_PATH_LENGTH_MAX"
            step="1"
            :disabled="running"
            class="mt-1 w-full rounded-md border border-slate-200 px-2 py-1.5 text-sm font-semibold text-slate-800 outline-none focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 disabled:bg-slate-100"
          />
          <span class="mt-1 block text-[10px] font-normal text-slate-400">{{ FUZZ_PATH_LENGTH_MIN }}-{{ FUZZ_PATH_LENGTH_MAX }} {{ t('app.fuzzStatesPerPath') }}</span>
        </label>
      </div>

      <details v-if="!frozenTask" class="rounded-lg border border-slate-200 bg-slate-50 px-3 py-2" :open="running ? true : undefined">
        <summary class="flex min-h-11 cursor-pointer items-center justify-between text-xs font-bold text-slate-700">
          <span class="inline-flex items-center gap-1.5"><span class="material-symbols-outlined text-sm text-indigo-600" aria-hidden="true">tune</span>{{ t('app.fuzzAdvancedSettings') }}</span>
          <span class="material-symbols-outlined text-sm text-slate-400" aria-hidden="true">expand_more</span>
        </summary>
        <div class="mt-2 grid grid-cols-2 gap-2">
          <label class="text-[11px] font-semibold text-slate-600">
            {{ t('app.fuzzPopulationSize') }}
              <input
              v-model.number="form.populationSize"
              data-testid="fuzz-population-size"
              type="number"
              min="1"
              :max="FUZZ_POPULATION_MAX"
              step="1"
              :disabled="running"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-sm font-semibold text-slate-800 outline-none focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 disabled:bg-slate-100"
              />
              <span class="mt-1 block text-[10px] font-normal text-slate-400">{{ FUZZ_POPULATION_MIN }}-{{ FUZZ_POPULATION_MAX }} {{ t('app.fuzzPathsPerIteration') }}</span>
          </label>
          <label class="text-[11px] font-semibold text-slate-600">
            {{ t('app.fuzzSeed') }}
            <input
              :value="form.seed ?? ''"
              @input="updateSeed"
              data-testid="fuzz-seed"
              type="number"
              min="0"
              max="9007199254740991"
              step="1"
              :placeholder="t('app.fuzzSeedAuto')"
              :disabled="running"
              class="mt-1 w-full rounded-md border border-slate-200 bg-white px-2 py-1.5 text-sm font-semibold text-slate-800 outline-none focus:border-indigo-400 focus:ring-2 focus:ring-indigo-100 disabled:bg-slate-100"
            />
          </label>
        </div>
        <p class="mt-2 text-[10px] leading-4 text-slate-500">{{ t('app.fuzzAdvancedSettingsHint') }}</p>
      </details>

      <div v-if="error" class="rounded-lg border border-red-200 bg-red-50 px-3 py-2 text-xs leading-5 text-red-800" role="alert">
        {{ error }}
      </div>

      <div v-if="notice" class="rounded-lg border border-sky-200 bg-sky-50 px-3 py-2 text-xs leading-5 text-sky-900" role="status">
        {{ notice }}
      </div>

      <div v-if="!frozenTask && configurationError" class="rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs leading-5 text-amber-900" role="alert">
        {{ configurationError }}
      </div>

      <div
        v-if="!frozenTask && workloadLoading"
        class="flex items-center gap-2 text-[10px] leading-4 text-slate-500"
        role="status"
      >
        <span class="material-symbols-outlined animate-spin text-sm" aria-hidden="true">progress_activity</span>
        <span>{{ t('app.fuzzWorkloadLoading') }}</span>
      </div>

      <div
        v-else-if="!frozenTask && workloadError"
        class="flex items-start justify-between gap-2 rounded-lg border border-amber-200 bg-amber-50 px-3 py-2 text-xs leading-5 text-amber-900"
        role="alert"
      >
        <span>{{ workloadError }}</span>
        <button
          type="button"
          class="min-h-11 shrink-0 px-2 font-bold text-amber-950 underline underline-offset-2"
          data-testid="refresh-fuzzing-workload"
          @click="emit('refreshWorkload')"
        >
          {{ t('app.retry') }}
        </button>
      </div>

      <p v-else-if="!frozenTask && Number.isFinite(workload)" class="text-[10px] leading-4 text-slate-500">
        {{ t('app.fuzzWorkloadPreview', { workload: formatNumber(Number(workload)), limit: formatNumber(Number(workloadLimit || 0)) }) }}
      </p>

      <div v-if="running" class="rounded-lg border border-indigo-100 bg-indigo-50 px-3 py-2" aria-live="polite" aria-atomic="true">
        <div class="flex items-center justify-between gap-2 text-xs font-semibold text-indigo-900">
          <span>{{ status }}</span>
          <span>{{ progress }}%</span>
        </div>
        <div
          class="mt-1.5 h-2 overflow-hidden rounded-full bg-indigo-100"
          role="progressbar"
          :aria-label="t('app.fuzzBudgetProgress')"
          aria-valuemin="0"
          aria-valuemax="100"
          :aria-valuenow="progress"
        >
          <div class="h-full rounded-full bg-indigo-600 transition-all" :style="{ width: `${progress}%` }"></div>
        </div>
        <p class="mt-1 text-[10px] leading-4 text-indigo-800">{{ t('app.fuzzProgressNotCoverage') }}</p>
        <div class="mt-1 flex items-center justify-between text-[10px] text-indigo-700/80">
          <span>{{ taskId ? t('app.fuzzTaskId', { id: taskId }) : t('app.taskInitializing') }}</span>
          <button
            v-if="taskId"
            type="button"
            class="inline-flex min-h-11 items-center gap-1 px-2 font-semibold hover:text-indigo-950 disabled:opacity-50"
            :disabled="cancelling"
            @click="emit('cancel')"
          >
            <span class="material-symbols-outlined text-sm" aria-hidden="true">cancel</span>{{ t('app.cancel') }}
          </button>
        </div>
      </div>

      <button
        v-if="!frozenTask"
        type="button"
        data-testid="run-fuzzing"
        class="flex min-h-11 w-full items-center justify-center gap-2 rounded-lg bg-indigo-600 px-3 py-2.5 text-sm font-bold text-white shadow-sm transition hover:bg-indigo-700 disabled:cursor-not-allowed disabled:bg-indigo-300"
        :disabled="running || preflightBlocked || eligibleSpecifications.length === 0 || invalidSelectedIds.length > 0 || Boolean(configurationError) || workloadReady === false || !paperDomainReady"
        @click="emit('submit')"
      >
        <span class="material-symbols-outlined text-base" :class="running ? 'animate-spin' : ''" aria-hidden="true">{{ running ? 'sync' : 'radar' }}</span>
        {{ running ? t('app.fuzzRunning') : t('app.startFuzzSearch') }}
      </button>
    </div>
  </section>
</template>
