<script setup lang="ts">
import { computed, onBeforeUnmount, ref } from 'vue'
import { useI18n } from 'vue-i18n'
import type { TraceTriggeredRule } from '@/types/verify'
import type { FuzzingInputEvent } from '@/types/fuzzing'
import type {
  PlaybackChangeKind,
  PlaybackDeviceChange,
  PlaybackDeviceChangeDetail,
  PlaybackEnvironmentChange
} from '@/utils/traceView'
import { formatBuiltInModelToken } from '@/utils/modelTokenDisplay'

const props = withDefaults(defineProps<{
  changes: PlaybackDeviceChange[]
  environmentChanges: PlaybackEnvironmentChange[]
  triggeredRules: TraceTriggeredRule[]
  compromisedAutomationLinks: TraceTriggeredRule[]
  animatedEdgeCount: number
  compromisedEdgeCount: number
  stateNumber: number
  totalStates: number
  kind: 'simulation' | 'counterexample' | 'fuzzing'
  position: { x: number; y: number }
  inputEvents?: Array<FuzzingInputEvent & { targetLabel?: string }>
  firstViolationStateNumber?: number
  bundledDeviceIds?: string[]
  bundledEnvironmentNames?: string[]
}>(), {
  bundledDeviceIds: () => [],
  bundledEnvironmentNames: () => []
})

const emit = defineEmits<{
  dismiss: []
  move: [position: { x: number; y: number }]
}>()

const { t, te } = useI18n()
const formatBundledModelToken = (value: unknown) => formatBuiltInModelToken(
  value,
  key => te(key) ? t(key) : key
)
const bundledDeviceIdSet = computed(() => new Set(props.bundledDeviceIds))
const bundledEnvironmentNameSet = computed(() => new Set(props.bundledEnvironmentNames))
const formatDeviceToken = (deviceId: string, value: unknown) =>
  bundledDeviceIdSet.value.has(deviceId)
    ? formatBundledModelToken(value)
    : String(value ?? '')
const formatDeviceProperty = (deviceId: string, property: unknown, stateProperty = false) =>
  (stateProperty && property === 'workingState') || bundledDeviceIdSet.value.has(deviceId)
    ? formatBundledModelToken(property)
    : String(property ?? '')
const formatEnvironmentToken = (name: string, value: unknown) =>
  bundledEnvironmentNameSet.value.has(name)
    ? formatBundledModelToken(value)
    : String(value ?? '')

const title = computed(() => {
  if (props.kind === 'simulation') return t('app.traceVisualization.simulationStepChanges')
  if (props.kind === 'fuzzing') return t('app.traceVisualization.fuzzingStepChanges')
  return t('app.traceVisualization.counterexampleStepChanges')
})

const isInitialState = computed(() => props.stateNumber <= 1)
const isFirstViolationState = computed(() =>
  props.kind === 'fuzzing' && props.firstViolationStateNumber === props.stateNumber)
const hasObservableChanges = computed(() =>
  props.changes.length > 0 || props.environmentChanges.length > 0)
const playbackSummary = computed(() => {
  if (isInitialState.value) {
    return t('app.traceVisualization.playbackInitialStateSummary')
  }
  const counts = {
    devices: props.changes.length,
    environment: props.environmentChanges.length,
    rules: props.triggeredRules.length
  }
  return props.triggeredRules.length > 0
    ? t('app.traceVisualization.playbackChangesSummaryWithRules', counts)
    : t('app.traceVisualization.playbackChangesSummaryWithoutRules', counts)
})

const ruleLabel = (rule: TraceTriggeredRule, index: number): string =>
  rule.ruleLabel?.trim() || t('app.ruleNumber', { number: index + 1 })

const inputEventKindLabel = (event: FuzzingInputEvent) => {
  if (event.kind === 'DEVICE_STATE') return t('app.traceVisualization.fuzzDeviceStateInput')
  if (event.kind === 'DEVICE_VARIABLE') return t('app.traceVisualization.fuzzDeviceInput')
  if (event.kind === 'ENVIRONMENT_RATE') return t('app.traceVisualization.fuzzEnvironmentRateInput')
  return t('app.traceVisualization.fuzzEnvironmentInput')
}

const inputEventSourceLabel = (event: FuzzingInputEvent) => {
  if (event.source === 'RANDOM_INITIAL_STATE') return t('app.traceVisualization.fuzzRandomInitialSource')
  if (event.source === 'SEED_EVENT') return t('app.traceVisualization.fuzzSeedEventSource')
  return t('app.traceVisualization.fuzzModelChoiceSource')
}

const inputEventValue = (event: FuzzingInputEvent) => {
  const value = event.kind === 'ENVIRONMENT_RATE' && event.value.startsWith('rate:')
    ? event.value.slice(5)
    : event.value
  return event.kind === 'DEVICE_STATE' || event.kind === 'DEVICE_VARIABLE'
    ? formatDeviceToken(event.targetId, value)
    : formatEnvironmentToken(event.property, value)
}

const inputEventProperty = (event: FuzzingInputEvent) =>
  event.kind === 'DEVICE_STATE' || event.kind === 'DEVICE_VARIABLE'
    ? formatDeviceProperty(event.targetId, event.property, event.kind === 'DEVICE_STATE')
    : formatEnvironmentToken(event.property, event.property)

const popoverRef = ref<HTMLElement | null>(null)
let dragState: {
  pointerId: number
  startX: number
  startY: number
  startPosition: { x: number; y: number }
  minDeltaX: number
  maxDeltaX: number
  minDeltaY: number
  maxDeltaY: number
} | null = null

const beginDrag = (clientX: number, clientY: number, pointerId: number, target?: HTMLElement) => {
  if (!popoverRef.value) return
  const rect = popoverRef.value.getBoundingClientRect()
  const viewportInset = 8
  dragState = {
    pointerId,
    startX: clientX,
    startY: clientY,
    startPosition: { ...props.position },
    minDeltaX: viewportInset - rect.left,
    maxDeltaX: window.innerWidth - viewportInset - rect.right,
    minDeltaY: viewportInset - rect.top,
    maxDeltaY: window.innerHeight - viewportInset - rect.bottom
  }
  if (pointerId >= 0) target?.setPointerCapture?.(pointerId)
}

const updateDrag = (clientX: number, clientY: number) => {
  if (!dragState) return
  const deltaX = Math.min(
    dragState.maxDeltaX,
    Math.max(dragState.minDeltaX, clientX - dragState.startX)
  )
  const deltaY = Math.min(
    dragState.maxDeltaY,
    Math.max(dragState.minDeltaY, clientY - dragState.startY)
  )
  emit('move', {
    x: Math.round(dragState.startPosition.x + deltaX),
    y: Math.round(dragState.startPosition.y + deltaY)
  })
}

const finishDrag = (pointerId: number, target?: HTMLElement) => {
  if (!dragState || dragState.pointerId !== pointerId) return
  if (pointerId >= 0) target?.releasePointerCapture?.(pointerId)
  dragState = null
  window.removeEventListener('mousemove', onMouseMove)
  window.removeEventListener('mouseup', onMouseUp)
}

const onDragStart = (event: PointerEvent) => {
  if (!event.pointerType || event.pointerType === 'mouse') return
  if (event.button !== 0 || event.isPrimary === false || dragState) return
  beginDrag(event.clientX, event.clientY, event.pointerId, event.currentTarget as HTMLElement)
}

const onDragMove = (event: PointerEvent) => {
  if (!dragState || event.pointerId !== dragState.pointerId) return
  event.preventDefault()
  updateDrag(event.clientX, event.clientY)
}

const onDragEnd = (event: PointerEvent) => {
  finishDrag(event.pointerId, event.currentTarget as HTMLElement)
}

const onMouseMove = (event: MouseEvent) => {
  if (!dragState || dragState.pointerId !== -1) return
  event.preventDefault()
  updateDrag(event.clientX, event.clientY)
}

const onMouseUp = () => {
  finishDrag(-1)
}

const onMouseDragStart = (event: MouseEvent) => {
  if (event.button !== 0 || dragState) return
  beginDrag(event.clientX, event.clientY, -1)
  window.addEventListener('mousemove', onMouseMove)
  window.addEventListener('mouseup', onMouseUp)
}

onBeforeUnmount(() => {
  window.removeEventListener('mousemove', onMouseMove)
  window.removeEventListener('mouseup', onMouseUp)
})

const detailLabel = (detail: PlaybackDeviceChangeDetail, deviceId: string): string => {
  const labels: Record<PlaybackChangeKind, string> = {
    state: t('app.state'),
    mode: t('app.mode'),
    variable: detail.name ? formatDeviceToken(deviceId, detail.name) : t('app.variableValue'),
    security: t('app.traceVisualization.securityLabels'),
    compromised: t('app.traceVisualization.compromiseStatus')
  }
  return labels[detail.kind]
}

const formatValue = (value: string, kind: PlaybackChangeKind, deviceId: string): string => {
  if (kind === 'compromised') {
    return value === 'true'
      ? t('app.traceVisualization.compromised')
      : t('app.traceVisualization.notCompromised')
  }
  if (kind !== 'security') return formatDeviceToken(deviceId, value)
  return [
    ['untrusted', t('app.untrusted')],
    ['trusted', t('app.trusted')],
    ['private', t('app.private')],
    ['public', t('app.public')],
    ['trust=', `${t('app.trust')}=`],
    ['privacy=', `${t('app.privacy')}=`]
  ].reduce((result, [source, target]) => result.split(source).join(target), value)
}
</script>

<template>
  <aside
    ref="popoverRef"
    class="board-playback-change-popover"
    data-testid="playback-change-popover"
    role="region"
    :aria-label="title"
    :style="{ transform: `translate3d(${position.x}px, ${position.y}px, 0)` }"
  >
    <header
      class="playback-change-popover__header flex items-start justify-between gap-3 border-b px-3 py-2"
      data-testid="playback-change-drag-handle"
      :title="t('app.traceVisualization.moveChangesPanel')"
      @pointerdown="onDragStart"
      @pointermove="onDragMove"
      @pointerup="onDragEnd"
      @pointercancel="onDragEnd"
      @mousedown="onMouseDragStart"
    >
      <div class="min-w-0">
        <div class="flex items-center gap-1.5 text-xs font-bold text-indigo-950">
          <span class="material-symbols-outlined text-base text-indigo-600" aria-hidden="true">sync_alt</span>
          <span class="truncate">{{ title }}</span>
          <span class="shrink-0 rounded-full bg-indigo-100 px-1.5 py-0.5 text-[10px] font-bold text-indigo-700">
            {{ t('app.traceVisualization.stateLabel') }} {{ stateNumber }} / {{ totalStates }}
          </span>
          <span
            v-if="isFirstViolationState"
            class="shrink-0 rounded-full bg-red-100 px-1.5 py-0.5 text-[10px] font-bold text-red-700"
            data-testid="fuzzing-first-violation-badge"
          >
            {{ t('app.fuzzFirstViolation') }}
          </span>
        </div>
        <p class="mt-0.5 text-[10px] leading-4 text-slate-500" aria-live="polite" aria-atomic="true">
          {{ playbackSummary }}
        </p>
      </div>
      <button
        type="button"
        data-testid="playback-change-dismiss"
        class="inline-flex h-7 w-7 shrink-0 items-center justify-center rounded-md text-slate-500 transition-colors hover:bg-indigo-50 hover:text-indigo-800"
        :aria-label="t('app.traceVisualization.dismissChanges')"
        :title="t('app.traceVisualization.dismissChanges')"
        @pointerdown.stop
        @mousedown.stop
        @click="emit('dismiss')"
      >
        <span class="material-symbols-outlined text-base" aria-hidden="true">close</span>
      </button>
    </header>

    <Transition name="playback-change-step" mode="out-in">
      <div
        :key="`${kind}-${stateNumber}`"
        class="playback-change-popover__body max-h-[15rem] space-y-1.5 overflow-y-auto px-3 py-2"
      >
        <article
          v-if="kind === 'fuzzing'"
          class="rounded-lg border border-indigo-200 bg-indigo-50 px-2.5 py-2"
          data-testid="playback-change-fuzz-inputs"
        >
          <div class="flex items-center gap-1.5 text-[11px] font-bold text-indigo-900">
            <span class="material-symbols-outlined text-sm text-indigo-700" aria-hidden="true">input</span>
            <span>{{ t('app.traceVisualization.fuzzInputsInThisStep') }}</span>
          </div>
          <ul v-if="inputEvents?.length" class="mt-1.5 space-y-1">
            <li
              v-for="(event, index) in inputEvents"
              :key="`${event.kind}-${event.targetId}-${event.property}-${index}`"
              class="rounded-md border border-indigo-100 bg-white px-2 py-1.5 text-[10px] leading-4 text-indigo-950"
            >
              <span class="mr-1 inline-flex rounded bg-indigo-100 px-1.5 py-0.5 font-bold text-indigo-800">{{ inputEventSourceLabel(event) }}</span>
              <span class="font-semibold">{{ inputEventKindLabel(event) }}</span>
              <span class="px-1 text-indigo-400" aria-hidden="true">·</span>
              <span>{{ event.targetLabel || event.targetId }}.{{ inputEventProperty(event) }}</span>
              <span class="px-1 font-bold text-indigo-500" aria-hidden="true">=</span>
              <span class="break-all font-mono font-semibold">{{ inputEventValue(event) }}</span>
            </li>
          </ul>
          <p v-else class="mt-1 text-[10px] leading-4 text-indigo-800">
            {{ t('app.traceVisualization.noFuzzInputInThisStep') }}
          </p>
        </article>

        <div
          v-if="isInitialState"
          class="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-[10px] leading-4 text-slate-600"
          data-testid="playback-change-initial-state"
        >
          {{ t('app.traceVisualization.playbackInitialStateNoPrevious') }}
        </div>

        <div
          v-else-if="!hasObservableChanges"
          class="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-[10px] leading-4 text-slate-600"
          data-testid="playback-change-empty"
        >
          {{ t('app.traceVisualization.playbackNoObservableChanges') }}
        </div>

        <div
          v-if="kind === 'fuzzing' && !isInitialState"
          class="pt-0.5 text-[10px] font-bold uppercase text-slate-500"
        >
          {{ t('app.traceVisualization.fuzzObservedModelChanges') }}
        </div>

        <article
          v-for="change in changes"
          :key="change.deviceId"
          class="playback-change-popover__device rounded-lg border px-2.5 py-2"
          :data-testid="`playback-change-device-${change.deviceId}`"
        >
          <div class="flex items-center justify-between gap-2">
            <div class="flex min-w-0 items-center gap-1.5 text-[11px] font-bold text-indigo-950">
              <span class="material-symbols-outlined text-sm text-indigo-600" aria-hidden="true">devices</span>
              <span class="truncate">{{ change.deviceLabel || t('app.unknown') }}</span>
            </div>
            <span class="shrink-0 text-[10px] font-semibold text-indigo-600">
              {{ change.details.length }} {{ t('app.traceVisualization.changeCountSuffix') }}
            </span>
          </div>
          <ul class="mt-1.5 space-y-1">
            <li
              v-for="(detail, index) in change.details"
              :key="`${detail.kind}-${detail.name || ''}-${index}`"
              class="grid grid-cols-[minmax(4.5rem,auto)_minmax(0,1fr)] items-baseline gap-2 text-[10px] leading-4"
            >
              <span class="truncate font-semibold text-slate-600" :title="detailLabel(detail, change.deviceId)">{{ detailLabel(detail, change.deviceId) }}</span>
              <span class="min-w-0 break-words font-mono text-slate-800">
                <span class="text-slate-500">{{ formatValue(detail.previousValue, detail.kind, change.deviceId) }}</span>
                <span class="px-1 font-sans font-bold text-indigo-500" aria-hidden="true">-&gt;</span>
                <span class="font-semibold text-indigo-900">{{ formatValue(detail.currentValue, detail.kind, change.deviceId) }}</span>
              </span>
            </li>
          </ul>
        </article>

        <article
          v-if="environmentChanges.length > 0"
          class="playback-change-popover__environment rounded-lg border px-2.5 py-2"
          data-testid="playback-change-environment"
        >
          <div class="flex items-center justify-between gap-2">
            <div class="flex min-w-0 items-center gap-1.5 text-[11px] font-bold text-amber-950">
              <span class="material-symbols-outlined text-sm text-amber-600" aria-hidden="true">terrain</span>
              <span>{{ t('app.traceVisualization.environmentChanges') }}</span>
            </div>
            <span class="shrink-0 text-[10px] font-semibold text-amber-700">
              {{ environmentChanges.length }} {{ t('app.traceVisualization.changeCountSuffix') }}
            </span>
          </div>
          <ul class="mt-1.5 space-y-1">
            <li
              v-for="change in environmentChanges"
              :key="change.name"
              class="grid grid-cols-[minmax(4.5rem,auto)_minmax(0,1fr)] items-baseline gap-2 text-[10px] leading-4"
            >
              <span class="truncate font-semibold text-slate-600" :title="formatEnvironmentToken(change.name, change.name)">{{ formatEnvironmentToken(change.name, change.name) }}</span>
              <span class="min-w-0 break-words font-mono text-slate-800">
                <span class="text-slate-500">{{ formatEnvironmentToken(change.name, change.previousValue) }}</span>
                <span class="px-1 font-sans font-bold text-amber-500" aria-hidden="true">-&gt;</span>
                <span class="font-semibold text-amber-900">{{ formatEnvironmentToken(change.name, change.currentValue) }}</span>
              </span>
            </li>
          </ul>
        </article>

        <article
          v-if="triggeredRules.length > 0"
          class="playback-change-popover__automation rounded-lg border px-2.5 py-2"
          data-testid="playback-change-automation"
        >
          <div class="flex items-center gap-1.5 text-[11px] font-bold text-slate-800">
            <span class="material-symbols-outlined text-sm text-emerald-600" aria-hidden="true">account_tree</span>
            <span>{{ t('app.traceVisualization.automationInThisStep') }}</span>
          </div>
          <div class="mt-1.5 flex flex-wrap gap-1">
            <span
              v-for="(rule, index) in triggeredRules"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="max-w-full truncate rounded-full border border-emerald-200 bg-emerald-50 px-2 py-1 text-[10px] font-semibold text-emerald-800"
              :title="ruleLabel(rule, index)"
            >
              {{ ruleLabel(rule, index) }}
            </span>
          </div>
          <p class="mt-1.5 text-[10px] leading-4 text-slate-600">
            {{ animatedEdgeCount > 0
              ? t('app.traceVisualization.playbackAnimatedEdges', { count: animatedEdgeCount })
              : t('app.traceVisualization.playbackTriggeredRuleWithoutCurrentEdge') }}
          </p>
        </article>

        <article
          v-if="compromisedAutomationLinks.length > 0"
          class="rounded-lg border border-red-200 bg-red-50 px-2.5 py-2"
          data-testid="playback-change-compromised-links"
        >
          <div class="flex items-center gap-1.5 text-[11px] font-bold text-red-800">
            <span class="material-symbols-outlined text-sm" aria-hidden="true">link_off</span>
            <span>{{ t('app.traceVisualization.compromisedAutomationLinks') }}</span>
          </div>
          <div class="mt-1.5 flex flex-wrap gap-1">
            <span
              v-for="(rule, index) in compromisedAutomationLinks"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="max-w-full truncate rounded-full border border-red-200 bg-white px-2 py-1 text-[10px] font-semibold text-red-700"
              :title="ruleLabel(rule, index)"
            >
              {{ ruleLabel(rule, index) }}
            </span>
          </div>
          <p class="mt-1.5 text-[10px] leading-4 text-red-700">
            {{ t('app.traceVisualization.playbackCompromisedEdgesStatic', { count: compromisedEdgeCount }) }}
          </p>
        </article>
      </div>
    </Transition>
  </aside>
</template>
