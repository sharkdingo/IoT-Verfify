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
import HintTooltip from '@/components/common/HintTooltip.vue'

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
  /**
   * This state closes an infinite counterexample by repeating the loop entry, so having no observable change
   * is the state's meaning rather than an absence of information. Without saying so the panel reports
   * "no observable changes" on the final step of a liveness violation, which reads as a broken animation.
   */
  isLoopBackState?: boolean
  /** 1-based state numbers of the repeating cycle, for the sentence explaining the loop. */
  loopRange?: { start: number; end: number } | null
  /**
   * The violated property is a liveness claim, so the cycle IS the violation and the sentence may say the
   * required state is never reached. False for a safety counterexample that merely ends on a cycle — NuSMV
   * reports a loop for those too, and there the fault is a single state, so that claim would be wrong.
   */
  isLivenessViolation?: boolean
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
const formatDeviceProperty = (deviceId: string, property: unknown) =>
  bundledDeviceIdSet.value.has(deviceId)
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

/**
 * What to say on the state that closes the path into a cycle.
 *
 * Two different facts, so two sentences. For a liveness property the repetition *is* the violation, so it
 * names the state that is never reached. For a safety property NuSMV may still report a loop — measured on
 * both a CTL `AX` and an LTL `G(p)` counterexample — but there the fault is a single state, so the sentence
 * stays factual about the repetition and claims nothing about what the specification requires.
 */
const loopBackSentence = computed(() => {
  const range = props.loopRange
  if (!range) return t('app.traceLoopRepeats')
  return props.isLivenessViolation
    ? t('app.traceLoopExplanation', { start: range.start, end: range.end })
    : t('app.traceLoopRepeatsDetail', { start: range.start })
})
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
    ? formatDeviceProperty(event.targetId, event.property)
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
let activeDragTarget: HTMLElement | null = null

const removeDragListeners = () => {
  window.removeEventListener('pointermove', onDragMove)
  window.removeEventListener('pointerup', onDragEnd)
  window.removeEventListener('pointercancel', onDragEnd)
  window.removeEventListener('mousemove', onMouseMove)
  window.removeEventListener('mouseup', onMouseUp)
  window.removeEventListener('resize', interruptDrag)
  window.removeEventListener('blur', interruptDrag)
  document.removeEventListener('visibilitychange', onDragVisibilityChange)
}

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
  activeDragTarget = pointerId >= 0 ? (target ?? null) : null
  if (activeDragTarget) {
    try {
      activeDragTarget.setPointerCapture?.(pointerId)
    } catch {
      // Window pointer listeners retain the fallback path when capture is unavailable.
    }
    activeDragTarget.addEventListener('lostpointercapture', onPointerCaptureLost)
  }
  if (pointerId >= 0) {
    window.addEventListener('pointermove', onDragMove)
    window.addEventListener('pointerup', onDragEnd)
    window.addEventListener('pointercancel', onDragEnd)
  }
  window.addEventListener('resize', interruptDrag)
  window.addEventListener('blur', interruptDrag)
  document.addEventListener('visibilitychange', onDragVisibilityChange)
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

const finishDrag = (pointerId: number) => {
  if (!dragState || dragState.pointerId !== pointerId) return
  const target = activeDragTarget
  dragState = null
  activeDragTarget = null
  target?.removeEventListener('lostpointercapture', onPointerCaptureLost)
  if (pointerId >= 0 && target) {
    try {
      target.releasePointerCapture?.(pointerId)
    } catch {
      // Capture may already have been released by the browser.
    }
  }
  removeDragListeners()
}

const interruptDrag = () => {
  if (dragState) finishDrag(dragState.pointerId)
}

const onPointerCaptureLost = (event: PointerEvent) => finishDrag(event.pointerId)

const onDragVisibilityChange = () => {
  if (document.hidden) interruptDrag()
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
  finishDrag(event.pointerId)
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
  interruptDrag()
  removeDragListeners()
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
      @mousedown="onMouseDragStart"
    >
      <div class="min-w-0">
        <div class="flex items-center gap-1.5 text-xs font-bold board-text-info">
          <span class="material-symbols-outlined text-base board-text-info" aria-hidden="true">sync_alt</span>
          <span class="truncate">{{ title }}</span>
          <span class="shrink-0 rounded-full board-chip-info px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-info">
            {{ t('app.traceVisualization.stateLabel') }} {{ stateNumber }} / {{ totalStates }}
          </span>
          <span
            v-if="isFirstViolationState"
            class="shrink-0 rounded-full board-chip-danger px-1.5 py-0.5 text-[length:var(--iot-font-min)] font-bold board-text-danger"
            data-testid="fuzzing-first-violation-badge"
          >
            {{ t('app.fuzzFirstViolation') }}
          </span>
        </div>
        <p class="mt-0.5 text-[length:var(--iot-font-min)] leading-4 text-slate-500" aria-live="polite" aria-atomic="true">
          {{ playbackSummary }}
        </p>
      </div>
      <HintTooltip :content="t('app.traceVisualization.dismissChanges')">
        <button
          type="button"
          data-testid="playback-change-dismiss"
          class="inline-flex h-11 w-11 shrink-0 items-center justify-center rounded-md text-slate-500 transition-colors hover:board-chip-info hover:board-text-info"
          :aria-label="t('app.traceVisualization.dismissChanges')"
          @pointerdown.stop
          @mousedown.stop
          @click="emit('dismiss')"
        >
          <span class="material-symbols-outlined text-base" aria-hidden="true">close</span>
        </button>
      </HintTooltip>
    </header>

    <Transition name="playback-change-step" mode="out-in">
      <!-- The body's height derives from the popover's own cap rather than a fixed `15rem`. At 15rem
           (240px) it exceeded the outer `max-height: min(34dvh, 20rem)` on a short viewport — 227px at
           667px tall — and the outer `overflow: hidden` would then have clipped content the body's own
           scrollbar could not reach. Subtracting the header keeps the two in step whichever term binds. -->
      <div
        :key="`${kind}-${stateNumber}`"
        class="iot-scroll-region playback-change-popover__body space-y-1.5 px-3 py-2"
        :style="{ maxHeight: 'calc(min(34dvh, 20rem) - 3.25rem)' }"
      >
        <article
          v-if="kind === 'fuzzing'"
          class="rounded-lg board-surface-info px-2.5 py-2"
          data-testid="playback-change-fuzz-inputs"
        >
          <div class="flex items-center gap-1.5 text-[11px] font-bold board-text-info">
            <span class="material-symbols-outlined text-sm board-text-info" aria-hidden="true">input</span>
            <span>{{ t('app.traceVisualization.fuzzInputsInThisStep') }}</span>
          </div>
          <ul v-if="inputEvents?.length" class="mt-1.5 space-y-1">
            <li
              v-for="(event, index) in inputEvents"
              :key="`${event.kind}-${event.targetId}-${event.property}-${index}`"
              class="rounded-md border board-border-subtle bg-white px-2 py-1.5 text-[length:var(--iot-font-min)] leading-4 board-text-info"
            >
              <span class="mr-1 inline-flex rounded board-chip-info px-1.5 py-0.5 font-bold board-text-info">{{ inputEventSourceLabel(event) }}</span>
              <span class="font-semibold">{{ inputEventKindLabel(event) }}</span>
              <span class="px-1 board-text-info" aria-hidden="true">·</span>
              <span>{{ event.targetLabel || event.targetId }}.{{ inputEventProperty(event) }}</span>
              <span class="px-1 font-bold board-text-info" aria-hidden="true">=</span>
              <span class="break-all font-mono font-semibold">{{ inputEventValue(event) }}</span>
            </li>
          </ul>
          <p v-else class="mt-1 text-[length:var(--iot-font-min)] leading-4 board-text-info">
            {{ t('app.traceVisualization.noFuzzInputInThisStep') }}
          </p>
        </article>

        <div
          v-if="isInitialState"
          class="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-[length:var(--iot-font-min)] leading-4 text-slate-600"
          data-testid="playback-change-initial-state"
        >
          {{ t('app.traceVisualization.playbackInitialStateNoPrevious') }}
        </div>

        <!-- Ordered before the generic empty state on purpose: on a loop-back step "no observable changes" is
             the symptom, and the repetition is the explanation the viewer needs. -->
        <div
          v-else-if="isLoopBackState"
          class="rounded-lg border px-2.5 py-2 text-[length:var(--iot-font-min)] leading-4 board-chip-warning board-text-warning"
          data-testid="playback-change-loop-back"
        >
          {{ loopBackSentence }}
        </div>

        <div
          v-else-if="!hasObservableChanges"
          class="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-[length:var(--iot-font-min)] leading-4 text-slate-600"
          data-testid="playback-change-empty"
        >
          {{ t('app.traceVisualization.playbackNoObservableChanges') }}
        </div>

        <div
          v-if="kind === 'fuzzing' && !isInitialState"
          class="pt-0.5 text-[length:var(--iot-font-min)] font-bold uppercase text-slate-500"
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
            <div class="flex min-w-0 items-center gap-1.5 text-[11px] font-bold board-text-info">
              <span class="material-symbols-outlined text-sm board-text-info" aria-hidden="true">devices</span>
              <span class="truncate">{{ change.deviceLabel || t('app.unknown') }}</span>
            </div>
            <span class="shrink-0 text-[length:var(--iot-font-min)] font-semibold board-text-info">
              {{ change.details.length }} {{ t('app.traceVisualization.changeCountSuffix') }}
            </span>
          </div>
          <ul class="mt-1.5 space-y-1">
            <li
              v-for="(detail, index) in change.details"
              :key="`${detail.kind}-${detail.name || ''}-${index}`"
              class="grid grid-cols-[minmax(4.5rem,auto)_minmax(0,1fr)] items-baseline gap-2 text-[length:var(--iot-font-min)] leading-4"
            >
              <span class="truncate font-semibold text-slate-600" :title="detailLabel(detail, change.deviceId)">{{ detailLabel(detail, change.deviceId) }}</span>
              <span class="min-w-0 break-words font-mono text-slate-800">
                <span class="text-slate-500">{{ formatValue(detail.previousValue, detail.kind, change.deviceId) }}</span>
                <span class="px-1 font-sans font-bold board-text-info" aria-hidden="true">-&gt;</span>
                <span class="font-semibold board-text-info">{{ formatValue(detail.currentValue, detail.kind, change.deviceId) }}</span>
              </span>
            </li>
          </ul>
        </article>

        <article
          v-if="environmentChanges.length > 0"
          class="playback-change-popover__environment rounded-lg border px-2.5 py-2"
          data-testid="playback-change-environment"
        >
          <!--
            Informational, matching the device-changes section above.

            This carried the **warning** role while the device section beside it carries **info** — the same
            popover, the same kind of fact, and no reason an environment value moving is more alarming than a
            device state moving. During a replay both are the trace's *evidence*: a temperature climbing to 26
            is what the counterexample exists to show, not a hazard to flag. Colouring half the evidence amber
            made the trace's own content read as a warning about itself, and left the two halves of one panel
            disagreeing about what they were.
          -->
          <div class="flex items-center justify-between gap-2">
            <div class="flex min-w-0 items-center gap-1.5 text-[11px] font-bold board-text-info">
              <span class="material-symbols-outlined text-sm board-text-info" aria-hidden="true">terrain</span>
              <span>{{ t('app.traceVisualization.environmentChanges') }}</span>
            </div>
            <span class="shrink-0 text-[length:var(--iot-font-min)] font-semibold board-text-info">
              {{ environmentChanges.length }} {{ t('app.traceVisualization.changeCountSuffix') }}
            </span>
          </div>
          <ul class="mt-1.5 space-y-1">
            <li
              v-for="change in environmentChanges"
              :key="change.name"
              class="grid grid-cols-[minmax(4.5rem,auto)_minmax(0,1fr)] items-baseline gap-2 text-[length:var(--iot-font-min)] leading-4"
            >
              <span class="truncate font-semibold text-slate-600" :title="formatEnvironmentToken(change.name, change.name)">{{ formatEnvironmentToken(change.name, change.name) }}</span>
              <span class="min-w-0 break-words font-mono text-slate-800">
                <span class="text-slate-500">{{ formatEnvironmentToken(change.name, change.previousValue) }}</span>
                <span class="px-1 font-sans font-bold board-text-warning" aria-hidden="true">-&gt;</span>
                <span class="font-semibold board-text-warning">{{ formatEnvironmentToken(change.name, change.currentValue) }}</span>
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
            <span class="material-symbols-outlined text-sm board-text-success" aria-hidden="true">account_tree</span>
            <span>{{ t('app.traceVisualization.automationInThisStep') }}</span>
          </div>
          <div class="mt-1.5 flex flex-wrap gap-1">
            <span
              v-for="(rule, index) in triggeredRules"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="max-w-full truncate rounded-full board-surface-success px-2 py-1 text-[length:var(--iot-font-min)] font-semibold board-text-success"
              :title="ruleLabel(rule, index)"
            >
              {{ ruleLabel(rule, index) }}
            </span>
          </div>
          <p class="mt-1.5 text-[length:var(--iot-font-min)] leading-4 text-slate-600">
            {{ animatedEdgeCount > 0
              ? t('app.traceVisualization.playbackAnimatedEdges', { count: animatedEdgeCount })
              : t('app.traceVisualization.playbackTriggeredRuleWithoutCurrentEdge') }}
          </p>
        </article>

        <article
          v-if="compromisedAutomationLinks.length > 0"
          class="board-surface-danger rounded-lg px-2.5 py-2"
          data-testid="playback-change-compromised-links"
        >
          <div class="flex items-center gap-1.5 text-[11px] font-bold board-text-danger">
            <span class="material-symbols-outlined text-sm" aria-hidden="true">link_off</span>
            <span>{{ t('app.traceVisualization.compromisedAutomationLinks') }}</span>
          </div>
          <div class="mt-1.5 flex flex-wrap gap-1">
            <span
              v-for="(rule, index) in compromisedAutomationLinks"
              :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
              class="max-w-full truncate rounded-full border board-border-subtle bg-white px-2 py-1 text-[length:var(--iot-font-min)] font-semibold board-text-danger"
              :title="ruleLabel(rule, index)"
            >
              {{ ruleLabel(rule, index) }}
            </span>
          </div>
          <p class="mt-1.5 text-[length:var(--iot-font-min)] leading-4 board-text-danger">
            {{ t('app.traceVisualization.playbackCompromisedEdgesStatic', { count: compromisedEdgeCount }) }}
          </p>
        </article>
      </div>
    </Transition>
  </aside>
</template>
