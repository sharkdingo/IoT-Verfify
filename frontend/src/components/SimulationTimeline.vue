<script setup lang="ts">
import { ref, computed, nextTick, watch, onBeforeUnmount } from 'vue'
import { useI18n } from 'vue-i18n'
import type { SimulationState } from '../types/simulation'
import type { ModelRunSnapshot, ModelSemantics, RunBoardComparison } from '../types/modelSemantics'
import type { TraceTriggeredRule } from '../types/verify'
import { isModelSemanticsConsistent } from '../utils/modelSemantics'
import {
  isPlaybackDeviceAttacked,
  normalizePlaybackDeviceId,
  playbackDeviceChanged,
  playbackDeviceSecurityFacts,
  playbackDeviceSummaryParts
} from '../utils/traceView'

const props = defineProps<{
  states: SimulationState[]
  visible: boolean
  actualSteps?: number
  requestedSteps?: number
  modelComplete?: boolean
  disabledRuleCount?: number
  isAttack?: boolean
  attackBudget?: number
  enablePrivacy?: boolean
  modelSemantics?: ModelSemantics
  modelSnapshot?: ModelRunSnapshot
  boardComparison?: RunBoardComparison
  currentRuleIds?: string[]
  currentDeviceIds?: string[]
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'highlight-state': [data: { states: SimulationState[]; selectedStateIndex: number } | null]
  'open-run-details': []
}>()

const { t, locale } = useI18n()

const formatRunTimestamp = (value?: string): string => {
  if (!value) return t('app.unknown')
  const date = new Date(value)
  if (Number.isNaN(date.getTime())) return value
  return date.toLocaleString(locale.value.toLowerCase().startsWith('zh') ? 'zh-CN' : 'en-US')
}

// 当前选中的状态索引
const selectedStateIndex = ref(0)

// 当前状态
const currentState = computed(() => {
  return props.states[selectedStateIndex.value] || null
})

const previousState = computed(() => {
  if (selectedStateIndex.value <= 0) return null
  return props.states[selectedStateIndex.value - 1] || null
})

// 所有状态数量
const totalStates = computed(() => {
  return props.states?.length || 0
})

const selectedStateNumber = computed({
  get: () => selectedStateIndex.value + 1,
  set: (value: number) => {
    if (!Number.isFinite(value)) return
    selectState(Math.trunc(value) - 1)
  }
})

const selectedStateRangeIndex = computed({
  get: () => selectedStateIndex.value,
  set: (value: number) => {
    if (!Number.isFinite(value)) return
    selectState(Math.trunc(value))
  }
})

const currentEnvironmentVariables = computed(() => currentState.value?.envVariables || [])
const currentTriggeredRules = computed(() => currentState.value?.triggeredRules || [])
const currentCompromisedAutomationLinks = computed(() => currentState.value?.compromisedAutomationLinks || [])
const currentDevices = computed(() => currentState.value?.devices || [])
const currentRuleIdSet = computed(() => new Set((props.currentRuleIds || []).map(String)))
const currentDeviceIdSet = computed(() => new Set(
  (props.currentDeviceIds || []).map(normalizePlaybackDeviceId)
))

const triggeredRuleLabel = (rule: TraceTriggeredRule, index: number) =>
  rule.ruleLabel?.trim() || t('app.ruleNumber', { number: index + 1 })

const triggeredRuleExistsOnCurrentBoard = (rule: TraceTriggeredRule) =>
  rule.ruleId != null && currentRuleIdSet.value.has(String(rule.ruleId))

const previousDevice = (deviceId: string) => previousState.value?.devices?.find(device =>
  normalizePlaybackDeviceId(device.deviceId) === normalizePlaybackDeviceId(deviceId)
)

const deviceChanged = (device: SimulationState['devices'][number]) =>
  selectedStateIndex.value > 0 && playbackDeviceChanged(device, previousDevice(device.deviceId))

const deviceExistsOnCurrentBoard = (deviceId: string) =>
  currentDeviceIdSet.value.has(normalizePlaybackDeviceId(deviceId))

const deviceSummary = (device: SimulationState['devices'][number]) => {
  const parts = playbackDeviceSummaryParts(device)
  return parts.length > 0 ? parts.join(' · ') : t('app.unknown')
}

const deviceChangeSummary = (device: SimulationState['devices'][number]) => {
  const previous = previousDevice(device.deviceId)
  if (!previous) return t('app.traceVisualization.changed')
  const changes: string[] = []
  if ((previous.state || '') !== (device.state || '')) {
    changes.push(`${t('app.state')}: ${previous.state || t('app.unknown')} -> ${device.state || t('app.unknown')}`)
  }
  if ((previous.mode || '') !== (device.mode || '')) {
    changes.push(`${t('app.mode')}: ${previous.mode || t('app.unknown')} -> ${device.mode || t('app.unknown')}`)
  }
  const previousVariables = new Map((previous.variables || []).map(variable => [variable.name, variable.value]))
  ;(device.variables || []).forEach(variable => {
    const previousValue = previousVariables.get(variable.name)
    if (previousValue !== undefined && previousValue !== variable.value) {
      changes.push(`${variable.name}: ${previousValue} -> ${variable.value}`)
    }
  })
  if (previous.compromised !== device.compromised) {
    changes.push(device.compromised
      ? t('app.traceVisualization.deviceBecameCompromised')
      : t('app.traceVisualization.deviceNoLongerCompromised'))
  }
  return changes.join(' · ') || t('app.traceVisualization.changed')
}

const modelSemanticsConsistent = computed(() => isModelSemanticsConsistent(
  props.modelSemantics,
  { isAttack: props.isAttack, attackBudget: props.attackBudget, enablePrivacy: props.enablePrivacy }
))

const attackSelectionText = computed(() => {
  if (props.modelSemantics?.attackSelectionPolicy === 'EXACT_ATTACK_POINTS') {
    const points = (props.modelSemantics.selectedAttackPoints || [])
      .map(point => point.displayLabel?.trim() || (point.kind === 'DEVICE'
        ? t('app.attackDevicePoint', { id: point.deviceId })
        : t('app.attackAutomationLinkPoint', { id: point.ruleId })))
      .join(', ')
    return t('app.attackExactSelectionDetail', {
      count: props.modelSemantics.selectedAttackPoints?.length ?? 0,
      points
    })
  }
  return t('app.attackExhaustiveSelectionDetail', {
    count: props.attackBudget ?? 0,
    total: props.modelSemantics?.modeledAttackPointCount ?? 0
  })
})

const attackSelectionShortText = computed(() => {
  if (!modelSemanticsConsistent.value) {
    return t('app.traceVisualization.attackScenario')
  }
  return props.modelSemantics?.attackSelectionPolicy === 'EXACT_ATTACK_POINTS'
    ? t('app.attackExactSelectionShort', {
        count: props.modelSemantics.selectedAttackPoints?.length ?? 0
      })
    : t('app.attackExhaustiveSelectionShort', { count: props.attackBudget ?? 0 })
})

const deviceSecurityFacts = (device: SimulationState['devices'][number]) =>
  playbackDeviceSecurityFacts(device)

const getPreviousEnvValue = (name: string) =>
  previousState.value?.envVariables?.find(variable => variable.name === name)?.value

const environmentVariableChanged = (name: string, value: string) =>
  selectedStateIndex.value > 0 && getPreviousEnvValue(name) !== value

const environmentVariableTitle = (name: string, value: string) => {
  const previous = getPreviousEnvValue(name)
  if (previous === undefined || previous === value) {
    return `${name}: ${value}`
  }
  return `${name}: ${previous} -> ${value}`
}

// Runtime compromised-point count from NuSMV globals, not the configured attack budget.
const runtimeCompromisedPointCount = computed(() => {
  if (!currentState.value?.globalVariables) return null
  const pointCount = currentState.value.globalVariables.find(v => v.name === 'compromisedPointCount')
  if (pointCount) {
    const parsed = Number.parseInt(pointCount.value, 10)
    return Number.isFinite(parsed) ? parsed : null
  }
  return null
})

// 检查当前状态是否有被攻击的设备
const hasAttackedDevices = computed(() => {
  if (!currentState.value?.devices) return false
  return currentState.value.devices.some(device => device.compromised === true)
})

// 关闭
const close = () => {
  emit('update:visible', false)
  emit('highlight-state', null)
}

// 跳转到指定状态
const goToState = (index: number) => {
  const lastIndex = Math.max(totalStates.value - 1, 0)
  selectedStateIndex.value = Math.min(Math.max(index, 0), lastIndex)
}

const selectState = (index: number) => {
  goToState(index)
  highlightState()
}

const selectPreviousState = () => selectState(selectedStateIndex.value - 1)
const selectNextState = () => selectState(selectedStateIndex.value + 1)

const revealStateButton = (index: number, focus = false) => {
  void nextTick(() => {
    const button = document.querySelector<HTMLButtonElement>(`[data-testid="simulation-timeline-state-${index}"]`)
    button?.scrollIntoView({ behavior: 'smooth', block: 'nearest', inline: 'center' })
    if (focus) {
      button?.focus()
    }
  })
}

const selectStateFromTimelinePointer = (event: PointerEvent) => {
  if (totalStates.value <= 1) return
  if (event.target instanceof Element && event.target.closest('button')) return
  const target = event.currentTarget as HTMLElement
  const rect = target.getBoundingClientRect()
  const trackLeft = rect.left + 8
  const trackWidth = Math.max(1, rect.width - 16)
  const ratio = Math.min(1, Math.max(0, (event.clientX - trackLeft) / trackWidth))
  const nextIndex = Math.round(ratio * (totalStates.value - 1))
  selectState(nextIndex)
  revealStateButton(nextIndex, true)
}

const handleStateKeydown = (event: KeyboardEvent, index: number) => {
  const keyToIndex: Record<string, number> = {
    ArrowLeft: index - 1,
    ArrowDown: index - 1,
    ArrowRight: index + 1,
    ArrowUp: index + 1,
    Home: 0,
    End: totalStates.value - 1
  }
  if (!(event.key in keyToIndex)) return
  event.preventDefault()
  const lastIndex = Math.max(totalStates.value - 1, 0)
  const nextIndex = Math.min(Math.max(keyToIndex[event.key], 0), lastIndex)
  selectState(nextIndex)
  revealStateButton(nextIndex, true)
}

const getStateAriaLabel = (index: number) => {
  return `${t('app.traceVisualization.state', { index: index + 1 })} (${index + 1}/${totalStates.value})`
}

// 播放动画
const isPlaying = ref(false)
let playInterval: ReturnType<typeof setInterval> | null = null

const play = () => {
  if (isPlaying.value) {
    stop()
    return
  }
  if (totalStates.value <= 1) {
    return
  }

  if (selectedStateIndex.value >= totalStates.value - 1) {
    goToState(0)
    highlightState()
  }
  
  isPlaying.value = true
  playInterval = setInterval(() => {
    if (selectedStateIndex.value < totalStates.value - 1) {
      selectedStateIndex.value++
      if (selectedStateIndex.value >= totalStates.value - 1) {
        stop()
      }
    } else {
      // 到达最后一个状态，停止播放
      stop()
    }
  }, 1500)
}

const stop = () => {
  isPlaying.value = false
  if (playInterval) {
    clearInterval(playInterval)
    playInterval = null
  }
}

// 高亮显示当前状态 - 发送完整的状态信息
const highlightState = () => {
  if (props.visible && props.states.length > 0) {
    emit('highlight-state', {
      states: props.states,
      selectedStateIndex: selectedStateIndex.value
    })
  }
}

// 监听对话框关闭
watch(() => props.visible, (newVal) => {
  if (!newVal) {
    stop()
    emit('highlight-state', null)
  } else if (props.states.length > 0) {
    goToState(0)
    highlightState()
  }
})

watch(() => props.states.length, (length) => {
  if (length <= 0) {
    selectedStateIndex.value = 0
    stop()
    emit('highlight-state', null)
    return
  }
  if (selectedStateIndex.value >= length) {
    selectedStateIndex.value = length - 1
  }
  if (props.visible) {
    highlightState()
  }
})

watch(() => props.states, (states, previousStates) => {
  if (states === previousStates) return
  stop()
  selectedStateIndex.value = 0
  if (props.visible && states.length > 0) {
    highlightState()
  }
})

onBeforeUnmount(() => {
  stop()
})

// 监听状态索引变化
watch(selectedStateIndex, () => {
  if (props.visible) {
    highlightState()
    revealStateButton(selectedStateIndex.value)
  }
})
</script>

<template>
  <div
    v-if="visible"
    class="board-timeline-host board-timeline-host--simulation"
    data-testid="simulation-timeline-host"
    role="region"
    :aria-label="t('app.traceVisualization.stateSequence')"
  >
    <div
      class="board-timeline board-timeline--simulation"
      data-testid="simulation-timeline"
      :data-selected-state-index="selectedStateIndex"
    >
      <header class="board-timeline__sticky-header mb-2 flex items-start justify-between gap-3 border-b border-slate-200 pb-2">
        <div class="min-w-0">
          <div class="flex flex-wrap items-center gap-2">
            <h2 class="text-sm font-bold text-slate-800">{{ t('app.traceVisualization.modelTracePlayback') }}</h2>
            <span class="rounded-full bg-indigo-100 px-2 py-0.5 text-xs font-semibold text-indigo-700" aria-live="polite">
              {{ totalStates > 0 ? selectedStateIndex + 1 : 0 }} / {{ totalStates }}
            </span>
            <span v-if="runtimeCompromisedPointCount !== null" class="inline-flex items-center gap-1 rounded-full bg-red-100 px-2 py-0.5 text-xs font-semibold text-red-700">
              <span class="material-symbols-outlined text-xs" aria-hidden="true">warning</span>
              {{ t('app.traceVisualization.runtimeCompromisedPoints') }}: {{ runtimeCompromisedPointCount }}
            </span>
            <span v-if="isAttack" class="rounded-full bg-orange-100 px-2 py-0.5 text-xs font-semibold text-orange-700">
              {{ attackSelectionShortText }}
            </span>
            <span v-if="enablePrivacy && modelSemanticsConsistent" class="rounded-full bg-fuchsia-100 px-2 py-0.5 text-xs font-semibold text-fuchsia-700">
              {{ t('app.traceVisualization.privacyPropagationEnabled') }}
            </span>
            <span v-if="hasAttackedDevices" class="inline-flex items-center gap-1 rounded-full bg-red-600 px-2 py-0.5 text-xs font-semibold text-white">
              <span class="material-symbols-outlined text-xs" aria-hidden="true">security</span>
              {{ t('app.traceVisualization.attackedBang') }}
            </span>
          </div>
          <p class="mt-0.5 text-[10px] leading-4 text-slate-500">{{ t('app.traceVisualization.modelTraceNotPrediction') }}</p>
        </div>

        <div class="flex flex-shrink-0 items-center gap-1.5">
          <button
            type="button"
            data-testid="simulation-timeline-run-details"
            class="inline-flex h-8 items-center gap-1 rounded-lg border border-slate-200 bg-white px-2 text-xs font-semibold text-slate-700 transition-colors hover:bg-slate-100"
            :title="t('app.viewSimulationRunDetails')"
            :aria-label="t('app.viewSimulationRunDetails')"
            @click="emit('open-run-details')"
          >
            <span class="material-symbols-outlined text-base" aria-hidden="true">description</span>
            <span class="hidden sm:inline">{{ t('app.runDetails') }}</span>
          </button>
          <button
            type="button"
            data-testid="simulation-timeline-play"
            :disabled="totalStates <= 1"
            :aria-label="isPlaying ? t('app.traceVisualization.pause') : t('app.traceVisualization.play')"
            class="inline-flex h-8 items-center gap-1 rounded-lg px-3 text-xs font-semibold transition-colors"
            :class="isPlaying
              ? 'bg-indigo-600 text-white'
              : totalStates <= 1
                ? 'cursor-not-allowed bg-slate-100 text-slate-400'
                : 'bg-indigo-600 text-white hover:bg-indigo-700'"
            @click="play"
          >
            <span class="material-symbols-outlined text-base" aria-hidden="true">{{ isPlaying ? 'pause' : 'play_arrow' }}</span>
            {{ isPlaying ? t('app.traceVisualization.pause') : t('app.traceVisualization.play') }}
          </button>
          <button
            type="button"
            data-testid="simulation-timeline-close"
            class="inline-flex h-8 w-8 items-center justify-center rounded-lg text-slate-500 transition-colors hover:bg-slate-100 hover:text-slate-800"
            :aria-label="t('app.close')"
            @click="close"
          >
            <span class="material-symbols-outlined" aria-hidden="true">close</span>
          </button>
        </div>
      </header>

      <div
        v-if="modelComplete === false"
        class="mb-2 rounded-lg border border-amber-300 bg-amber-50 px-3 py-2 text-[11px] font-medium leading-4 text-amber-800"
        data-testid="simulation-timeline-incomplete-warning"
      >
        {{ t('app.traceVisualization.modelIncompletePlayback', { rules: disabledRuleCount || 0 }) }}
      </div>

      <div
        v-if="actualSteps !== undefined && requestedSteps !== undefined && actualSteps < requestedSteps"
        class="mb-2 rounded-lg border border-amber-300 bg-amber-50 px-3 py-2 text-[11px] font-medium leading-4 text-amber-800"
        data-testid="simulation-timeline-short-horizon-warning"
      >
        {{ t('app.simulationStoppedBeforeRequestedSteps', { actual: actualSteps, requested: requestedSteps }) }}
      </div>

      <div
        v-if="!modelSemanticsConsistent"
        class="mb-2 rounded-lg border border-amber-300 bg-amber-50 px-3 py-2 text-[11px] font-semibold leading-4 text-amber-800"
      >
        {{ t('app.modelSemanticsUnavailable') }}
      </div>

      <div
        v-if="boardComparison === 'CHANGED'"
        class="mb-2 rounded-lg border border-amber-300 bg-amber-50 px-3 py-2 text-[11px] font-medium leading-4 text-amber-900"
        data-testid="simulation-board-drift-warning"
      >
        {{ t('app.runBoardInputChanged') }}
      </div>

      <section class="border-b border-slate-200 pb-2" :aria-label="t('app.traceVisualization.stateSequence')">
        <div class="grid items-center gap-2 sm:grid-cols-[auto_minmax(8rem,1fr)_auto]">
          <div class="flex items-center gap-1">
            <button
              type="button"
              class="inline-flex h-8 w-8 items-center justify-center rounded-lg border border-slate-200 bg-white text-slate-700 transition-colors hover:bg-slate-100 disabled:cursor-not-allowed disabled:text-slate-300"
              :disabled="selectedStateIndex <= 0"
              :aria-label="t('app.traceVisualization.previousState')"
              @click="selectPreviousState"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">chevron_left</span>
            </button>
            <label class="flex h-8 items-center gap-1 rounded-lg border border-slate-200 bg-white px-2 text-xs font-semibold text-slate-600">
              <span>{{ t('app.traceVisualization.stateLabel') }}</span>
              <input
                v-model.number="selectedStateNumber"
                data-testid="simulation-timeline-step-input"
                type="number"
                :min="1"
                :max="Math.max(totalStates, 1)"
                :disabled="totalStates <= 0"
                class="w-10 bg-transparent text-center font-bold text-slate-800 outline-none"
                :aria-label="t('app.traceVisualization.jumpToState')"
              >
              <span class="text-slate-400">/ {{ totalStates }}</span>
            </label>
            <button
              type="button"
              class="inline-flex h-8 w-8 items-center justify-center rounded-lg border border-slate-200 bg-white text-slate-700 transition-colors hover:bg-slate-100 disabled:cursor-not-allowed disabled:text-slate-300"
              :disabled="selectedStateIndex >= totalStates - 1"
              :aria-label="t('app.traceVisualization.nextState')"
              @click="selectNextState"
            >
              <span class="material-symbols-outlined text-lg" aria-hidden="true">chevron_right</span>
            </button>
          </div>
          <input
            v-model.number="selectedStateRangeIndex"
            data-testid="simulation-timeline-range"
            type="range"
            :min="0"
            :max="Math.max(totalStates - 1, 0)"
            :disabled="totalStates <= 1"
            class="min-w-0 flex-1 accent-indigo-600"
            :aria-label="t('app.traceVisualization.jumpToState')"
          >
          <span class="text-right text-[10px] font-semibold text-slate-500">
            {{ selectedStateIndex === 0
              ? t('app.traceVisualization.initialModelState')
              : t('app.traceVisualization.transitionNumber', { index: selectedStateIndex }) }}
          </span>
        </div>

        <div data-testid="simulation-timeline-scroll" class="mt-1 overflow-x-auto scrollbar-thin py-1">
          <div
            class="relative h-12"
            data-testid="simulation-timeline-track"
            :style="{ width: states.length > 15 ? 'max-content' : '100%', minWidth: states.length > 15 ? `${Math.max(states.length * 32, 500)}px` : '100%' }"
            @pointerdown="selectStateFromTimelinePointer"
          >
            <div class="absolute left-2 right-2 top-1/2 h-2 -translate-y-1/2 rounded bg-slate-200"></div>
            <div
              v-if="selectedStateIndex > 0 && totalStates > 1"
              class="absolute top-1/2 h-2 -translate-y-1/2 rounded bg-indigo-600 transition-all duration-300"
              :style="{
                left: '8px',
                width: `calc((100% - 16px) * ${selectedStateIndex / (totalStates - 1)})`
              }"
            ></div>
            <div class="absolute left-2 right-2 top-1/2 flex -translate-y-1/2 items-center justify-between">
              <button
                v-for="(_, index) in states"
                :key="index"
                type="button"
                :tabindex="index === selectedStateIndex ? 0 : -1"
                :aria-label="getStateAriaLabel(index)"
                :aria-current="index === selectedStateIndex ? 'step' : undefined"
                :data-testid="`simulation-timeline-state-${index}`"
                class="relative z-10 flex h-6 w-6 flex-shrink-0 items-center justify-center rounded-full border-2 transition-all focus:outline-none focus:ring-2 focus:ring-indigo-500 focus:ring-offset-2"
                :class="index === selectedStateIndex
                  ? 'scale-125 border-indigo-600 bg-indigo-600 shadow-md'
                  : index < selectedStateIndex
                    ? 'border-indigo-300 bg-indigo-200'
                    : 'border-slate-300 bg-white hover:border-indigo-400'"
                @click="selectState(index)"
                @keydown="handleStateKeydown($event, index)"
              >
                <span v-if="index === selectedStateIndex" class="text-[8px] font-bold text-white">{{ index + 1 }}</span>
                <span v-else class="text-[7px] font-semibold text-slate-500">{{ index + 1 }}</span>
              </button>
            </div>
          </div>
        </div>
      </section>

      <details class="group pt-2" data-testid="simulation-timeline-state-details">
        <summary class="flex cursor-pointer list-none items-center justify-between gap-3 rounded-lg px-1 py-1 text-[11px] font-semibold text-slate-600 hover:bg-slate-100">
          <span class="inline-flex items-center gap-1.5">
            <span class="material-symbols-outlined text-base" aria-hidden="true">tune</span>
            {{ t('app.traceVisualization.stateDetails') }}
          </span>
          <span class="material-symbols-outlined text-base transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
        </summary>
        <div class="mt-1.5 border-t border-slate-200">
      <section class="border-b border-slate-200 py-2" data-testid="simulation-timeline-triggered-rules">
        <div class="text-[10px] font-bold uppercase text-slate-500">
          {{ selectedStateIndex === 0
            ? t('app.traceVisualization.initialModelState')
            : t('app.traceVisualization.rulesAppliedToReachState') }}
        </div>
        <div v-if="selectedStateIndex > 0 && currentTriggeredRules.length > 0" class="mt-1.5 flex flex-wrap gap-1.5">
          <span
            v-for="(rule, index) in currentTriggeredRules"
            :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
            class="inline-flex max-w-full items-center gap-1 rounded-full border px-2 py-1 text-[10px] font-semibold"
            :class="triggeredRuleExistsOnCurrentBoard(rule)
              ? 'border-emerald-200 bg-emerald-50 text-emerald-700'
              : 'border-amber-300 bg-amber-50 text-amber-800'"
            :title="triggeredRuleExistsOnCurrentBoard(rule) ? undefined : t('app.traceVisualization.historicalRuleNotOnCurrentBoard')"
          >
            <span class="max-w-[14rem] truncate">{{ triggeredRuleLabel(rule, index) }}</span>
            <span v-if="!triggeredRuleExistsOnCurrentBoard(rule)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
          </span>
        </div>
        <p v-else-if="selectedStateIndex > 0" class="mt-1 text-[11px] text-slate-500">
          {{ t('app.traceVisualization.noRulesApplied') }}
        </p>
      </section>

      <section
        v-if="currentCompromisedAutomationLinks.length > 0"
        class="border-b border-red-200 bg-red-50 px-2 py-2"
        data-testid="simulation-timeline-compromised-links"
      >
        <div class="text-[10px] font-bold uppercase text-red-700">
          {{ t('app.traceVisualization.compromisedAutomationLinks') }}
        </div>
        <div class="mt-1.5 flex flex-wrap gap-1.5">
          <span
            v-for="(rule, index) in currentCompromisedAutomationLinks"
            :key="rule.ruleId || `${rule.ruleLabel}-${index}`"
            class="inline-flex max-w-full items-center gap-1 rounded-full border border-red-200 bg-white px-2 py-1 text-[10px] font-semibold text-red-700"
            :title="triggeredRuleExistsOnCurrentBoard(rule) ? t('app.traceVisualization.compromisedAutomationLinkHint') : t('app.traceVisualization.historicalRuleNotOnCurrentBoard')"
          >
            <span class="material-symbols-outlined text-[12px]" aria-hidden="true">link_off</span>
            <span class="max-w-[14rem] truncate">{{ triggeredRuleLabel(rule, index) }}</span>
            <span v-if="!triggeredRuleExistsOnCurrentBoard(rule)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
          </span>
        </div>
      </section>

      <section v-if="currentDevices.length > 0" class="border-b border-slate-200 py-2" data-testid="simulation-timeline-devices">
        <div class="mb-1.5 inline-flex items-center gap-1 text-[10px] font-bold uppercase text-slate-500">
          <span class="material-symbols-outlined text-[13px]" aria-hidden="true">devices</span>
          {{ t('app.traceVisualization.devicesInCurrentState') }}
        </div>
        <div class="flex flex-wrap gap-1.5">
          <span
            v-for="device in currentDevices"
            :key="device.deviceId"
            class="inline-flex max-w-full flex-wrap items-center gap-1 rounded border px-2 py-1 text-[10px] font-semibold"
            :class="!deviceExistsOnCurrentBoard(device.deviceId)
              ? 'border-amber-300 bg-amber-50 text-amber-800'
              : deviceChanged(device)
                ? 'border-indigo-300 bg-indigo-50 text-indigo-800'
                : 'border-slate-200 bg-slate-50 text-slate-700'"
            :title="deviceExistsOnCurrentBoard(device.deviceId) ? undefined : t('app.traceVisualization.historicalDeviceNotOnCurrentBoard')"
          >
            <span class="font-bold">{{ device.deviceLabel || device.deviceId }}</span>
            <span class="max-w-[20rem] break-words font-mono font-normal">{{ deviceSummary(device) }}</span>
            <span
              v-if="deviceChanged(device)"
              class="max-w-[24rem] truncate rounded bg-indigo-200 px-1 text-[9px] text-indigo-800"
              :title="deviceChangeSummary(device)"
            >
              {{ deviceChangeSummary(device) }}
            </span>
            <span v-if="isPlaybackDeviceAttacked(device)" class="rounded bg-red-100 px-1 text-[9px] text-red-700">{{ t('app.traceVisualization.attacked') }}</span>
            <span
              v-if="deviceSecurityFacts(device).untrustedLabels.length > 0"
              class="rounded bg-amber-100 px-1 text-[9px] text-amber-800"
              :title="t('app.traceVisualization.untrustedLabelDetails', { labels: deviceSecurityFacts(device).untrustedLabels.join(', ') })"
            >
              {{ t('app.traceVisualization.includesUntrustedSource') }}
            </span>
            <span
              v-if="deviceSecurityFacts(device).privateLabels.length > 0"
              class="rounded bg-fuchsia-100 px-1 text-[9px] text-fuchsia-800"
              :title="t('app.traceVisualization.privateLabelDetails', { labels: deviceSecurityFacts(device).privateLabels.join(', ') })"
            >
              {{ t('app.traceVisualization.includesPrivateData') }}
            </span>
            <span v-if="!deviceExistsOnCurrentBoard(device.deviceId)" class="material-symbols-outlined text-[12px]" aria-hidden="true">history</span>
          </span>
        </div>
      </section>

      <section v-if="currentEnvironmentVariables.length > 0" class="border-b border-slate-200 py-2" data-testid="simulation-timeline-env">
        <div class="mb-1.5 inline-flex items-center gap-1 text-[10px] font-bold uppercase text-slate-500">
          <span class="material-symbols-outlined text-[13px]" aria-hidden="true">terrain</span>
          {{ t('app.traceVisualization.environmentVariables') }}
        </div>
        <div class="flex flex-wrap gap-1.5">
          <span
            v-for="envVar in currentEnvironmentVariables"
            :key="envVar.name"
            class="inline-flex max-w-full items-center gap-1 rounded-full border px-2 py-1 text-[10px] font-bold"
            :class="environmentVariableChanged(envVar.name, envVar.value)
              ? 'border-amber-300 bg-amber-50 text-amber-700'
              : 'border-slate-200 bg-slate-50 text-slate-600'"
            :title="environmentVariableTitle(envVar.name, envVar.value)"
          >
            <span class="max-w-[7rem] truncate">{{ envVar.name }}</span>
            <span class="font-mono">{{ envVar.value }}</span>
            <span v-if="environmentVariableChanged(envVar.name, envVar.value)" class="rounded-full bg-amber-200 px-1 text-[9px] text-amber-800">{{ t('app.traceVisualization.changed') }}</span>
          </span>
        </div>
      </section>

      <details class="group pt-2 text-[11px] text-slate-600" data-testid="simulation-timeline-snapshot-notice">
        <summary class="flex cursor-pointer list-none items-center justify-between gap-3 rounded-lg px-1 py-1 font-semibold text-slate-700 hover:bg-slate-100">
          <span class="inline-flex min-w-0 items-center gap-1.5">
            <span class="material-symbols-outlined text-base text-sky-700" aria-hidden="true">inventory_2</span>
            <span>{{ t('app.runScopeAndSnapshot') }}</span>
          </span>
          <span class="flex items-center gap-1.5">
            <span
              class="rounded-full px-2 py-0.5 text-[10px] font-semibold"
              :class="boardComparison === 'UNCHANGED'
                ? 'bg-emerald-100 text-emerald-700'
                : boardComparison === 'CHANGED'
                  ? 'bg-amber-100 text-amber-800'
                  : 'bg-slate-100 text-slate-600'"
              data-testid="simulation-board-comparison"
            >
              {{ boardComparison === 'UNCHANGED'
                ? t('app.runBoardInputUnchangedShort')
                : boardComparison === 'CHANGED'
                  ? t('app.runBoardInputChangedShort')
                  : boardComparison === 'UNAVAILABLE'
                    ? t('app.runBoardComparisonUnavailableShort')
                    : t('app.runBoardNotComparedShort') }}
            </span>
            <span class="material-symbols-outlined text-base transition-transform group-open:rotate-180" aria-hidden="true">expand_more</span>
          </span>
        </summary>
        <div class="mt-1.5 space-y-1.5 border-l-2 border-sky-200 pl-3 leading-5">
          <p class="font-bold text-slate-700">{{ t('app.modelRunSnapshotTitle') }}</p>
          <p v-if="modelSnapshot">
            {{ t('app.modelRunSnapshotSummary', {
              time: formatRunTimestamp(modelSnapshot.capturedAt),
              devices: modelSnapshot.deviceCount,
              rules: modelSnapshot.ruleCount,
              specs: modelSnapshot.specificationCount,
              variables: modelSnapshot.environmentVariableCount,
              templates: modelSnapshot.deviceTemplateCount
            }) }}
          </p>
          <p>{{ t('app.traceVisualization.playbackSnapshotReadOnly') }}</p>
          <p v-if="modelSemanticsConsistent">
            {{ isAttack
              ? attackSelectionText
              : t('app.traceVisualization.simulationNoAttackContext') }}
          </p>
          <p v-if="modelSemanticsConsistent">
            {{ enablePrivacy
              ? t('app.traceVisualization.privacyPropagationEnabled')
              : t('app.traceVisualization.privacyPropagationNotModeled') }}
          </p>
          <p v-if="modelSemanticsConsistent">{{ t('app.environmentEvolutionIncluded') }}</p>
          <p v-if="modelSemanticsConsistent">{{ t('app.labelPropagationScopeSummary') }}</p>
          <p>
            {{ boardComparison === 'UNCHANGED'
              ? t('app.runBoardInputUnchanged')
              : boardComparison === 'CHANGED'
                ? t('app.runBoardInputChanged')
                : boardComparison === 'UNAVAILABLE'
                  ? t('app.runBoardComparisonUnavailable')
                  : t('app.runBoardNotCompared') }}
          </p>
        </div>
      </details>
        </div>
      </details>
    </div>
  </div>
</template>

<style scoped>
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
  font-variation-settings: 'FILL' 0, 'wght' 400, 'GRAD' 0, 'opsz' 24;
}
</style>
