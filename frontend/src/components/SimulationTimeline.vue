<script setup lang="ts">
import { ref, computed, nextTick, watch, onBeforeUnmount } from 'vue'
import { useI18n } from 'vue-i18n'
import type { SimulationState } from '../types/simulation'

const props = defineProps<{
  states: SimulationState[]
  visible: boolean
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'highlight-state': [data: { states: SimulationState[]; selectedStateIndex: number } | null]
}>()

const { t } = useI18n()

// 当前选中的状态索引
const selectedStateIndex = ref(0)

// 当前状态
const currentState = computed(() => {
  return props.states[selectedStateIndex.value] || null
})

// 所有状态数量
const totalStates = computed(() => {
  return props.states?.length || 0
})

// 获取攻击强度
const intensity = computed(() => {
  if (!currentState.value?.envVariables) return null
  const intensityVar = currentState.value.envVariables.find(v => v.name === 'intensity')
  if (intensityVar) {
    return parseInt(intensityVar.value, 10)
  }
  return null
})

// 检查当前状态是否有被攻击的设备
const hasAttackedDevices = computed(() => {
  if (!currentState.value?.devices) return false
  return currentState.value.devices.some(device =>
    device.variables?.some(v => v.name === 'is_attack' && v.value.toUpperCase() === 'TRUE')
  )
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

const focusStateButton = (index: number) => {
  void nextTick(() => {
    const button = document.querySelector<HTMLButtonElement>(`[data-testid="simulation-timeline-state-${index}"]`)
    button?.focus()
  })
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
  focusStateButton(nextIndex)
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
  
  isPlaying.value = true
  playInterval = setInterval(() => {
    if (selectedStateIndex.value < totalStates.value - 1) {
      selectedStateIndex.value++
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
    goToState(Math.min(selectedStateIndex.value, props.states.length - 1))
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

onBeforeUnmount(() => {
  stop()
})

// 监听状态索引变化
watch(selectedStateIndex, () => {
  if (props.visible) {
    highlightState()
  }
})
</script>

<template>
  <!-- 底部时间轴控制栏 -->
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
      <!-- Timeline -->
      <div>
        <div class="flex items-center justify-between mb-3 flex-shrink-0">
          <div class="flex items-center gap-2">
            <span class="text-sm font-bold text-slate-700">{{ t('app.traceVisualization.stateSequence') }}</span>
            <span class="px-2 py-0.5 bg-indigo-100 text-indigo-600 text-xs rounded-full" aria-live="polite">
              {{ totalStates > 0 ? selectedStateIndex + 1 : 0 }} / {{ totalStates }}
            </span>
            <!-- 显示攻击强度 -->
            <span v-if="intensity !== null" class="px-2 py-0.5 bg-red-100 text-red-600 text-xs rounded-full flex items-center gap-1">
              <span class="material-symbols-outlined text-xs" aria-hidden="true">warning</span>
              {{ t('app.traceVisualization.intensity') }}: {{ intensity }}
            </span>
            <!-- 显示被攻击设备数量 -->
            <span v-if="hasAttackedDevices" class="px-2 py-0.5 bg-red-500 text-white text-xs rounded-full flex items-center gap-1 animate-pulse">
              <span class="material-symbols-outlined text-xs" aria-hidden="true">security</span>
              {{ t('app.traceVisualization.attackedBang') }}
            </span>
          </div>
          <div class="flex items-center gap-2 flex-shrink-0">
            <button
              type="button"
              @click="play"
              data-testid="simulation-timeline-play"
              :disabled="totalStates <= 1"
              :aria-label="isPlaying ? t('app.traceVisualization.stop') : t('app.traceVisualization.play')"
              class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1"
              :class="isPlaying 
                ? 'bg-indigo-500 text-white' 
                : totalStates <= 1
                  ? 'bg-slate-100 text-slate-400 cursor-not-allowed'
                  : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
            >
              <span class="material-symbols-outlined text-sm" aria-hidden="true">{{ isPlaying ? 'stop' : 'play_arrow' }}</span>
              {{ isPlaying ? t('app.traceVisualization.stop') : t('app.traceVisualization.play') }}
            </button>
            <button
              type="button"
              @click="close"
              data-testid="simulation-timeline-close"
              class="p-1.5 hover:bg-slate-100 rounded-lg transition-colors"
              :aria-label="t('app.close')"
            >
              <span class="material-symbols-outlined text-slate-500" aria-hidden="true">close</span>
            </button>
          </div>
        </div>
        
        <!-- 时间轴容器：支持横向滚动 -->
        <div data-testid="simulation-timeline-scroll" class="overflow-x-auto scrollbar-thin py-2">
          <!-- 内部容器：根据状态数量动态调整宽度 -->
          <div 
            class="relative h-14"
            :style="{ width: states.length > 15 ? 'max-content' : '100%', minWidth: states.length > 15 ? `${Math.max(states.length * 32, 500)}px` : '100%' }"
          >
            <!-- 进度线背景 -->
            <div class="absolute top-1/2 left-2 right-2 h-3 bg-slate-200 rounded -translate-y-1/2"></div>
            
            <!-- 进度条 -->
            <div 
              v-if="selectedStateIndex > 0 && totalStates > 1"
              class="absolute top-1/2 h-3 bg-indigo-500 rounded transition-all duration-300 -translate-y-1/2"
              :style="{ 
                left: '8px',
                width: `calc((100% - 16px) * ${selectedStateIndex / (totalStates - 1)})`
              }"
            ></div>
            
            <!-- 状态节点 -->
            <div class="absolute top-1/2 left-2 right-2 flex justify-between items-center -translate-y-1/2">
              <button
                v-for="(_, index) in states"
                :key="index"
                type="button"
                @click="selectState(index)"
                @keydown="handleStateKeydown($event, index)"
                :tabindex="index === selectedStateIndex ? 0 : -1"
                :aria-label="getStateAriaLabel(index)"
                :aria-current="index === selectedStateIndex ? 'step' : undefined"
                :data-testid="`simulation-timeline-state-${index}`"
                class="w-6 h-6 rounded-full border-3 transition-all flex items-center justify-center relative z-10 flex-shrink-0 focus:outline-none focus:ring-2 focus:ring-indigo-500 focus:ring-offset-2"
                :class="index === selectedStateIndex 
                  ? 'bg-indigo-500 border-indigo-500 scale-125 shadow-lg' 
                  : index < selectedStateIndex 
                    ? 'bg-green-500 border-green-500' 
                    : 'bg-white border-slate-300 hover:border-indigo-300'"
              >
                <span 
                  v-if="index === selectedStateIndex" 
                  class="text-white text-[8px] font-bold"
                >★</span>
                <span v-else class="text-slate-500 text-[6px] font-medium">{{ index + 1 }}</span>
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
  font-variation-settings: 'FILL' 0, 'wght' 400, 'GRAD' 0, 'opsz' 24;
}
</style>
