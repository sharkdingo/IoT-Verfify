<script setup lang="ts">
import { ref, computed, watch, onBeforeUnmount } from 'vue'
import type { SimulationState } from '../types/simulation'

const props = defineProps<{
  states: SimulationState[]
  visible: boolean
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'highlight-state': [data: { states: SimulationState[]; selectedStateIndex: number } | null]
}>()

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

// 关闭
const close = () => {
  emit('update:visible', false)
  emit('highlight-state', null)
}

// 跳转到指定状态
const goToState = (index: number) => {
  selectedStateIndex.value = index
}

// 播放动画
const isPlaying = ref(false)
let playInterval: ReturnType<typeof setInterval> | null = null

const play = () => {
  if (isPlaying.value) {
    stop()
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
    class="fixed left-2/3 -translate-x-1/2 bottom-8 z-40"
  >
    <div class="bg-white rounded-xl shadow-2xl border border-slate-200 p-4 w-[600px]">
      <!-- Timeline -->
      <div>
        <div class="flex items-center justify-between mb-2">
          <div class="flex items-center gap-2">
            <span class="text-sm font-bold text-slate-700">State Sequence</span>
            <span class="px-2 py-0.5 bg-indigo-100 text-indigo-600 text-xs rounded-full">
              {{ selectedStateIndex + 1 }} / {{ totalStates }}
            </span>
          </div>
          <div class="flex items-center gap-2">
            <button
              @click="play"
              class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1"
              :class="isPlaying 
                ? 'bg-indigo-500 text-white' 
                : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
            >
              <span class="material-symbols-outlined text-sm">{{ isPlaying ? 'stop' : 'play_arrow' }}</span>
              {{ isPlaying ? 'Stop' : 'Play' }}
            </button>
            <button
              @click="close"
              class="p-1.5 hover:bg-slate-100 rounded-lg transition-colors"
            >
              <span class="material-symbols-outlined text-slate-500">close</span>
            </button>
          </div>
        </div>
        
        <!-- 时间轴线 -->
        <div class="relative h-8 px-2">
          <div class="absolute top-1/2 left-2 right-2 h-2 bg-slate-200 rounded"></div>
          <!-- 进度条 -->
          <div 
            v-if="selectedStateIndex < totalStates - 1"
            class="absolute top-1/2 h-2 bg-indigo-500 rounded transition-all duration-300"
            :style="{ 
              left: totalStates > 1 ? `${(selectedStateIndex / (totalStates - 1)) * 100}%` : '0%',
              width: totalStates > 1 ? `${(1 / (totalStates - 1)) * 100}%` : '100%',
              transform: 'translateY(-50%)'
            }"
          ></div>
          
          <!-- 状态节点 -->
          <div class="absolute top-1/2 left-2 right-2 flex justify-between items-center -translate-y-1/2">
            <button
              v-for="(_, index) in states"
              :key="index"
              @click="goToState(index); highlightState()"
              class="w-6 h-6 rounded-full border-3 transition-all flex items-center justify-center relative z-10"
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
</template>

<style scoped>
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
  font-variation-settings: 'FILL' 0, 'wght' 400, 'GRAD' 0, 'opsz' 24;
}
</style>
