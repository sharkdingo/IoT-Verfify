<script setup lang="ts">
import { ref, computed, watch, onBeforeUnmount } from 'vue'
import type { Trace } from '../types/verify'

const props = defineProps<{
  traces: Trace[]
  visible: boolean
}>()

const emit = defineEmits<{
  'update:visible': [value: boolean]
  'highlight-trace': [trace: Trace | null]
}>()

// 格式化规约为易读格式
const formatSpec = (specJson: string): string => {
  try {
    const spec = JSON.parse(specJson)
    
    // 模板标签
    const templateLabel = spec.templateLabel || 'Spec'
    
    //: Always □(condition)
    if (spec.templateId === '1' && spec.aConditions) {
      const conditions = spec.aConditions.map((c: any) => {
        const device = c.deviceId || c.deviceLabel || 'device'
        const key = c.key || ''
        const relation = formatRelation(c.relation)
        const value = c.value ? `"${c.value}"` : ''
        return `${device}_${key} ${relation} ${value}`.trim()
      }).join(' ∧ ')
      return `□(${conditions})`
    }
    
    // Response: □(A → ◇B)
    if (spec.templateId === '5') {
      const ifPart = spec.ifConditions?.map((c: any) => 
        `${c.deviceId}_${c.key} ${formatRelation(c.relation)} "${c.value}"`
      ).join(' ∧ ') || ''
      const thenPart = spec.thenConditions?.map((c: any) => 
        `${c.deviceId}_${c.key} = "${c.value}"`
      ).join(' ∧ ') || ''
      return `□(${ifPart} → ◇(${thenPart}))`
    }
    
    // 其他情况返回原始模板标签
    return templateLabel
  } catch {
    return specJson
  }
}

// 格式化关系运算符
const formatRelation = (relation: string): string => {
  const relations: Record<string, string> = {
    '=': '=',
    '!=': '≠',
    '>': '>',
    '<': '<',
    '>=': '≥',
    '<=': '≤',
    'in': '∈',
    'not_in': '∉'
  }
  return relations[relation] || relation
}

// 当前规约的格式化显示
const formattedSpec = computed(() => {
  if (!currentTrace.value?.violatedSpecJson) return ''
  return formatSpec(currentTrace.value.violatedSpecJson)
})

// 当前选中的 trace
const selectedTraceIndex = ref(0)

// 当前选中的状态
const selectedStateIndex = ref(0)

// 当前选中的 trace
const currentTrace = computed(() => {
  return props.traces[selectedTraceIndex.value] || null
})

// 当前状态
const currentState = computed(() => {
  if (!currentTrace.value?.states) return null
  return currentTrace.value.states[selectedStateIndex.value] || null
})

// 所有状态数量
const totalStates = computed(() => {
  return currentTrace.value?.states?.length || 0
})

// 关闭对话框
const close = () => {
  emit('update:visible', false)
  emit('highlight-trace', null)
}

// 高亮显示反例路径
const highlightTrace = () => {
  emit('highlight-trace', currentTrace.value)
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
      selectedStateIndex.value = 0
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

// 获取设备状态颜色
const getStateColor = (state: string): string => {
  const stateColors: Record<string, string> = {
    'heat': 'bg-red-500',
    'cool': 'bg-blue-500',
    'off': 'bg-gray-400',
    'on': 'bg-green-500',
    'auto': 'bg-purple-500',
    'dry': 'bg-yellow-500',
    'fanOnly': 'bg-cyan-500',
    'heatClean': 'bg-orange-500',
    'dryClean': 'bg-amber-500',
    'coolClean': 'bg-sky-500'
  }
  return stateColors[state?.toLowerCase()] || 'bg-slate-500'
}

// 监听对话框关闭，停止播放并清除高亮
watch(() => props.visible, (newVal) => {
  if (!newVal) {
    stop()
    emit('highlight-trace', null)
  }
})

onBeforeUnmount(() => {
  stop()
})
</script>

<template>
  <div v-if="visible" class="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50" @click="close">
    <div class="bg-white rounded-xl w-[900px] max-w-[95vw] shadow-2xl max-h-[85vh] flex flex-col" @click.stop>
      <!-- 头部 -->
      <div class="flex items-center justify-between px-6 py-4 border-b border-slate-200 bg-gradient-to-r from-red-500 to-red-600 rounded-t-xl">
        <div class="flex items-center gap-3">
          <div class="w-10 h-10 bg-white/20 rounded-lg flex items-center justify-center">
            <span class="material-symbols-outlined text-white">warning</span>
          </div>
          <div>
            <h3 class="text-lg font-bold text-white">Counterexample Trace</h3>
            <p class="text-sm text-white/80">反例路径可视化</p>
          </div>
        </div>
        <button @click="close" class="p-2 hover:bg-white/20 rounded-lg transition-colors">
          <span class="material-symbols-outlined text-white">close</span>
        </button>
      </div>

      <!-- 内容区 -->
      <div class="flex-1 overflow-hidden flex min-h-[500px]">
        <!-- 左侧：Trace 列表 -->
        <div class="w-64 border-r border-slate-200 p-4 overflow-y-auto bg-slate-50">
          <h4 class="text-xs font-bold text-slate-500 uppercase mb-3">Violations ({{ traces.length }})</h4>
          <div class="space-y-2">
            <button
              v-for="(trace, index) in traces"
              :key="trace.id"
              @click="selectedTraceIndex = index; selectedStateIndex = 0; highlightTrace()"
              class="w-full p-3 rounded-lg text-left transition-all"
              :class="selectedTraceIndex === index 
                ? 'bg-red-50 border-2 border-red-500 shadow-md' 
                : 'bg-white border border-slate-200 hover:border-red-300 hover:shadow-sm'"
            >
              <div class="flex items-center gap-2 mb-1">
                <span 
                  class="w-6 h-6 rounded flex items-center justify-center"
                  :class="selectedTraceIndex === index ? 'bg-red-500 text-white' : 'bg-slate-200 text-slate-600'"
                >
                  <span class="text-xs font-bold">{{ index + 1 }}</span>
                </span>
                <span class="text-sm font-bold text-slate-700 truncate">{{ trace.violatedSpecId }}</span>
              </div>
              <div class="text-xs text-slate-500 pl-8">
                {{ trace.states?.length || 0 }} states
              </div>
            </button>
          </div>
        </div>

        <!-- 右侧：状态序列 -->
        <div class="flex-1 flex flex-col">
          <!-- 时间轴 -->
          <div class="p-4 border-b border-slate-200 bg-white">
            <div class="flex items-center justify-between mb-3">
              <div class="flex items-center gap-2">
                <span class="text-sm font-bold text-slate-700">State Sequence</span>
                <span class="px-2 py-0.5 bg-red-100 text-red-600 text-xs rounded-full">
                  {{ selectedStateIndex + 1 }} / {{ totalStates }}
                </span>
              </div>
              <div class="flex items-center gap-2">
                <button
                  @click="play"
                  class="px-3 py-1.5 rounded-lg text-xs font-medium transition-colors flex items-center gap-1"
                  :class="isPlaying 
                    ? 'bg-red-500 text-white' 
                    : 'bg-slate-100 text-slate-700 hover:bg-slate-200'"
                >
                  <span class="material-symbols-outlined text-sm">{{ isPlaying ? 'stop' : 'play_arrow' }}</span>
                  {{ isPlaying ? 'Stop' : 'Play' }}
                </button>
              </div>
            </div>
            
            <!-- 时间轴线 -->
            <div class="relative h-14 px-2">
              <div class="absolute top-1/2 left-4 right-4 h-2 bg-slate-200 rounded"></div>
              <div 
                class="absolute top-1/2 h-2 bg-red-500 rounded transition-all duration-300"
                :style="{ 
                  left: totalStates > 1 ? `${(selectedStateIndex / (totalStates - 1)) * 100}%` : '0%',
                  width: totalStates > 1 ? `${(1 / (totalStates - 1)) * 100}%` : '100%',
                  transform: 'translateY(-50%)'
                }"
              ></div>
              
              <!-- 状态节点 -->
              <div class="absolute top-1/2 left-4 right-4 flex justify-between items-center -translate-y-1/2">
                <button
                  v-for="(_, index) in currentTrace?.states || []"
                  :key="index"
                  @click="goToState(index); highlightTrace()"
                  class="w-8 h-8 rounded-full border-4 transition-all flex items-center justify-center relative z-10 shadow-sm"
                  :class="index === selectedStateIndex 
                    ? 'bg-red-500 border-red-500 scale-125 shadow-lg shadow-red-500/50' 
                    : index < selectedStateIndex 
                      ? 'bg-green-500 border-green-500' 
                      : 'bg-white border-slate-300 hover:border-red-300'"
                >
                  <span 
                    v-if="index === selectedStateIndex" 
                    class="text-white text-xs font-bold"
                  >
                    ★
                  </span>
                  <span 
                    v-else 
                    class="text-slate-500 text-[8px] font-medium"
                  >
                    {{ index + 1 }}
                  </span>
                </button>
              </div>
            </div>
          </div>

          <!-- 状态详情 -->
          <div class="flex-1 p-4 overflow-y-auto bg-slate-50">
            <div v-if="currentState" class="space-y-4">
              <!-- 当前状态标题 -->
              <div class="flex items-center justify-between">
                <div class="flex items-center gap-2">
                  <span class="text-lg font-bold text-slate-800">State {{ selectedStateIndex + 1 }}</span>
                  <span 
                    v-if="selectedStateIndex === totalStates - 1"
                    class="px-2 py-0.5 bg-red-500 text-white text-xs rounded-full animate-pulse"
                  >
                    Violation Point!
                  </span>
                </div>
                <span class="text-sm text-slate-500">
                  {{ selectedStateIndex === 0 ? 'Initial State' : selectedStateIndex === totalStates - 1 ? 'Violation State' : 'Intermediate State' }}
                </span>
              </div>

              <!-- 违反的规约详情 -->
              <div v-if="selectedStateIndex === totalStates - 1 && formattedSpec" class="mt-3 p-3 bg-red-50 border border-red-200 rounded-lg">
                <div class="text-xs font-semibold text-red-600 mb-1 uppercase">Violated Specification</div>
                <div class="text-sm text-slate-800 font-mono bg-white p-3 rounded border border-red-200">
                  {{ formattedSpec }}
                </div>
              </div>

              <!-- 设备状态列表 -->
              <div class="grid grid-cols-1 gap-3">
                <div
                  v-for="device in currentState.devices"
                  :key="device.deviceId"
                  class="p-4 rounded-lg border-2 transition-all"
                  :class="selectedStateIndex === totalStates - 1 
                    ? 'bg-red-50 border-red-300 shadow-md' 
                    : 'bg-white border-slate-200'"
                >
                  <div class="flex items-center justify-between mb-3">
                    <div class="flex items-center gap-2">
                      <div class="w-8 h-8 bg-slate-100 rounded-lg flex items-center justify-center">
                        <span class="material-symbols-outlined text-slate-600 text-lg">devices</span>
                      </div>
                      <div>
                        <span class="text-sm font-bold text-slate-800">{{ device.deviceLabel }}</span>
                        <span class="text-xs text-slate-400 block">{{ device.templateName }}</span>
                      </div>
                    </div>
                    <span 
                      class="px-3 py-1.5 rounded-lg text-xs font-bold text-white shadow-sm"
                      :class="getStateColor(device.state || device.newState)"
                    >
                      {{ device.state || device.newState }}
                    </span>
                  </div>

                  <!-- 变量 -->
                  <div v-if="device.variables && device.variables.length > 0" class="mt-3 pt-3 border-t border-slate-200">
                    <div class="text-xs font-semibold text-slate-500 mb-2 uppercase">Variables</div>
                    <div class="flex flex-wrap gap-2">
                      <span
                        v-for="variable in device.variables"
                        :key="variable.name"
                        class="px-3 py-1.5 bg-slate-100 border border-slate-200 rounded-lg text-xs flex items-center gap-2"
                      >
                        <span class="text-slate-500 font-medium">{{ variable.name }}:</span>
                        <span class="font-bold text-slate-800">{{ variable.value }}</span>
                      </span>
                    </div>
                  </div>

                  <!-- 信任状态 -->
                  <div v-if="device.trustPrivacy && device.trustPrivacy.length > 0" class="mt-3 pt-3 border-t border-slate-200">
                    <div class="text-xs font-semibold text-slate-500 mb-2 uppercase">Trust & Privacy</div>
                    <div class="flex flex-wrap gap-2">
                      <span
                        v-for="tp in device.trustPrivacy"
                        :key="tp.name"
                        class="px-3 py-1.5 rounded-lg text-xs flex items-center gap-2"
                        :class="tp.trust ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'"
                      >
                        <span class="material-symbols-outlined text-sm">
                          {{ tp.trust ? 'verified' : 'warning' }}
                        </span>
                        {{ tp.name }}: {{ tp.trust ? 'trusted' : 'untrusted' }}
                      </span>
                    </div>
                  </div>
                </div>
              </div>

              <!-- 高亮按钮 -->
              <div class="pt-4 border-t border-slate-200">
                <button
                  @click="highlightTrace"
                  class="w-full py-3 bg-gradient-to-r from-red-500 to-red-600 hover:from-red-600 hover:to-red-700 text-white rounded-lg text-sm font-bold transition-all shadow-md hover:shadow-lg flex items-center justify-center gap-2"
                >
                  <span class="material-symbols-outlined">highlight</span>
                  Highlight on Canvas
                </button>
              </div>
            </div>

            <!-- 空状态 -->
            <div v-else class="flex items-center justify-center h-full text-slate-400">
              <div class="text-center">
                <span class="material-symbols-outlined text-4xl mb-2">info</span>
                <p>No state data available</p>
              </div>
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
