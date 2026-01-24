<script setup lang="ts">
import {ref, watch, computed} from 'vue'
import {useI18n} from 'vue-i18n'

import type {DeviceManifest} from '../types/device'
import type {DeviceEdge} from '../types/edge'
import type {Specification} from '../types/spec'
import {buildSpecText} from "../utils/spec"

const props = defineProps<{
  visible: boolean
  deviceName: string
  description: string
  label: string
  nodeId?: string
  manifest?: DeviceManifest | null
  rules?: DeviceEdge[]
  specs?: Specification[]
}>()

const emit = defineEmits<{
  (e: 'update:visible', value: boolean): void
  (e: 'delete'): void
}>()

const {t} = useI18n()

const innerVisible = ref(props.visible)

/* 同步 props -> local state */
watch(() => props.visible, v => (innerVisible.value = v))

const close = () => {
  innerVisible.value = false
  emit('update:visible', false)
}

const onDelete = () => emit('delete')

/* ---------- 核心展示数据提取 ---------- */

const manifest = computed<DeviceManifest | null>(() => props.manifest ?? null)

// 1. 基础信息数据
const basicInfo = computed(() => {
  const m = manifest.value
  if (!m) return {}

  return {
    name: m.Name,
    instanceName: props.label,
    description: m.Description || props.description || t('app.null'),
    initState: m.InitState,
    modes: m.Modes?.join(', '),
    impactedVariables: m.ImpactedVariables
  }
})

// 2. 变量列表 (合并 Internal 和 Impacted，并展示隐私/信任)
const variables = computed(() => {
  const m = manifest.value
  if (!m) return []
  const list: any[] = []

  // Internal Variables (完整对象)
  if (m.InternalVariables) {
    m.InternalVariables.forEach(iv => {
      // 智能格式化 Value 列：显示枚举值 或 数值范围
      let valDisplay = ''
      if (iv.Values && iv.Values.length) valDisplay = iv.Values.join(' / ')
      else if (iv.LowerBound !== undefined && iv.UpperBound !== undefined) valDisplay = `[${iv.LowerBound}, ${iv.UpperBound}]`

      list.push({
        name: iv.Name,
        range: valDisplay,
        trust: iv.Trust,
        privacy: iv.Privacy,
        type: 'Impacted'
      })
    })
  }

  // Impacted Variables (外部引用)
  if (m.ImpactedVariables) {
    m.ImpactedVariables.forEach(vName => {
      // 避免重复显示
      if (!list.some(item => item.name === vName)) {
        list.push({
          name: vName,
          range: '(External)',
          trust: '-',
          privacy: '-',
          type: 'Impacted'
        })
      }
    })
  }
  return list
})

// 3. 状态列表 (展示隐私、不变式)
const states = computed(() => {
  const m = manifest.value
  if (!m || !m.WorkingStates) return []
  return m.WorkingStates.map(s => ({
    name: s.Name,
    description: s.Description,
    invariant: s.Invariant,
    privacy: s.Privacy
  }))
})

// 生成设备ID（用于显示）
const deviceId = computed(() => {
  // 这里可以根据实际需求生成设备ID
  return Math.floor(Math.random() * 10000000) + 1000000
})

// 获取设备图标
const getDeviceIcon = (deviceName: string) => {
  // 根据设备类型返回对应的图标
  if (deviceName.toLowerCase().includes('sensor')) {
    return 'sensors'
  } else if (deviceName.toLowerCase().includes('light')) {
    return 'lightbulb'
  } else if (deviceName.toLowerCase().includes('switch')) {
    return 'toggle_on'
  }
  return 'devices'
}

// 获取设备相关的规约
const deviceSpecs = computed(() => {
  if (!props.specs || !props.nodeId) return []

  const currentDeviceId = props.nodeId // 使用正确的设备ID
  return props.specs
    .filter(spec => {
      // 检查单设备规约
      if (spec.deviceId === currentDeviceId) return true
      // 检查多设备规约
      if (spec.devices && spec.devices.some(d => d.deviceId === currentDeviceId)) return true
      return false
    })
    .map(spec => {
      let specType = 'Unknown'
      switch (spec.templateId) {
        case 'safety':
        case '1':
          specType = 'Safety'
          break
        case 'liveness':
        case '2':
          specType = 'Liveness'
          break
        case 'fairness':
        case '3':
          specType = 'Fairness'
          break
      }

      // 处理设备信息显示
      let deviceInfo = ''
      if (spec.devices && spec.devices.length > 0) {
        const deviceLabels = spec.devices.map(d => d.deviceLabel || d.deviceId).join(', ')
        deviceInfo = ` (${deviceLabels})`
      } else if (spec.deviceId) {
        deviceInfo = ` (${spec.deviceLabel || spec.deviceId})`
      } else {
        deviceInfo = ' (Global)'
      }

      return {
        id: spec.id,
        name: `${specType} Property${deviceInfo}`,
        formula: spec.formula || 'No formula defined',
        status: 'Active'
      }
    })
})
</script>

<template>
  <!-- 自定义模态框 -->
  <teleport to="body">
    <transition name="modal-fade" appear>
      <div v-if="innerVisible" class="fixed inset-0 z-50 flex items-center justify-center p-4 bg-black/50 backdrop-blur-sm">
        <transition name="modal-scale" appear>
          <div class="bg-white w-full max-w-3xl rounded-2xl shadow-2xl overflow-hidden flex flex-col max-h-[90vh]">

            <!-- Header -->
            <div class="px-8 py-6 border-b border-slate-100 flex justify-between items-center bg-white sticky top-0 z-10">
              <div class="flex items-center gap-4">
                <div class="w-12 h-12 rounded-xl bg-blue-50 flex items-center justify-center text-primary">
                  <span class="material-icons-round text-3xl">{{ getDeviceIcon(deviceName) }}</span>
                </div>
                <div>
                  <h1 class="text-xl font-bold text-slate-900 leading-tight">{{ t('app.deviceInfo') || '设备信息' }}</h1>
                  <p class="text-sm text-slate-500">{{ deviceName || 'Sensor' }} • ID: {{ deviceId }}</p>
                </div>
              </div>
              <button @click="close" class="text-slate-400 hover:text-slate-600 transition-colors">
                <span class="material-icons-round">close</span>
              </button>
            </div>

            <!-- Body -->
            <div class="flex-1 overflow-y-auto custom-scrollbar px-8 py-6 space-y-10">
              <!-- Basic Info -->
              <section>
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceBasic') || '基本信息' }}</h2>
                </div>
                <div class="grid grid-cols-1 md:grid-cols-2 gap-x-12 gap-y-4 bg-slate-50 p-6 rounded-2xl">
                  <div class="flex flex-col gap-1">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.name') || '名称' }}</span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.name || deviceName }}</span>
                  </div>
                  <div class="flex flex-col gap-1">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.instanceName') || '实例名称' }}</span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.instanceName || '1' }}</span>
                  </div>
                  <div class="flex flex-col gap-1 md:col-span-2">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.description') || '描述' }}</span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.description }}</span>
                  </div>
                  <div class="flex flex-col gap-1">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.initState') || '初始状态' }}</span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.initState || 'Working' }}</span>
                  </div>
                  <div class="flex flex-col gap-1">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.modes') || '模式' }}</span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.modes || 'Working, Off' }}</span>
                  </div>
                  <div v-if="basicInfo.impactedVariables && basicInfo.impactedVariables.length" class="flex flex-col gap-1 md:col-span-2">
                    <span class="text-xs font-medium text-slate-400 uppercase tracking-wider">{{ t('app.impactedVariables') || '受影响变量' }}</span>
                    <div class="flex flex-wrap gap-2 mt-1">
                      <span v-for="variable in basicInfo.impactedVariables" :key="variable"
                            class="px-2 py-1 bg-white text-[11px] font-medium text-slate-600 rounded border border-slate-200">
                        {{ variable }}
                      </span>
                    </div>
                  </div>
                </div>
              </section>

              <!-- Variables -->
              <section v-if="variables.length">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceVariables') || '变量' }}</h2>
                </div>
                <div class="overflow-hidden border border-slate-100 rounded-xl">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-slate-50">
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.name') || '名称' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.range') || '范围' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.trust') || '可信度' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.type') || '类型' }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100">
                      <tr v-for="(v, idx) in variables" :key="idx" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ v.name }}</td>
                        <td class="px-4 py-3 text-sm text-slate-500">{{ v.range }}</td>
                        <td class="px-4 py-3 text-sm text-slate-500">{{ v.trust || '-' }}</td>
                        <td class="px-4 py-3">
                          <span class="inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium bg-emerald-100 text-emerald-800">
                            {{ v.type }}
                          </span>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- States -->
              <section>
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceStates') || '状态' }}</h2>
                </div>
                <div class="overflow-hidden border border-slate-100 rounded-xl">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-slate-50">
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.name') || '名称' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.description') || '描述' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.invariant') || '不变性' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">{{ t('app.privacy') || '隐私度' }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100">
                      <tr v-if="states.length === 0">
                        <td class="px-4 py-8 text-center text-slate-400 text-sm italic" colspan="4">
                          {{ t('app.noData') || '暂无状态数据' }}
                        </td>
                      </tr>
                      <tr v-for="(s, idx) in states" :key="idx" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ s.name }}</td>
                        <td class="px-4 py-3 text-sm text-slate-500">{{ s.description || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-500">{{ s.invariant || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-500">{{ s.privacy || '-' }}</td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- Specifications Section -->
              <section v-if="deviceSpecs.length > 0" class="border-t border-dashed border-slate-200 pt-8">
                <div class="flex items-center gap-2 mb-6">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceSpecs') || '设备规约' }}</h2>
                </div>
                <div class="space-y-4">
                  <div
                    v-for="spec in deviceSpecs"
                    :key="spec.id"
                    class="bg-red-50/50 border border-red-100 rounded-xl p-4"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex items-center gap-2">
                        <div class="w-2 h-2 bg-red-500 rounded-full"></div>
                        <span class="text-sm font-semibold text-red-700">{{ spec.name }}</span>
                      </div>
                      <span class="text-xs font-medium text-red-600 bg-red-100 px-2 py-1 rounded">
                        {{ spec.status }}
                      </span>
                    </div>
                    <div class="text-xs text-slate-600 leading-relaxed font-mono bg-white p-3 rounded border">
                      {{ spec.formula }}
                    </div>
                  </div>
                </div>
              </section>
            </div>

            <!-- Footer -->
            <div class="px-8 py-6 border-t border-slate-100 bg-slate-50 flex justify-end items-center gap-3">
                <button @click="close" class="px-6 py-2.5 text-sm font-semibold text-slate-600 hover:bg-slate-200 rounded-xl transition-all">
                  关闭
                </button>
              <button @click="onDelete" class="px-5 py-2.5 text-sm font-semibold text-rose-500 hover:text-white border border-rose-200 hover:bg-rose-500 rounded-xl transition-all flex items-center gap-2">
                <span class="material-icons-round text-lg">delete_outline</span>
                {{ t('app.deleteDevice') || '删除设备' }}
              </button>
            </div>
          </div>
        </transition>
      </div>
    </transition>
  </teleport>
</template>

<style scoped>
/* Modal Transitions */
.modal-fade-enter-active,
.modal-fade-leave-active {
  transition: opacity 0.3s ease;
}

.modal-fade-enter-from,
.modal-fade-leave-to {
  opacity: 0;
}

.modal-scale-enter-active,
.modal-scale-leave-active {
  transition: transform 0.3s ease, opacity 0.3s ease;
}

.modal-scale-enter-from,
.modal-scale-leave-to {
  opacity: 0;
  transform: scale(0.95);
}

/* Custom Scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 6px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: transparent;
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: #cbd5e1;
  border-radius: 10px;
}

.dark .custom-scrollbar::-webkit-scrollbar-thumb {
  background: #475569;
}
</style>