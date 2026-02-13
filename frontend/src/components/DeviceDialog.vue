<script setup lang="ts">
import {ref, watch, computed} from 'vue'
import {useI18n} from 'vue-i18n'

import type {DeviceManifest} from '../types/device'
import type {DeviceEdge} from '../types/edge'
import type {Specification, SpecCondition} from '../types/spec'
import {buildSpecText} from "../utils/spec"
import {specTemplateDetails} from '../assets/config/specTemplates'

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

// 从条件生成LTL公式
const generateFormulaFromConditions = (spec: Specification): string => {
  const template = specTemplateDetails.find(t => t.id === spec.templateId)
  if (!template) return spec.templateLabel || 'Unknown'

  // 将条件转换为字符串
  const conditionsToString = (conditions: SpecCondition[]) => {
    return conditions
      .filter(c => c && c.deviceId && c.key)
      .map(c => {
        const deviceName = (c.deviceLabel || c.deviceId).toLowerCase().replace(/\s+/g, '_')
        const key = c.key
        const relation = c.relation === '!=' ? '≠' : c.relation
        const value = c.value ? ` ${relation} "${c.value}"` : ''
        return `${deviceName}_${key}${value}`
      })
      .join(' ∧ ')
  }

  // 根据模板类型生成公式
  switch (template.type) {
    case 'always':
      const aStr = conditionsToString(spec.aConditions || [])
      return aStr ? `□(${aStr})` : '□A'
    case 'eventually':
      const evA = conditionsToString(spec.aConditions || [])
      return evA ? `◇(${evA})` : '◇A'
    case 'never':
      const neverA = conditionsToString(spec.aConditions || [])
      return neverA ? `□¬(${neverA})` : '□¬A'
    case 'immediate':
      const ifStr = conditionsToString(spec.ifConditions || [])
      const thenStr = conditionsToString(spec.thenConditions || [])
      if (ifStr && thenStr) {
        return `□((${ifStr}) → (${thenStr}))`
      } else if (ifStr) {
        return `□((${ifStr}) → B)`
      }
      return '□(A → B)'
    case 'response':
      const respIf = conditionsToString(spec.ifConditions || [])
      const respThen = conditionsToString(spec.thenConditions || [])
      if (respIf && respThen) {
        return `□((${respIf}) → ◇(${respThen}))`
      } else if (respIf) {
        return `□((${respIf}) → ◇B)`
      }
      return '□(A → ◇B)'
    case 'persistence':
      const persIf = conditionsToString(spec.ifConditions || [])
      const persThen = conditionsToString(spec.thenConditions || [])
      if (persIf && persThen) {
        return `□((${persIf}) → □(${persThen}))`
      } else if (persIf) {
        return `□((${persIf}) → □B)`
      }
      return '□(A → □B)'
    case 'safety':
      const safeIf = conditionsToString(spec.ifConditions || [])
      const safeThen = conditionsToString(spec.thenConditions || [])
      if (safeIf && safeThen) {
        return `□((${safeIf}) → ¬(${safeThen}))`
      } else if (safeIf) {
        return `□((${safeIf}) → ¬A)`
      }
      return '□(untrusted → ¬A)'
    default:
      return spec.templateLabel || 'Unknown'
  }
}

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

// 4. API列表
const apis = computed(() => {
  const m = manifest.value
  if (!m || !m.APIs) return []
  return m.APIs.map(api => ({
    name: api.Name,
    description: api.Description || '',
    startState: api.StartState,
    endState: api.EndState,
    trigger: api.Trigger || 'user',
    signal: api.Signal || false
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
  if (!props.specs || !props.nodeId) {
    return []
  }

  const currentDeviceId = props.nodeId // 使用正确的设备ID
  
  // 检查条件中是否包含该设备
  const checkConditionsForDevice = (spec: Specification) => {
    const allConditions = [
      ...(spec.aConditions || []),
      ...(spec.ifConditions || []),
      ...(spec.thenConditions || [])
    ]
    return allConditions.some(cond => cond && cond.deviceId === currentDeviceId)
  }
  
  return props.specs
    .filter(spec => {
      // 检查单设备规约
      if (spec.deviceId === currentDeviceId) return true
      // 检查多设备规约
      if (spec.devices && Array.isArray(spec.devices) && spec.devices.some(d => d && d.deviceId === currentDeviceId)) return true
      // 检查条件中是否包含该设备
      if (checkConditionsForDevice(spec)) return true
      return false
    })
    .map(spec => {
      // 使用templateLabel或根据templateId映射
      let specType = spec.templateLabel || 'Unknown'
      let specTypeColor = 'slate'
      
      // 根据templateId设置颜色和类型
      switch (spec.templateId) {
        case 'safety':
        case '1':
          specType = spec.templateLabel || 'Safety'
          specTypeColor = 'red'
          break
        case 'liveness':
        case '2':
          specType = spec.templateLabel || 'Liveness'
          specTypeColor = 'blue'
          break
        case 'fairness':
        case '3':
          specType = spec.templateLabel || 'Fairness'
          specTypeColor = 'green'
          break
        case 'always':
        case '4':
          specType = spec.templateLabel || 'Always'
          specTypeColor = 'purple'
          break
        case 'eventually':
        case '5':
          specType = spec.templateLabel || 'Eventually'
          specTypeColor = 'indigo'
          break
        case 'never':
        case '6':
          specType = spec.templateLabel || 'Never'
          specTypeColor = 'orange'
          break
        case 'immediate':
        case 'response':
        case 'persistence':
        case '7':
          specType = spec.templateLabel || 'Response'
          specTypeColor = 'teal'
          break
      }

      // 处理设备信息显示
      let deviceInfo = ''
      if (spec.devices && spec.devices.length > 0) {
        const deviceLabels = spec.devices.map(d => d.deviceLabel || d.deviceId).join(', ')
        deviceInfo = deviceLabels
      } else if (spec.deviceId) {
        deviceInfo = spec.deviceLabel || spec.deviceId
      } else {
        deviceInfo = 'Global'
      }

      // 生成公式：如果formula不存在，从条件生成
      let formula = spec.formula
      if (!formula || formula === 'No formula defined') {
        formula = generateFormulaFromConditions(spec)
      }

      return {
        id: spec.id,
        type: specType,
        typeColor: 'red', // 强制使用红色
        formula: formula,
        devices: deviceInfo,
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
          <div class="bg-white w-full max-w-4xl rounded-2xl shadow-2xl overflow-hidden flex flex-col max-h-[90vh]">

            <!-- Header -->
            <div class="px-8 py-6 border-b border-slate-200 bg-gradient-to-r from-white to-slate-50/50 flex justify-between items-center sticky top-0 z-10 shadow-sm">
              <div class="flex items-center gap-4">
                <div class="w-14 h-14 rounded-xl bg-gradient-to-br from-blue-50 to-blue-100 border-2 border-blue-200 flex items-center justify-center shadow-lg">
                  <span class="material-icons-round text-3xl text-blue-600">{{ getDeviceIcon(deviceName) }}</span>
                </div>
                <div>
                  <h1 class="text-xl font-bold text-slate-900 leading-tight">{{ t('app.deviceInfo') || 'Device Details' }}</h1>
                  <div class="flex items-center gap-2 mt-1">
                    <p class="text-sm text-slate-500 font-medium">{{ label }}</p>
                    <span class="text-slate-300">•</span>
                    <p class="text-sm text-slate-500 font-mono bg-slate-100 px-1.5 py-0.5 rounded text-xs">ID: {{ nodeId?.substring(0, 8) }}</p>
                  </div>
                </div>
              </div>
              <button @click="close" class="p-2 text-slate-400 hover:text-slate-600 hover:bg-slate-100 rounded-lg transition-all">
                <span class="material-icons-round text-xl">close</span>
              </button>
            </div>

            <!-- Body -->
            <div class="flex-1 overflow-y-auto custom-scrollbar px-8 py-6 space-y-8">
              <!-- Basic Info -->
              <section>
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceBasic') || 'Basic Information' }}</h2>
                </div>
                
                <!-- 基本信息表格 -->
                <div class="overflow-hidden border border-slate-200 rounded-xl bg-white shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-slate-50 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider w-1/3">Property</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-500 uppercase tracking-wider">Value</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100">
                      <!-- Template Name -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.name') || 'Template Name' }}</td>
                        <td class="px-4 py-3 text-sm font-bold text-slate-800">{{ basicInfo.name || deviceName }}</td>
                      </tr>
                      
                      <!-- Instance Name -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.instanceName') || 'Instance Name' }}</td>
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ basicInfo.instanceName || label }}</td>
                      </tr>

                      <!-- Modes -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.modes') || 'Modes' }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-1.5">
                            <span v-for="(mode, idx) in (basicInfo.modes || 'Working, Off').split(',')" :key="idx" 
                                  class="px-2 py-0.5 bg-slate-100 text-slate-600 text-xs rounded-md font-medium border border-slate-200">
                              {{ mode.trim() }}
                            </span>
                  </div>
                        </td>
                      </tr>

                      <!-- Initial State -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider">{{ t('app.initState') || 'Initial State' }}</td>
                        <td class="px-4 py-3">
                          <div class="flex items-center gap-2">
                            <span class="w-2 h-2 rounded-full bg-green-500 animate-pulse"></span>
                    <span class="text-sm font-medium text-slate-700">{{ basicInfo.initState || 'Working' }}</span>
                  </div>
                        </td>
                      </tr>

                      <!-- Description -->
                      <tr class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.description') || 'Description' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 leading-relaxed">{{ basicInfo.description || '-' }}</td>
                      </tr>

                      <!-- Impacted Variables -->
                      <tr v-if="basicInfo.impactedVariables && basicInfo.impactedVariables.length" class="hover:bg-slate-50/50 transition-colors">
                        <td class="px-4 py-3 text-xs font-medium text-slate-500 uppercase tracking-wider align-top">{{ t('app.impactedVariables') || 'Impacted Variables' }}</td>
                        <td class="px-4 py-3">
                          <div class="flex flex-wrap gap-2">
                      <span v-for="variable in basicInfo.impactedVariables" :key="variable"
                                  class="px-2.5 py-1 bg-blue-50 text-blue-700 text-xs font-medium rounded-md border border-blue-100">
                        {{ variable }}
                      </span>
                    </div>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- Variables -->
              <section v-if="variables.length">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-primary rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceVariables') || '变量' }}</h2>
                </div>
                <div class="overflow-hidden border border-slate-200 rounded-xl shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-gradient-to-r from-slate-50 to-slate-100 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.name') || 'Name' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.range') || 'Range/Values' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.trust') || 'Trust Level' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.type') || 'Type' }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100 bg-white">
                      <tr v-for="(v, idx) in variables" :key="idx" class="hover:bg-blue-50/30 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ v.name }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 font-mono">{{ v.range || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="v.trust === 'high' || v.trust === 'trusted' ? 'bg-green-100 text-green-700' : 
                                    v.trust === 'medium' ? 'bg-yellow-100 text-yellow-700' : 
                                    'bg-slate-100 text-slate-600'">
                            {{ v.trust || '-' }}
                          </span>
                        </td>
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
                <div class="overflow-hidden border border-slate-200 rounded-xl shadow-sm">
                  <table class="w-full text-left border-collapse">
                    <thead>
                      <tr class="bg-gradient-to-r from-slate-50 to-slate-100 border-b border-slate-200">
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.name') || 'Name' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.description') || 'Description' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.invariant') || 'Invariant' }}</th>
                        <th class="px-4 py-3 text-xs font-bold text-slate-600 uppercase tracking-wider">{{ t('app.privacy') || 'Privacy' }}</th>
                      </tr>
                    </thead>
                    <tbody class="divide-y divide-slate-100 bg-white">
                      <tr v-if="states.length === 0">
                        <td class="px-4 py-8 text-center text-slate-400 text-sm italic" colspan="4">
                          {{ t('app.noData') || '暂无状态数据' }}
                        </td>
                      </tr>
                      <tr v-for="(s, idx) in states" :key="idx" class="hover:bg-blue-50/30 transition-colors">
                        <td class="px-4 py-3 text-sm font-medium text-slate-700">{{ s.name }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">{{ s.description || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600 font-mono text-xs">{{ s.invariant || '-' }}</td>
                        <td class="px-4 py-3 text-sm text-slate-600">
                          <span class="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium"
                            :class="s.privacy === 'public' ? 'bg-blue-100 text-blue-700' : 
                                    s.privacy === 'private' ? 'bg-purple-100 text-purple-700' : 
                                    'bg-slate-100 text-slate-600'">
                            {{ s.privacy || '-' }}
                          </span>
                        </td>
                      </tr>
                    </tbody>
                  </table>
                </div>
              </section>

              <!-- APIs Section -->
              <section v-if="apis.length > 0">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-emerald-500 rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">{{ t('app.deviceApis') || 'API Interfaces' }}</h2>
                </div>
                <div class="grid grid-cols-1 md:grid-cols-2 gap-4">
                  <div
                    v-for="(api, idx) in apis"
                    :key="idx"
                    class="bg-white border border-slate-200 rounded-xl p-4 hover:shadow-md transition-all hover:border-emerald-200 group"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex items-center gap-2">
                        <div class="w-8 h-8 bg-emerald-50 rounded-lg flex items-center justify-center group-hover:bg-emerald-100 transition-colors">
                        <span class="material-icons-round text-emerald-600 text-lg">api</span>
                        </div>
                        <span class="text-sm font-bold text-slate-800">{{ api.name }}</span>
                      </div>
                      <span v-if="api.signal" class="text-[10px] px-1.5 py-0.5 bg-amber-100 text-amber-700 rounded font-medium border border-amber-200">
                        Signal
                      </span>
                    </div>
                    <p v-if="api.description" class="text-xs text-slate-600 mb-4 line-clamp-2">
                      {{ api.description }}
                    </p>
                    <div class="flex items-center gap-2 text-xs bg-slate-50 p-2 rounded-lg border border-slate-100">
                      <div class="flex items-center gap-1 text-slate-500">
                        <span class="material-icons-round text-sm font-bold">play_arrow</span>
                        <span class="font-medium text-slate-700">{{ api.startState }}</span>
                      </div>
                      <span class="text-slate-300">→</span>
                      <div class="flex items-center gap-1 text-slate-500">
                        <span class="material-icons-round text-sm font-bold">stop</span>
                        <span class="font-medium text-slate-700">{{ api.endState }}</span>
                      </div>
                      <div class="flex-1"></div>
                      <span class="text-[10px] text-slate-400 uppercase font-semibold tracking-wider">Trigger: {{ api.trigger }}</span>
                    </div>
                  </div>
                </div>
              </section>

              <!-- Specifications Section -->
              <section v-if="deviceSpecs.length > 0">
                <div class="flex items-center gap-2 mb-4">
                  <div class="w-1 h-5 bg-rose-500 rounded-full"></div>
                  <h2 class="text-lg font-semibold text-slate-800">Specifications</h2>
                </div>
                  <div v-if="deviceSpecs.length === 0" class="bg-slate-50 border border-slate-200 rounded-xl p-8 text-center">
                  <span class="material-icons-round text-slate-300 text-4xl mb-2 block">verified</span>
                    <p class="text-sm text-slate-500">{{ t('app.noSpecs') || 'No associated specifications' }}</p>
                </div>
                <div v-else class="space-y-3">
                  <div
                    v-for="spec in deviceSpecs"
                    :key="spec.id"
                    class="bg-white border border-slate-200 rounded-xl p-4 transition-all hover:shadow-md hover:border-rose-200"
                  >
                    <div class="flex items-start justify-between mb-3">
                      <div class="flex items-center gap-2 flex-1">
                        <div class="w-8 h-8 bg-rose-50 rounded-lg flex items-center justify-center">
                          <span class="material-icons-round text-rose-500 text-lg">verified</span>
                        </div>
                        <div class="flex-1 min-w-0">
                          <span class="text-sm font-bold block truncate text-slate-800">{{ spec.type }}</span>
                          <span class="text-xs text-slate-500 mt-0.5 block truncate">
                            <span class="font-medium text-slate-400">Target:</span> {{ spec.devices }}
                          </span>
                        </div>
                      </div>
                    </div>
                    <div class="bg-slate-50 rounded-lg p-3 border border-slate-100">
                      <p class="text-[11px] text-slate-400 uppercase font-bold tracking-wider mb-1">LTL Formula</p>
                      <div class="text-xs text-slate-700 leading-relaxed font-mono break-all">
                      {{ spec.formula }}
                      </div>
                    </div>
                  </div>
                </div>
              </section>
            </div>

            <!-- Footer -->
            <div class="px-8 py-5 border-t border-slate-200 bg-gradient-to-r from-slate-50 to-white flex justify-end items-center gap-3">
                <button @click="close" class="px-6 py-2.5 text-sm font-semibold text-slate-700 bg-white hover:bg-slate-200 hover:text-slate-900 rounded-lg transition-all shadow-sm border border-slate-200">
                  关闭
                </button>
              <button @click="onDelete" class="px-5 py-2.5 text-sm font-semibold text-rose-900 bg-rose-100 hover:bg-rose-200 rounded-lg transition-all flex items-center gap-2 border border-rose-200">
                <span class="material-icons-round text-lg text-rose-600">delete_outline</span>
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