<script setup lang="ts">
import { reactive, computed, watch } from 'vue'
import { ElMessage } from 'element-plus'
import type { DeviceNode } from '../types/node'
import type { RuleForm } from '../types/rule'

// Props
interface Props {
  modelValue: boolean
  nodes: DeviceNode[]
  deviceTemplates: any[]
}

const props = withDefaults(defineProps<Props>(), {
  modelValue: false,
  nodes: () => [],
  deviceTemplates: () => []
})

// 过滤掉内部变量节点（只保留真实设备）
const deviceNodes = computed(() => {
  return (props.nodes || []).filter((node: DeviceNode) => !node.templateName?.startsWith('variable_'))
})

// Emits
const emit = defineEmits<{
  'update:modelValue': [value: boolean]
  'save-rule': [rule: RuleForm]
}>()

// Rule data
const ruleData = reactive<RuleForm>({
  id: '',
  name: '',
  sources: [],
  toId: '',
  toApi: ''
})

// Current source being added
const currentSource = reactive({
  // 来源类型：device=设备API，globalVariable=全局变量
  sourceType: '' as '' | 'device' | 'globalVariable',
  fromId: '',  // 设备ID（仅 sourceType=device 时需要）
  itemType: '',  // 'api' or 'variable'（仅 sourceType=device 时需要）
  fromApi: '',  // API名称或全局变量名称
  relation: '=',  // 条件关系（仅全局变量需要）
  value: ''  // 值（仅全局变量需要）
})

// 条件选项 - 使用 NuSMV 兼容的关系运算符
const relationOptions = [
  { label: '等于 (=)', value: '=' },
  { label: '不等于 (≠)', value: '!=' },
  { label: '大于 (>)', value: '>' },
  { label: '小于 (<)', value: '<' },
  { label: '大于等于 (≥)', value: '>=' },
  { label: '小于等于 (≤)', value: '<=' }
]

// 获取设备图标
const getDeviceApis = (templateName: string) => {
  if (!templateName) return []

  // 使用更宽松的匹配：支持大小写不敏感和空格变化
  const normalizedName = templateName.toLowerCase().trim()

  const template = props.deviceTemplates.find((t: any) => {
    const tplName = t.manifest?.Name || t.name || ''
    return tplName.toLowerCase().trim() === normalizedName ||
           normalizedName.includes(tplName.toLowerCase().trim()) ||
           tplName.toLowerCase().trim().includes(normalizedName)
  })

  if (template && template.manifest?.APIs) {
    return template.manifest.APIs.map((api: any) => ({
      name: api.Name || api.name || '',
      type: 'api'
    }))
  }

  // 如果没有找到模板，返回空数组
  return []
}

// 获取设备的变量列表（InternalVariables + ImpactedVariables）
const getDeviceVariables = (templateName: string) => {
  if (!templateName) return []

  // 使用更宽松的匹配：支持大小写不敏感和空格变化
  const normalizedName = templateName.toLowerCase().trim()

  const template = props.deviceTemplates.find((t: any) => {
    const tplName = t.manifest?.Name || t.name || ''
    return tplName.toLowerCase().trim() === normalizedName ||
           normalizedName.includes(tplName.toLowerCase().trim()) ||
           tplName.toLowerCase().trim().includes(normalizedName)
  })

  const variables: { name: string; type: string }[] = []

  // 只使用 InternalVariables（内部变量）
  if (template && template.manifest?.InternalVariables) {
    template.manifest.InternalVariables.forEach((v: any) => {
      if (v.Name || v.name) {
        variables.push({
          name: v.Name || v.name || '',
          type: 'variable'  // 统一使用 'variable' 类型
        })
      }
    })
  }

  // 如果没有找到模板，返回空数组
  return variables
}

// 合并 API 和变量列表
const getDeviceApiAndVariables = (templateName: string) => {
  return [...getDeviceApis(templateName), ...getDeviceVariables(templateName)]
}

const availableTargetApis = computed(() => {
  if (!ruleData.toId) return []
  const targetNode = props.nodes.find(n => n.id === ruleData.toId)
  if (!targetNode) return []

  // 只返回 API 名称（字符串数组）
  const apis = getDeviceApis(targetNode.templateName)
  return apis.map((a: any) => a.name)
})

const availableSourceApis = computed(() => {
  if (!currentSource.fromId) return []
  const sourceNode = props.nodes.find(n => n.id === currentSource.fromId)
  if (!sourceNode) return []

  return getDeviceApiAndVariables(sourceNode.templateName)
})

// 根据选择的类型过滤显示的项
const filteredSourceItems = computed(() => {
  if (!currentSource.itemType) return []
  return availableSourceApis.value.filter((item: any) => item.type === currentSource.itemType)
})

// 判断是否可以添加源（根据选择的项目类型决定是否需要条件/值）
const canAddSource = computed(() => {
  if (!currentSource.fromId || !currentSource.itemType || !currentSource.fromApi) {
    return false
  }
  // 如果是变量类型，relation 默认是 EQ，所以总是可以添加
  if (currentSource.itemType === 'variable') {
    return true  // 变量类型只需要选择设备和变量名，条件/值可选
  }
  // API 类型只需要选择设备和 API
  return true
})

// 判断是否可以自动添加源（变量类型需要 condition 和 value 都填写完）
const canAutoAddSource = computed(() => {
  if (!canAddSource.value) {
    return false
  }
  // 变量类型需要 condition 和 value 都填写完才能自动添加
  if (currentSource.itemType === 'variable') {
    return currentSource.relation && currentSource.value
  }
  // API 类型可以直接添加
  return true
})

// 自动添加源：按回车键或失去焦点时触发
const tryAutoAddSource = () => {
  if (canAutoAddSource.value) {
    addSource()
  }
}

// 监听 API 选择变化，自动添加（对于 API 类型）
watch(() => currentSource.fromApi, (newVal) => {
  if (newVal && currentSource.itemType === 'api' && canAddSource.value) {
    addSource()
  }
})

// Rule preview
const rulePreview = computed(() => {
  if (!ruleData.toId || ruleData.sources.length === 0) {
    return null
  }

  const targetNode = props.nodes.find(n => n.id === ruleData.toId)
  const sourceNodes = ruleData.sources.map(s => props.nodes.find(n => n.id === s.fromId)).filter(Boolean)

  return {
    sources: sourceNodes,
    sourceConditions: ruleData.sources,
    target: targetNode,
    action: ruleData.toApi
  }
})

// Methods
const addSource = () => {
  // 添加源设备及其条件
  if (currentSource.fromId && currentSource.itemType && currentSource.fromApi) {
    ruleData.sources.push({
      fromId: currentSource.fromId,
      fromApi: currentSource.fromApi,
      itemType: currentSource.itemType as 'api' | 'variable' | undefined,
      relation: currentSource.relation,
      value: currentSource.value
    })
    
    // 重置当前源选择
    currentSource.fromId = ''
    currentSource.itemType = ''
    currentSource.fromApi = ''
    currentSource.relation = '='
    currentSource.value = ''
  }
}

const removeSource = (index: number) => {
  ruleData.sources.splice(index, 1)
}

const handleSave = () => {
  if (!ruleData.toId || !ruleData.toApi || ruleData.sources.length === 0) {
    ElMessage.warning('Please complete all required fields')
    return
  }

  // Generate ID
  ruleData.id = 'rule_' + Date.now()

  emit('save-rule', { ...ruleData })
  handleClose()
}

const handleClose = () => {
  // Reset form
  ruleData.id = ''
  ruleData.name = ''
  ruleData.sources = []
  ruleData.toId = ''
  ruleData.toApi = ''
  currentSource.fromId = ''
  currentSource.itemType = ''
  currentSource.fromApi = ''
  currentSource.relation = '='
  currentSource.value = ''

  emit('update:modelValue', false)
}

// Helper functions for UI
const getDeviceIcon = (node: DeviceNode) => {
  const deviceType = (node.templateName || '').toLowerCase()
  
  // 传感器类
  if (deviceType.includes('sensor') || deviceType.includes('temperature') || deviceType.includes('humidity') || deviceType.includes('gas') || deviceType.includes('smoke') || deviceType.includes('motion') || deviceType.includes('soil') || deviceType.includes('illuminance') || deviceType.includes('door')) return 'sensors'
  
  // 温度/恒温器
  if (deviceType.includes('thermostat') || deviceType.includes('weather')) return 'thermostat'
  
  // 灯/照明
  if (deviceType.includes('light')) return 'lightbulb'
  
  // 开关
  if (deviceType.includes('switch')) return 'toggle_on'
  
  // 空调
  if (deviceType.includes('air conditioner') || deviceType.includes('ac')) return 'ac_unit'
  
  // 空气净化器/通风
  if (deviceType.includes('air purifier') || deviceType.includes('ventilator') || deviceType.includes('humidifier')) return 'air'
  
  // 窗帘/窗户
  if (deviceType.includes('window shade') || deviceType.includes('shade')) return 'blinds'
  if (deviceType.includes('window')) return 'window'
  
  // 门/车库门
  if (deviceType.includes('garage door')) return 'garage'
  if (deviceType.includes('door')) return 'door_front_door'
  
  // 摄像头
  if (deviceType.includes('camera')) return 'videocam'
  
  // 电视
  if (deviceType.includes('tv') || deviceType.includes('television')) return 'tv'
  
  // 手机
  if (deviceType.includes('phone') || deviceType.includes('mobile')) return 'smartphone'
  
  // 洗衣机/烘干机
  if (deviceType.includes('washer') || deviceType.includes('dryer')) return 'local_laundry_service'
  
  // 冰箱
  if (deviceType.includes('refrigerator') || deviceType.includes('fridge')) return 'kitchen'
  
  // 热水器
  if (deviceType.includes('water heater') || deviceType.includes('water')) return 'hot_tub'
  
  // 炊具/烤箱/咖啡机
  if (deviceType.includes('oven') || deviceType.includes('cooker') || deviceType.includes('cooktop')) return 'microwave'
  if (deviceType.includes('coffee')) return 'coffee'
  
  // 警报器
  if (deviceType.includes('alarm') || deviceType.includes('security')) return 'security'
  
  // 汽车
  if (deviceType.includes('car') || deviceType.includes('vehicle')) return 'directions_car'
  
  // 日历/时钟
  if (deviceType.includes('calendar')) return 'calendar_month'
  if (deviceType.includes('clock')) return 'schedule'
  
  // 社交媒体
  if (deviceType.includes('weibo') || deviceType.includes('twitter') || deviceType.includes('facebook') || deviceType.includes('email')) return 'alternate_email'
  
  // 泳池相关
  if (deviceType.includes('pool') || deviceType.includes('sprinkler')) return 'pool'
  
  // 油烟机
  if (deviceType.includes('range hood') || deviceType.includes('hood')) return 'kitchen'
  
  // 家庭模式
  if (deviceType.includes('home mode') || deviceType.includes('home')) return 'home'
  
  return 'devices_other'
}

const formatApiLabel = (api: string) => {
  return api.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase())
}
</script>

<template>
  <div
    v-show="modelValue"
    class="fixed inset-0 z-50 flex items-center justify-center bg-black/50 backdrop-blur-sm"
    @click.self="handleClose"
  >
    <div class="w-full max-w-2xl bg-white rounded-2xl overflow-hidden border border-slate-200 shadow-2xl">
      <!-- Header -->
      <div class="px-8 py-6 border-b border-slate-100 dark:border-slate-700">
        <div class="flex items-center justify-between mb-4">
          <h1 class="text-xl font-semibold text-slate-800 dark:text-white flex items-center gap-2">
            <span class="material-icons-round text-blue-500">auto_fix_high</span>
            Create New Rule
          </h1>
          <button
            @click="handleClose"
            class="p-2 rounded-full hover:bg-slate-100 dark:hover:bg-slate-700 text-slate-400 transition-colors"
          >
            <span class="material-icons-round">close</span>
          </button>
        </div>

        <!-- Rule Name Input -->
        <div class="space-y-2">
          <label class="text-sm font-semibold text-slate-600 dark:text-slate-400">Rule Name</label>
          <input
            v-model="ruleData.name"
            type="text"
            placeholder="Enter a name for this rule"
            class="w-full px-3 py-2 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 placeholder:text-slate-400"
          />
        </div>
      </div>

      <!-- Content -->
      <div class="p-8 space-y-8">
        <!-- IF (Trigger) Section -->
        <section class="space-y-4">
          <div class="flex items-center gap-2 mb-2">
            <span class="bg-blue-100 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400 text-xs font-bold px-2 py-1 rounded uppercase tracking-wider">
              IF (Trigger)
            </span>
            <h2 class="text-sm font-medium text-slate-500 dark:text-slate-400 uppercase tracking-wide">
              Source Devices
            </h2>
          </div>

          <!-- Add Source Form -->
          <div class="grid grid-cols-5 gap-3">
            <!-- 设备选择 -->
            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Device</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  {{ currentSource.fromId ? getDeviceIcon(deviceNodes.find(n => n.id === currentSource.fromId)!) : 'sensors' }}
                </span>
                <select
                  v-model="currentSource.fromId"
                  class="w-full pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm"
                >
                  <option value="" disabled hidden>Select</option>
                  <option v-for="node in deviceNodes" :key="node.id" :value="node.id">
                    {{ node.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 类型选择 (API / Variable) -->
            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Type</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  {{ currentSource.itemType === 'variable' ? 'tune' : (currentSource.itemType === 'api' ? 'bolt' : 'category') }}
                </span>
                <select
                  v-model="currentSource.itemType"
                  class="w-full pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="!currentSource.fromId"
                >
                  <option value="" disabled hidden>Select</option>
                  <option value="api">API</option>
                  <option value="variable">Variable</option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- API选择 - 仅选择 API 类型时显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'api'">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">API</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  bolt
                </span>
                <select
                  v-model="currentSource.fromApi"
                  class="w-full pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm"
                >
                  <option value="" disabled hidden>Select</option>
                  <option v-for="item in filteredSourceItems" :key="item.name" :value="item.name">
                    {{ formatApiLabel(item.name) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- Variable选择 - 仅选择 Variable 类型时显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'variable'">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Variable</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  tune
                </span>
                <select
                  v-model="currentSource.fromApi"
                  class="w-full pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm"
                >
                  <option value="" disabled hidden>Select</option>
                  <option v-for="item in filteredSourceItems" :key="item.name" :value="item.name">
                    {{ formatApiLabel(item.name) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 条件选择 - 仅变量显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'variable'">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Condition</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  compare_arrows
                </span>
                <select
                  v-model="currentSource.relation"
                  class="w-full pl-10 pr-8 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm"
                  :disabled="!currentSource.fromApi"
                >
                  <option v-for="rel in relationOptions" :key="rel.value" :value="rel.value">
                    {{ rel.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <!-- 值输入 - 仅变量显示 -->
            <div class="space-y-2" v-if="currentSource.itemType === 'variable'">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Value</label>
              <input
                v-model="currentSource.value"
                type="text"
                placeholder="Enter value"
                class="w-full px-3 py-2.5 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200 text-sm placeholder:text-slate-400"
                :disabled="!currentSource.relation"
                @keydown.enter="tryAutoAddSource"
                @blur="tryAutoAddSource"
              />
            </div>
          </div>

          <button
            @click="addSource"
            class="flex items-center gap-2 text-blue-500 font-medium text-sm hover:bg-blue-50 dark:hover:bg-blue-900/20 px-3 py-2 rounded-lg transition-all group"
            :disabled="!canAddSource"
          >
            <span class="material-icons-round text-lg group-hover:scale-110 transition-transform">add_circle_outline</span>
            Add Source
          </button>

          <!-- Sources List -->
          <div v-if="ruleData.sources.length > 0" class="space-y-2">
            <div
              v-for="(source, index) in ruleData.sources"
              :key="index"
              class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600"
            >
              <span class="material-icons-round text-blue-500 text-sm">sensors</span>
              <span class="text-sm text-slate-700 dark:text-slate-200">
                {{ deviceNodes.find(n => n.id === source.fromId)?.label }}
              </span>
              <span class="text-xs text-slate-400">•</span>
              <span class="text-sm font-medium text-blue-600 dark:text-blue-400">
                {{ formatApiLabel(source.fromApi) }}
              </span>
              <span class="text-xs px-1.5 py-0.5 rounded" :class="source.itemType === 'api' ? 'bg-purple-100 text-purple-600 dark:bg-purple-900/30 dark:text-purple-400' : 'bg-green-100 text-green-600 dark:bg-green-900/30 dark:text-green-400'">
                {{ source.itemType || 'api' }}
              </span>
              <!-- 条件和值仅对变量显示 -->
              <template v-if="source.itemType === 'variable'">
                <span class="text-xs text-slate-400">→</span>
                <span class="text-sm font-medium text-orange-600 dark:text-orange-400">
                  {{ relationOptions.find(r => r.value === source.relation)?.label || source.relation || '=' }}
                </span>
                <span class="text-sm text-slate-600 dark:text-slate-300">
                  {{ source.value || '(any)' }}
                </span>
              </template>
              <button
                @click="removeSource(index)"
                class="ml-auto text-red-500 hover:text-red-700 text-sm transition-colors"
              >
                <span class="material-icons-round text-sm">close</span>
              </button>
            </div>
          </div>
        </section>


        <!-- THEN (Action) Section -->
        <section class="space-y-4">
          <div class="flex items-center gap-2 mb-2">
            <span class="bg-emerald-100 dark:bg-emerald-900/30 text-emerald-600 dark:text-emerald-400 text-xs font-bold px-2 py-1 rounded uppercase tracking-wider">
              THEN (Action)
            </span>
            <h2 class="text-sm font-medium text-slate-500 dark:text-slate-400 uppercase tracking-wide">
              Target Device
            </h2>
          </div>

          <div class="grid grid-cols-2 gap-4">
            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Device</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  {{ ruleData.toId ? getDeviceIcon(deviceNodes.find(n => n.id === ruleData.toId)!) : 'sensors' }}
                </span>
                <select
                  v-model="ruleData.toId"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200"
                >
                  <option value="" disabled hidden>Select device</option>
                  <option v-for="node in deviceNodes" :key="node.id" :value="node.id">
                    {{ node.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Action</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  bolt
                </span>
                <select
                  v-model="ruleData.toApi"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200"
                  :disabled="!ruleData.toId"
                >
                  <option value="" disabled hidden>Select action</option>
                  <option v-for="api in availableTargetApis" :key="api" :value="api">
                    {{ formatApiLabel(api) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>
          </div>
        </section>

        <!-- Rule Preview -->
        <div v-if="rulePreview" class="p-6 rounded-2xl bg-slate-50 dark:bg-slate-900/50 border border-dashed border-slate-300 dark:border-slate-600">
          <p class="text-xs font-bold text-slate-400 dark:text-slate-500 uppercase tracking-widest mb-4">Rule Preview</p>
          <div class="flex items-center gap-3 text-sm font-medium text-slate-600 dark:text-slate-300">
            <!-- Source devices with conditions -->
            <div class="flex flex-wrap items-center gap-2">
              <template v-for="(source, index) in rulePreview.sourceConditions" :key="source.fromId + index">
                <div class="flex items-center gap-1 px-2 py-1.5 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600 text-xs">
                  <span class="material-icons-round text-blue-500 text-sm">sensors</span>
                  <span>{{ deviceNodes.find(n => n.id === source.fromId)?.label || 'Unknown' }}</span>
                  <span class="text-slate-400">→</span>
                  <span class="text-blue-600 dark:text-blue-400">{{ formatApiLabel(source.fromApi) }}</span>
                  <span class="text-xs px-1 py-0.5 rounded" :class="source.itemType === 'api' ? 'bg-purple-100 text-purple-600' : 'bg-green-100 text-green-600'">
                    {{ source.itemType || 'api' }}
                  </span>
                  <!-- 条件和值仅对变量显示 -->
                  <template v-if="source.itemType === 'variable'">
                    <span class="text-orange-600 dark:text-orange-400">{{ relationOptions.find(r => r.value === source.relation)?.label.split(' ')[0] || '=' }}</span>
                    <span class="text-slate-700 dark:text-slate-300">{{ source.value || '*' }}</span>
                  </template>
                </div>
                <!-- Add "AND" connector if not the last source -->
                <span v-if="index < rulePreview.sourceConditions.length - 1" class="text-xs font-bold text-slate-400 dark:text-slate-500 px-1">
                  AND
                </span>
              </template>
            </div>

            <!-- Arrow -->
            <span class="material-icons-round text-slate-300 dark:text-slate-500">trending_flat</span>

            <!-- Target device -->
            <div class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600 min-w-[60px] justify-center">
              <span class="material-icons-round text-emerald-500 text-base">{{ getDeviceIcon(rulePreview.target!) }}</span>
              <span>{{ rulePreview.target?.label }}</span>
            </div>

            <!-- Description -->
            <div class="ml-auto text-xs text-slate-400 italic max-w-xs">
              <template v-if="rulePreview.sources.length === 1">
                "If {{ rulePreview.sources[0]?.label }} triggers, then {{ rulePreview.target?.label }} {{ formatApiLabel(rulePreview.action) }}"
              </template>
              <template v-else-if="rulePreview.sources.length === 2">
                "If {{ rulePreview.sources[0]?.label }} and {{ rulePreview.sources[1]?.label }} trigger, then {{ rulePreview.target?.label }} {{ formatApiLabel(rulePreview.action) }}"
              </template>
              <template v-else>
                "If {{ rulePreview.sources[0]?.label }} and {{ rulePreview.sources.length - 1 }} other devices trigger, then {{ rulePreview.target?.label }} {{ formatApiLabel(rulePreview.action) }}"
              </template>
            </div>
          </div>
        </div>
      </div>

      <!-- Footer -->
      <div class="px-8 py-6 bg-slate-50/50 dark:bg-slate-900/20 border-t border-slate-100 dark:border-slate-700 flex justify-end gap-3">
        <button
          @click="handleClose"
          class="px-6 py-2.5 text-sm font-semibold text-slate-600 dark:text-slate-400 hover:bg-slate-100 dark:hover:bg-slate-800 rounded-xl transition-all"
        >
          Cancel
        </button>
        <button
          @click="handleSave"
          class="px-8 py-2.5 text-sm font-semibold text-white bg-blue-500 hover:bg-blue-600 active:scale-95 shadow-lg shadow-blue-500/20 rounded-xl transition-all flex items-center gap-2"
        >
         
          Create Rule
        </button>
      </div>
    </div>
  </div>
</template>

<style scoped>
/* Custom overlay styles */
.fixed.inset-0 {
  animation: fadeIn 0.2s ease-out;
}

@keyframes fadeIn {
  from {
    opacity: 0;
  }
  to {
    opacity: 1;
  }
}

/* Container animation */
.bg-white.dark\:bg-slate-800 {
  animation: slideIn 0.3s ease-out;
}

@keyframes slideIn {
  from {
    opacity: 0;
    transform: scale(0.95) translateY(-10px);
  }
  to {
    opacity: 1;
    transform: scale(1) translateY(0);
  }
}

/* Custom scrollbar for sources list */
.space-y-2::-webkit-scrollbar {
  width: 4px;
}

.space-y-2::-webkit-scrollbar-track {
  background: rgba(241, 245, 249, 0.5);
}

.space-y-2::-webkit-scrollbar-thumb {
  background: #cbd5e1;
  border-radius: 2px;
}

.space-y-2::-webkit-scrollbar-thumb:hover {
  background: #94a3b8;
}

/* Focus styles for selects */
select:focus {
  outline: none;
  box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.1);
}

/* Hide default select dropdown arrow */
select {
  -webkit-appearance: none;
  -moz-appearance: none;
  appearance: none;
  background-image: none;
}

/* Ensure dropdown arrow is positioned correctly */
.select-wrapper {
  position: relative;
}

.select-wrapper .dropdown-arrow {
  position: absolute;
  right: 12px;
  top: 50%;
  transform: translateY(-50%);
  pointer-events: none;
  color: #94a3b8;
  font-size: 18px;
  transition: color 0.2s ease;
}

.select-wrapper:hover .dropdown-arrow {
  color: #64748b;
}

/* Ensure icons are perfectly aligned with select text */
.select-wrapper .select-icon {
  position: absolute;
  left: 12px;
  top: 50%;
  transform: translateY(-50%);
  pointer-events: none;
  font-size: 20px;
  line-height: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  width: 20px;
  height: 20px;
}
</style>
