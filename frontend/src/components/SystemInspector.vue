<script setup lang="ts">
import { ref, computed } from 'vue'
import type { DeviceNode } from '../types/node'
import type { RuleForm } from '../types/rule'
import type { Specification } from '../types/spec'
import type { DeviceEdge } from '../types/edge'

// Props
interface Props {
  devices?: DeviceNode[]
  rules?: RuleForm[]
  specifications?: Specification[]
  edges?: DeviceEdge[]
}

const props = withDefaults(defineProps<Props>(), {
  devices: () => [],
  rules: () => [],
  specifications: () => [],
  edges: () => []
})

// Panel state
const isCollapsed = ref(false)

// Emits
const emit = defineEmits<{
  'delete-device': [deviceId: string]
  'delete-rule': [ruleId: string]
  'delete-spec': [specId: string]
  'add-rule': []
  'device-click': [deviceId: string]
  'toggle-rule': [ruleId: string, enabled: boolean]
}>()

// Convert real device nodes to display format (过滤掉变量节点)
const displayDevices = computed(() => {
  return props.devices
    .filter(device => !device.templateName.startsWith('variable_'))  // 排除变量节点
    .map(device => ({
    id: device.id,
    name: device.label,
    type: device.templateName || 'Device',
    status: 'online' as const // Simplified - in real app, this would come from device state
  }))
})

// 关系代码转可读标签
const getRelationLabel = (relation: string): string => {
  const relationMap: Record<string, string> = {
    'EQ': '=',
    'NEQ': '≠',
    'GT': '>',
    'GTE': '≥',
    'LT': '<',
    'LTE': '≤'
  }
  return relationMap[relation] || relation
}

// Convert real rules to display format
const displayRules = computed(() => {
  // 优先使用 rules，如果为空则尝试从 edges 转换
  let sourceRules = props.rules

  if ((!sourceRules || sourceRules.length === 0) && props.edges && props.edges.length > 0) {
    console.log('⚠️ [SystemInspector] 规则为空，正在从连线恢复规则数据...')
    // 从连线构建规则对象
    sourceRules = props.edges.map(edge => ({
      id: edge.id, // 使用连线 ID 作为规则 ID
      name: `Rule from ${edge.fromLabel}`,
      sources: [{ 
        fromId: edge.from, 
        fromApi: edge.fromApi || '',
        itemType: edge.itemType,
        relation: edge.relation,
        value: edge.value
      }],
      toId: edge.to,
      toApi: edge.toApi || ''
    }))
  }

  return sourceRules.map(rule => {
    const targetNode = props.devices.find(d => d.id === rule.toId)
    
    // 构建更详细的源设备描述
    const sourceDescriptions = rule.sources.map(s => {
      const sourceNode = props.devices.find(d => d.id === s.fromId)
      let desc = `${sourceNode?.label || 'Unknown'}`
      
      // 如果有 itemType、relation、value 信息，显示更完整
      // 兼容 itemType 和 targetType 两种字段名
      const sourceType = s.itemType || s.targetType
      if (sourceType === 'variable' && s.relation && s.value) {
        desc += ` ${s.fromApi} ${getRelationLabel(s.relation)} ${s.value}`
      } else if (sourceType === 'api') {
        desc += ` triggers ${s.fromApi}`
      } else {
        // 如果有 relation 和 value，也显示
        if (s.relation && s.value) {
          desc += ` ${s.fromApi} ${getRelationLabel(s.relation)} ${s.value}`
        } else {
          desc += ` ${s.fromApi}`
        }
      }
      return desc
    })

    return {
      originalId: rule.id, // 保留原始id用于删除操作
      id: rule.id ? rule.id.replace('rule_', '') : 'unknown',
      name: rule.name || `Rule ${(rule.id ? rule.id.replace('rule_', '') : '').split('_')[1] || 'unknown'}`,
      description: `IF ${sourceDescriptions.join(' AND ')} THEN ${targetNode?.label || 'Unknown'} triggers ${rule.toApi || 'N/A'}`,
      status: 'Active' as const,
      color: 'blue' as const,
      enabled: true // Add enabled status
    }
  })
})

// Helper function to generate formula from conditions if not already defined
const generateFormulaFromConditions = (spec: any): string => {
  // If formula already exists, use it
  if (spec.formula && spec.formula !== 'No formula defined') {
    return spec.formula
  }

  // Generate from conditions based on templateId
  const conditionsToString = (conditions: any[] = []) => {
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

  switch (spec.templateId) {
    case 'always':
    case '1':
    case 'safety':
      const aStr = conditionsToString(spec.aConditions)
      return aStr ? `□(${aStr})` : '□A'
    case 'eventually':
    case '2':
    case 'liveness':
      const evA = conditionsToString(spec.aConditions)
      return evA ? `◇(${evA})` : '◇A'
    case 'never':
    case '3':
    case 'fairness':
      const neverA = conditionsToString(spec.aConditions)
      return neverA ? `□¬(${neverA})` : '□¬A'
    case 'immediate':
    case '4':
      const ifStr = conditionsToString(spec.ifConditions)
      const thenStr = conditionsToString(spec.thenConditions)
      return ifStr && thenStr ? `□((${ifStr}) → (${thenStr}))` : '□(A → B)'
    case 'response':
    case '5':
      const respIf = conditionsToString(spec.ifConditions)
      const respThen = conditionsToString(spec.thenConditions)
      return respIf && respThen ? `□((${respIf}) → ◇(${respThen}))` : '□(A → ◇B)'
    case 'persistence':
    case '6':
      const persIf = conditionsToString(spec.ifConditions)
      const persThen = conditionsToString(spec.thenConditions)
      return persIf && persThen ? `□((${persIf}) → □(${persThen}))` : '□(A → □B)'
    default:
      return 'No formula defined'
  }
}

// Convert real specifications to display format
const displaySpecs = computed(() => {
  return props.specifications.map(spec => {
    let specType = 'Unknown'

    // Handle both string and number templateId
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

    const deviceInfo = spec.deviceId ? ` (${spec.deviceLabel || spec.deviceId})` : ' (Global)'

    return {
      id: spec.id,
      name: `${specType} Property${deviceInfo}`,
      formula: generateFormulaFromConditions(spec),
      status: 'Active' as const,
      color: 'red' as const, // All specifications use red theme
      deviceId: spec.deviceId,
      deviceLabel: spec.deviceLabel
    }
  })
})

// Methods
const handleDeleteDevice = (deviceId: string) => {
  emit('delete-device', deviceId)
}

const handleDeleteRule = (ruleId: string) => {
  emit('delete-rule', ruleId)
}

const handleAddRule = () => {
  emit('add-rule')
}

const handleDeviceClick = (deviceId: string) => {
  emit('device-click', deviceId)
}

const handleDeleteSpec = (specId: string) => {
  emit('delete-spec', specId)
}

const togglePanel = () => {
  isCollapsed.value = !isCollapsed.value
}
</script>

<template>
  <aside
    class="absolute right-0 top-0 bottom-0 glass-panel z-40 flex flex-col border-l border-slate-200 transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'w-12' : 'w-80'"
  >
    <div class="relative overflow-hidden p-4 bg-white border-b border-slate-200">
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <div class="flex items-center gap-3">
          <div class="p-2 bg-blue-50 rounded-lg border border-blue-100/50 shadow-sm">
            <span class="material-symbols-outlined text-blue-600">fact_check</span>
          </div>
          <div>
            <h2 class="text-sm font-bold text-slate-800 leading-none">System Inspector</h2>
            <p class="text-[10px] text-slate-500 font-medium mt-0.5">Device Management</p>
          </div>
        </div>
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-800 hover:bg-slate-100 p-1.5 rounded-lg transition-all"
        >
        <span class="material-symbols-outlined text-base">dock_to_left</span>
        </button>
      </div>
      <div v-else class="flex items-center justify-center p-1">
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-800 hover:bg-slate-100 p-1.5 rounded-lg transition-all"
        >
          <span class="material-symbols-outlined text-base">dock_to_left</span>
        </button>
      </div>
    </div>

    <div
      class="flex-1 overflow-y-auto custom-scrollbar bg-white transition-all duration-300"
      :class="isCollapsed ? 'opacity-0 pointer-events-none p-0' : 'p-5 space-y-6'"
    >
      <!-- Device List Section -->
      <div>
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">devices</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">Device List</h3>
          </div>
        </div>

        <div class="space-y-2.5">
          <div
            v-for="device in displayDevices"
            :key="device.id"
            @click="handleDeviceClick(device.id)"
            class="group relative p-4 rounded-xl bg-white border border-slate-200/60 hover:border-blue-300/50 shadow-sm hover:shadow-md transition-all cursor-pointer overflow-hidden"
          >
            <!-- Hover gradient background -->
            <div class="absolute inset-0 bg-gradient-to-r from-blue-50/0 to-indigo-50/0 opacity-0 group-hover:opacity-100 transition-opacity duration-300"></div>

            <div class="relative flex items-center justify-between">
              <div class="flex items-center gap-3">
                <div class="relative">
                  <div class="w-2.5 h-2.5 rounded-full shadow-sm" :class="device.status === 'online' ? 'bg-green-500' : 'bg-red-500'"></div>
                  <div class="absolute inset-0 w-2.5 h-2.5 rounded-full animate-ping opacity-75" :class="device.status === 'online' ? 'bg-green-400' : 'bg-red-400'"></div>
                </div>
                <span class="text-sm font-semibold text-slate-700 group-hover:text-blue-600 transition-colors">
                  {{ device.name }}
                </span>
                <span v-if="device.type" class="px-2 py-0.5 rounded-full text-[10px] font-medium bg-slate-100 text-slate-500 border border-slate-200">
                  {{ device.type }}
                </span>
              </div>
              <button
                @click.stop="handleDeleteDevice(device.id)"
                class="text-slate-300 hover:text-red-500 hover:bg-red-50 transition-all opacity-0 group-hover:opacity-100 p-1.5 rounded-lg"
                title="Remove device"
              >
                <span class="material-symbols-outlined text-sm">close</span>
              </button>
            </div>
          </div>
        </div>
      </div>

      <!-- Active Global Rules Section -->
      <div>
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">rule</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">Global Rules</h3>
          </div>
          <button
            @click="handleAddRule"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
        </div>

        <div class="space-y-3">
          <div
            v-for="rule in displayRules"
            :key="rule.id"
            class="p-3 rounded-lg border relative overflow-hidden transition-all hover:shadow-md group bg-blue-50 border-blue-200 hover:border-blue-400"
          >
            <!-- 蓝色背景装饰 -->
            <div class="absolute left-0 top-0 bottom-0 w-1 bg-blue-500 rounded-l-lg"></div>
            
            <div class="flex items-start justify-between mb-2">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-sm text-blue-600">
                  auto_awesome
                </span>
                <h4 class="text-sm font-bold text-blue-800">
                  {{ rule.name }}
                </h4>
              </div>
              
              <!-- 删除规则按钮 -->
              <button
                @click="rule.originalId && handleDeleteRule(rule.originalId)"
                class="text-blue-400 hover:text-red-500 p-1 rounded hover:bg-red-50 transition-all"
                title="Delete rule"
              >
                <span class="material-symbols-outlined text-sm">delete</span>
              </button>
            </div>

            <p class="text-[11px] text-blue-600 leading-tight font-medium ml-6">
              {{ rule.description }}
            </p>
          </div>

          <!-- Empty state when no rules -->
          <div v-if="displayRules.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">rule</span>
            <p class="text-xs">No rules active</p>
          </div>
        </div>
      </div>

      <!-- Specifications Section -->
      <div>
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">verified</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">Specifications</h3>
          </div>
        </div>

        <div class="space-y-3">
          <div
            v-for="spec in displaySpecs"
            :key="spec.id"
            class="p-3 rounded-lg border border-red-100 relative overflow-hidden transition-all hover:shadow-md bg-white group"
          >
            <!-- Subtle background pulse -->
            <div class="absolute inset-0 bg-red-50/30 pointer-events-none"></div>

            <div class="relative flex items-start justify-between mb-2">
              <div class="flex items-center gap-2">
                <span class="material-symbols-outlined text-sm text-red-500">warning</span>
                <h4 class="text-sm font-bold text-slate-800">
                  {{ spec.name }}
                </h4>
              </div>
              <button
                @click="handleDeleteSpec(spec.id)"
                class="text-slate-300 hover:text-red-500 p-1 rounded hover:bg-red-50 opacity-0 group-hover:opacity-100 transition-all"
                title="Delete specification"
              >
                <span class="material-symbols-outlined text-xs">delete</span>
              </button>
            </div>

            <p class="text-[11px] text-slate-600 leading-tight font-mono ml-7 bg-slate-50 p-1.5 rounded border border-slate-100 inline-block">
              {{ spec.formula }}
            </p>
          </div>

          <!-- Empty state when no specifications -->
          <div v-if="displaySpecs.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">verified</span>
            <p class="text-xs">No specifications verified</p>
          </div>
        </div>
      </div>
    </div>
  </aside>
</template>

<style scoped>
/* Glass panel effect */
.glass-panel {
  background: rgba(255, 255, 255, 0.7);
  backdrop-filter: blur(16px);
  border: 1px solid rgba(226, 232, 240, 0.8);
}

/* Custom scrollbar */
.custom-scrollbar::-webkit-scrollbar {
  width: 4px;
}

.custom-scrollbar::-webkit-scrollbar-track {
  background: rgba(0, 0, 0, 0.02);
}

.custom-scrollbar::-webkit-scrollbar-thumb {
  background: rgba(0, 0, 0, 0.1);
  border-radius: 10px;
}

.custom-scrollbar::-webkit-scrollbar-thumb:hover {
  background: rgba(0, 0, 0, 0.2);
}

/* Utility classes */
.text-primary {
  color: #2563EB;
}

.bg-online {
  background-color: #059669;
}

.bg-offline {
  background-color: #dc2626;
}

/* Material Symbols font */
.material-symbols-outlined {
  font-family: 'Material Symbols Outlined';
}
</style>
