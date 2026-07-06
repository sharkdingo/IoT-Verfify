<script setup lang="ts">
import { ref, computed } from 'vue'
import type { DeviceNode } from '../types/node'
import type { RuleForm } from '../types/rule'
import type { Specification } from '../types/spec'
import type { DeviceEdge } from '../types/edge'
import { specTemplateDetails } from '../assets/config/specTemplates'
import { useI18n } from 'vue-i18n'

const { t } = useI18n()

// Props
interface Props {
  devices?: DeviceNode[]
  rules?: RuleForm[]
  specifications?: Specification[]
  edges?: DeviceEdge[]
  collapsed?: boolean
  width?: number
  activeSection?: string
}

const props = withDefaults(defineProps<Props>(), {
  devices: () => [],
  rules: () => [],
  specifications: () => [],
  edges: () => [],
  width: 320,
  activeSection: 'devices'
})

// Panel state
const localCollapsed = ref(typeof window !== 'undefined' && window.innerWidth < 768)
type InspectorSection = 'devices' | 'rules' | 'specs'

const localActiveSection = ref<InspectorSection>('devices')

const isInspectorSection = (value?: string): value is InspectorSection =>
  value === 'devices' || value === 'rules' || value === 'specs'

// Emits
const emit = defineEmits<{
  'delete-device': [deviceId: string]
  'delete-rule': [ruleId: string]
  'delete-spec': [specId: string]
  'open-rule-builder': []
  'open-control-section': [section: 'devices' | 'rules' | 'specs']
  'device-click': [deviceId: string]
  'toggle-rule': [ruleId: string, enabled: boolean]
  'update:collapsed': [value: boolean]
  'update:active-section': [value: InspectorSection]
}>()

const isCollapsed = computed({
  get: () => props.collapsed ?? localCollapsed.value,
  set: (value: boolean) => {
    localCollapsed.value = value
    emit('update:collapsed', value)
  }
})

const panelWidth = computed(() => {
  const width = Number.isFinite(props.width) ? props.width : 320
  return `${Math.min(520, Math.max(240, width))}px`
})

const activeSection = computed<InspectorSection>({
  get: () => isInspectorSection(props.activeSection) ? props.activeSection : localActiveSection.value,
  set: (value: InspectorSection) => {
    localActiveSection.value = value
    emit('update:active-section', value)
  }
})

// Convert real device nodes to display format (过滤掉变量节点)
const displayDevices = computed(() => {
  return props.devices
    .filter(device => !device.templateName.startsWith('variable_'))  // 排除变量节点
    .map(device => ({
    id: device.id,
    name: device.label,
    type: device.templateName || t('app.device'),
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
    // 从连线构建规则对象
    sourceRules = props.edges.map(edge => ({
      id: edge.id, // 使用连线 ID 作为规则 ID
      name: t('app.ruleFrom', { source: edge.fromLabel }),
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
      let desc = `${sourceNode?.label || t('app.unknown')}`
      
      // 如果有 itemType、relation、value 信息，显示更完整
      // 兼容 itemType 和 targetType 两种字段名
      const sourceType = s.itemType || s.targetType
      if (sourceType === 'variable' && s.relation && s.value) {
        desc += ` ${s.fromApi} ${getRelationLabel(s.relation)} ${s.value}`
      } else if (sourceType === 'api') {
        desc += ` ${t('app.triggers')} ${s.fromApi}`
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
      name: rule.name || t('app.ruleFrom', { source: (rule.id ? rule.id.replace('rule_', '') : '').split('_')[1] || t('app.unknown') }),
      description: t('app.ifThenDescription', {
        source: sourceDescriptions.join(` ${t('app.and')} `),
        target: targetNode?.label || t('app.unknown'),
        action: rule.toApi || 'N/A'
      }),
      status: t('app.active'),
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
      const aStr = conditionsToString(spec.aConditions)
      return aStr ? `□(${aStr})` : '□A'
    case 'safety':
    case '7': {
      const safeA = conditionsToString(spec.aConditions)
      return safeA ? `□¬((${safeA}) ∧ untrusted)` : '□(untrusted → ¬A)'
    }
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
      return ifStr && thenStr ? `□((${ifStr}) → ○(${thenStr}))` : '□(A → ○B)'
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
      return t('app.noFormulaDefined')
  }
}

// Convert real specifications to display format
const displaySpecs = computed(() => {
  return props.specifications.map(spec => {
    // 优先用后端持久化的 templateLabel（@NotBlank，恒非空）；回退到模板配置；最后 Unknown。
    // 覆盖全部 1-7，避免旧 switch 只处理 1-3 时把 4-7 显示成 "Unknown Property"。
    const specType = spec.templateLabel
      || specTemplateDetails.find(t => t.id === spec.templateId)?.label
      || t('app.unknown')

    const deviceInfo = spec.deviceId ? ` (${spec.deviceLabel || spec.deviceId})` : ` (${t('app.global')})`

    return {
      id: spec.id,
      name: `${specType} ${t('app.property')}${deviceInfo}`,
      formula: generateFormulaFromConditions(spec),
      status: t('app.active'),
      color: 'red' as const, // All specifications use red theme
      deviceId: spec.deviceId,
      deviceLabel: spec.deviceLabel
    }
  })
})

const inspectorTabs = computed(() => [
  {
    id: 'devices' as const,
    label: t('app.devicesTool'),
    icon: 'devices',
    count: displayDevices.value.length
  },
  {
    id: 'rules' as const,
    label: t('app.rulesTool'),
    icon: 'rule',
    count: displayRules.value.length
  },
  {
    id: 'specs' as const,
    label: t('app.specificationsTool'),
    icon: 'fact_check',
    count: displaySpecs.value.length
  }
])

// Methods
const handleDeleteDevice = (deviceId: string) => {
  emit('delete-device', deviceId)
}

const handleDeleteRule = (ruleId: string) => {
  emit('delete-rule', ruleId)
}

const handleAddRule = () => {
  emit('open-control-section', 'rules')
  emit('open-rule-builder')
}

const handleAddDevice = () => {
  emit('open-control-section', 'devices')
}

const handleAddSpec = () => {
  emit('open-control-section', 'specs')
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
    data-testid="system-inspector"
    class="absolute right-0 top-0 bottom-0 glass-panel board-side-panel z-40 flex flex-col border-l transition-all duration-300 ease-in-out"
    :class="isCollapsed ? 'is-collapsed' : 'is-expanded'"
    :style="{ width: isCollapsed ? '3rem' : panelWidth }"
  >
    <div class="board-panel-header relative overflow-hidden p-4 border-b">
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <div class="flex items-center gap-3">
          <div class="p-2 bg-blue-50 rounded-lg border border-blue-100/50 shadow-sm">
            <span class="material-symbols-outlined text-blue-600">fact_check</span>
          </div>
          <div>
            <h2 class="board-panel-title text-sm font-bold leading-none">{{ t('app.systemInspector') }}</h2>
            <p class="board-panel-subtitle text-[10px] font-medium mt-0.5">{{ t('app.currentBoardContent') }}</p>
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
      class="board-panel-body flex-1 overflow-y-auto custom-scrollbar transition-all duration-300"
      :class="isCollapsed ? 'opacity-0 pointer-events-none p-0' : 'p-4 space-y-4'"
    >
      <div
        class="board-segmented grid grid-cols-3 gap-1 rounded-xl border p-1"
        role="tablist"
        :aria-label="t('app.currentBoardContent')"
      >
        <button
          v-for="tab in inspectorTabs"
          :key="tab.id"
          type="button"
          role="tab"
          :data-testid="`inspector-tab-${tab.id}`"
          :aria-selected="activeSection === tab.id"
          :aria-pressed="activeSection === tab.id"
          @click="activeSection = tab.id"
          :class="[
            'min-w-0 rounded-lg px-2 py-2 text-[11px] font-bold transition-all flex items-center justify-start gap-1.5',
            activeSection === tab.id
              ? 'bg-blue-600 text-white shadow-sm'
              : 'text-slate-500 hover:bg-white hover:text-slate-800'
          ]"
        >
          <span class="material-symbols-outlined text-sm" aria-hidden="true">{{ tab.icon }}</span>
          <span class="min-w-0 flex-1 truncate text-left">{{ tab.label }}</span>
          <span
            class="shrink-0 rounded-full px-1.5 py-0.5 text-[10px] leading-none"
            :class="activeSection === tab.id ? 'bg-white/20 text-white' : 'bg-slate-200 text-slate-500'"
          >
            {{ tab.count }}
          </span>
        </button>
      </div>

      <!-- Device List Section -->
      <div v-if="activeSection === 'devices'" data-testid="inspector-section-devices">
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">devices</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">{{ t('app.deviceList') }}</h3>
          </div>
          <button
            type="button"
            data-testid="inspector-add-device"
            @click="handleAddDevice"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.openDeviceCreator')"
            :aria-label="t('app.openDeviceCreator')"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
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

            <div class="relative flex min-w-0 items-center justify-between gap-2">
              <div class="flex min-w-0 items-center gap-3">
                <div class="relative">
                  <div class="w-2.5 h-2.5 rounded-full shadow-sm" :class="device.status === 'online' ? 'bg-green-500' : 'bg-red-500'"></div>
                  <div class="absolute inset-0 w-2.5 h-2.5 rounded-full animate-ping opacity-75" :class="device.status === 'online' ? 'bg-green-400' : 'bg-red-400'"></div>
                </div>
                <span class="min-w-0 truncate text-sm font-semibold text-slate-700 group-hover:text-blue-600 transition-colors" :title="device.name">
                  {{ device.name }}
                </span>
                <span v-if="device.type" class="max-w-[7rem] shrink-0 truncate px-2 py-0.5 rounded-full text-[10px] font-medium bg-slate-100 text-slate-500 border border-slate-200" :title="device.type">
                  {{ device.type }}
                </span>
              </div>
              <button
                @click.stop="handleDeleteDevice(device.id)"
                class="text-slate-300 hover:text-red-500 hover:bg-red-50 transition-all opacity-0 group-hover:opacity-100 p-1.5 rounded-lg"
                :title="t('app.removeDevice')"
              >
                <span class="material-symbols-outlined text-sm">close</span>
              </button>
            </div>
          </div>

          <div v-if="displayDevices.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">devices</span>
            <p class="text-xs mb-3">{{ t('app.noDevicesOnCanvas') }}</p>
            <button
              type="button"
              @click="handleAddDevice"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openDeviceCreator') }}
            </button>
          </div>
        </div>
      </div>

      <!-- Active Global Rules Section -->
      <div v-if="activeSection === 'rules'" data-testid="inspector-section-rules">
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">rule</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">{{ t('app.globalRules') }}</h3>
          </div>
          <button
            type="button"
            data-testid="inspector-add-rule"
            @click="handleAddRule"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.createRule')"
            :aria-label="t('app.createRule')"
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
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm text-blue-600">
                  auto_awesome
                </span>
                <h4 class="min-w-0 truncate text-sm font-bold text-blue-800" :title="rule.name">
                  {{ rule.name }}
                </h4>
              </div>
              
              <!-- 删除规则按钮 -->
              <button
                @click="rule.originalId && handleDeleteRule(rule.originalId)"
                class="text-blue-400 hover:text-red-500 p-1 rounded hover:bg-red-50 transition-all"
                :title="t('app.deleteRule')"
              >
                <span class="material-symbols-outlined text-sm">delete</span>
              </button>
            </div>

            <p class="ml-6 break-words text-[11px] font-medium leading-tight text-blue-600">
              {{ rule.description }}
            </p>
          </div>

          <!-- Empty state when no rules -->
          <div v-if="displayRules.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">rule</span>
            <p class="text-xs mb-3">{{ t('app.noRulesActive') }}</p>
            <button
              type="button"
              @click="handleAddRule"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.createRule') }}
            </button>
          </div>
        </div>
      </div>

      <!-- Specifications Section -->
      <div v-if="activeSection === 'specs'" data-testid="inspector-section-specs">
        <div class="flex items-center justify-between mb-4">
          <div class="flex items-center gap-2">
            <span class="material-symbols-outlined text-slate-400">fact_check</span>
            <h3 class="text-xs font-bold text-slate-500 uppercase tracking-widest">{{ t('app.specifications') }}</h3>
          </div>
          <button
            type="button"
            data-testid="inspector-add-spec"
            @click="handleAddSpec"
            class="text-slate-400 hover:text-blue-600 hover:bg-blue-50 p-1.5 rounded-lg transition-all"
            :title="t('app.openSpecificationCreator')"
            :aria-label="t('app.openSpecificationCreator')"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
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
              <div class="flex min-w-0 items-center gap-2">
                <span class="material-symbols-outlined text-sm text-red-500">warning</span>
                <h4 class="min-w-0 truncate text-sm font-bold text-slate-800" :title="spec.name">
                  {{ spec.name }}
                </h4>
              </div>
              <button
                @click="handleDeleteSpec(spec.id)"
                class="text-slate-300 hover:text-red-500 p-1 rounded hover:bg-red-50 opacity-0 group-hover:opacity-100 transition-all"
                :title="t('app.deleteSpecification')"
              >
                <span class="material-symbols-outlined text-xs">delete</span>
              </button>
            </div>

            <p class="ml-7 block max-w-full overflow-x-auto whitespace-pre-wrap break-all rounded border border-slate-100 bg-slate-50 p-1.5 font-mono text-[11px] leading-tight text-slate-600">
              {{ spec.formula }}
            </p>
          </div>

          <!-- Empty state when no specifications -->
          <div v-if="displaySpecs.length === 0" class="text-center py-6 text-slate-400 border border-dashed border-slate-200 rounded-lg">
            <span class="material-symbols-outlined text-3xl mb-1 block opacity-50">fact_check</span>
            <p class="text-xs mb-3">{{ t('app.noSpecificationsVerified') }}</p>
            <button
              type="button"
              @click="handleAddSpec"
              class="mx-auto inline-flex items-center gap-1.5 rounded-lg bg-blue-600 px-3 py-1.5 text-xs font-bold text-white shadow-sm hover:bg-blue-700"
            >
              <span class="material-symbols-outlined text-sm">add</span>
              {{ t('app.openSpecificationCreator') }}
            </button>
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
