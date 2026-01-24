<script setup lang="ts">
import { ref, reactive, computed, watch } from 'vue'
import { ElMessage } from 'element-plus'
import type { DeviceNode } from '../types/node'
import type { RuleForm } from '../types/rule'

// Props
interface Props {
  modelValue: boolean
  nodes: DeviceNode[]
}

const props = withDefaults(defineProps<Props>(), {
  modelValue: false,
  nodes: () => []
})

// Emits
const emit = defineEmits<{
  'update:modelValue': [value: boolean]
  'save-rule': [rule: RuleForm]
}>()

// Rule data
const ruleData = reactive<RuleForm>({
  id: '',
  sources: [],
  toId: '',
  toApi: ''
})

// Current source being added
const currentSource = reactive({
  fromId: '',
  fromApi: ''
})

// Available APIs (mock data - in real app, this would come from device templates)
const availableApis = {
  sensor: ['temperature', 'humidity', 'motion', 'light_level'],
  switch: ['turn_on', 'turn_off', 'toggle', 'status'],
  light: ['brightness', 'color', 'turn_on', 'turn_off']
}

const availableTargetApis = computed(() => {
  if (!ruleData.toId) return []
  const targetNode = props.nodes.find(n => n.id === ruleData.toId)
  if (!targetNode) return []

  // Get device type from template name (simplified)
  const deviceType = targetNode.templateName.toLowerCase()
  if (deviceType.includes('sensor')) return availableApis.sensor
  if (deviceType.includes('switch')) return availableApis.switch
  if (deviceType.includes('light')) return availableApis.light
  return []
})

const availableSourceApis = computed(() => {
  if (!currentSource.fromId) return []
  const sourceNode = props.nodes.find(n => n.id === currentSource.fromId)
  if (!sourceNode) return []

  // Get device type from template name (simplified)
  const deviceType = sourceNode.templateName.toLowerCase()
  if (deviceType.includes('sensor')) return availableApis.sensor
  if (deviceType.includes('switch')) return availableApis.switch
  if (deviceType.includes('light')) return availableApis.light
  return []
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
    target: targetNode,
    action: ruleData.toApi
  }
})

// Methods
const addSource = () => {
  // Just reset current source for adding another one
  currentSource.fromId = ''
  currentSource.fromApi = ''
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
  ruleData.sources = []
  ruleData.toId = ''
  ruleData.toApi = ''
  currentSource.fromId = ''
  currentSource.fromApi = ''

  emit('update:modelValue', false)
}

// Watch for auto-add source when both device and API are selected
watch(
  () => [currentSource.fromId, currentSource.fromApi],
  ([newFromId, newFromApi]) => {
    if (newFromId && newFromApi) {
      // Auto-add the source when both are selected
      const exists = ruleData.sources.some(s =>
        s.fromId === newFromId && s.fromApi === newFromApi
      )

      if (!exists) {
        ruleData.sources.push({
          fromId: newFromId,
          fromApi: newFromApi
        })

        // Reset current source for next addition
        currentSource.fromId = ''
        currentSource.fromApi = ''
      }
    }
  },
  { immediate: false }
)

// Helper functions for UI
const getDeviceIcon = (node: DeviceNode) => {
  const deviceType = node.templateName.toLowerCase()
  if (deviceType.includes('sensor')) return 'sensors'
  if (deviceType.includes('switch')) return 'toggle'
  if (deviceType.includes('light')) return 'lightbulb'
  return 'device_unknown'
}

const getApiIcon = (api: string) => {
  if (api.includes('motion') || api.includes('temperature') || api.includes('humidity')) return 'api'
  if (api.includes('turn_on') || api.includes('turn_off')) return 'bolt'
  return 'settings'
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
          <div class="grid grid-cols-2 gap-4">
            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">Device</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  {{ currentSource.fromId ? getDeviceIcon(nodes.find(n => n.id === currentSource.fromId)!) : 'sensors' }}
                </span>
                <select
                  v-model="currentSource.fromId"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200"
                >
                  <option value="" disabled hidden>Select device</option>
                  <option v-for="node in nodes" :key="node.id" :value="node.id">
                    {{ node.label }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>

            <div class="space-y-2">
              <label class="text-xs font-semibold text-slate-500 dark:text-slate-400 ml-1">API / Condition</label>
              <div class="relative group select-wrapper">
                <span class="material-icons-round select-icon text-slate-400 group-focus-within:text-blue-500 transition-colors">
                  {{ currentSource.fromApi ? getApiIcon(currentSource.fromApi) : 'api' }}
                </span>
                <select
                  v-model="currentSource.fromApi"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200"
                  :disabled="!currentSource.fromId"
                >
                  <option value="" disabled hidden>Select API</option>
                  <option v-for="api in availableSourceApis" :key="api" :value="api">
                    {{ formatApiLabel(api) }}
                  </option>
                </select>
                <span class="material-icons-round dropdown-arrow">expand_more</span>
              </div>
            </div>
          </div>

          <button
            @click="addSource"
            class="flex items-center gap-2 text-blue-500 font-medium text-sm hover:bg-blue-50 dark:hover:bg-blue-900/20 px-3 py-2 rounded-lg transition-all group"
            :disabled="!currentSource.fromId && !currentSource.fromApi"
          >
            <span class="material-icons-round text-lg group-hover:scale-110 transition-transform">add_circle_outline</span>
            Add Another Source
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
                {{ nodes.find(n => n.id === source.fromId)?.label }}
              </span>
              <span class="text-xs text-slate-400">•</span>
              <span class="text-sm font-medium text-blue-600 dark:text-blue-400">
                {{ formatApiLabel(source.fromApi) }}
              </span>
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
                  {{ ruleData.toId ? getDeviceIcon(nodes.find(n => n.id === ruleData.toId)!) : 'sensors' }}
                </span>
                <select
                  v-model="ruleData.toId"
                  class="w-full pl-10 pr-10 py-3 bg-slate-50 dark:bg-slate-800/50 border border-slate-200 dark:border-slate-600 rounded-xl focus:ring-2 focus:ring-blue-500/20 focus:border-blue-500 transition-all text-slate-700 dark:text-slate-200"
                >
                  <option value="" disabled hidden>Select device</option>
                  <option v-for="node in nodes" :key="node.id" :value="node.id">
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
            <!-- Source devices -->
            <div class="flex items-center gap-2">
              <template v-for="(source, index) in rulePreview.sources" :key="source.id">
                <div class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600">
                  <span class="material-icons-round text-blue-500 text-base">{{ getDeviceIcon(source) }}</span>
                  <span>{{ source.label }}</span>
                </div>
                <!-- Add "AND" connector if not the last source -->
                <span v-if="index < rulePreview.sources.length - 1" class="text-xs font-bold text-slate-400 dark:text-slate-500 px-2 py-1 bg-slate-200 dark:bg-slate-600 rounded">
                  AND
                </span>
              </template>
            </div>

            <!-- Arrow -->
            <span class="material-icons-round text-slate-300 dark:text-slate-500">trending_flat</span>

            <!-- Target device -->
            <div class="flex items-center gap-2 px-3 py-2 rounded-lg bg-white dark:bg-slate-700 border border-slate-200 dark:border-slate-600">
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
