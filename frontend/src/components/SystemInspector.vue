<script setup lang="ts">
import { ref, computed } from 'vue'
import type { DeviceNode } from '../types/node'
import type { RuleForm } from '../types/rule'
import type { Specification } from '../types/spec'

// Props
interface Props {
  devices?: DeviceNode[]
  rules?: RuleForm[]
  specifications?: Specification[]
}

const props = withDefaults(defineProps<Props>(), {
  devices: () => [],
  rules: () => [],
  specifications: () => []
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

// Computed
const activeDevicesCount = computed(() => props.devices.length)
const activeSpecsCount = computed(() => props.specifications.length)

// Convert real device nodes to display format
const displayDevices = computed(() => {
  return props.devices.map(device => ({
    id: device.id,
    name: device.label,
    status: 'online' as const // Simplified - in real app, this would come from device state
  }))
})

// Convert real rules to display format
const displayRules = computed(() => {
  return props.rules.map(rule => {
    const targetNode = props.devices.find(d => d.id === rule.toId)
    const sourceNodes = rule.sources.map(s => props.devices.find(d => d.id === s.fromId)?.label).filter(Boolean)

    return {
      id: rule.id || 'unknown',
      name: rule.name || `Rule ${(rule.id || '').split('_')[1] || 'unknown'}`,
      description: `IF ${sourceNodes.join(' AND ')} THEN ${targetNode?.label} ${rule.toApi}`,
      status: 'Active' as const,
      color: 'blue' as const,
      enabled: true // Add enabled status
    }
  })
})

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
      formula: spec.formula || 'No formula defined',
      status: 'Active' as const,
      color: 'red' as const, // All specifications use red theme
      deviceId: spec.deviceId,
      deviceLabel: spec.deviceLabel
    }
  })
})

// Methods
const getDeviceIcon = (device: any) => {
  const icons = {
    online: 'check_circle',
    offline: 'cancel'
  }
  return icons[device.status as keyof typeof icons] || 'help'
}

const getDeviceColor = (device: any) => {
  return device.status === 'online' ? 'bg-online' : 'bg-offline'
}

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

const handleToggleRule = (ruleId: string) => {
  // Find current rule status and toggle it
  const rule = displayRules.value.find(r => r.id === ruleId)
  if (rule) {
    const newEnabled = !rule.enabled
    emit('toggle-rule', ruleId, newEnabled)
  }
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
    <div class="p-3 border-b border-slate-100 bg-white/50 flex items-center justify-center">
      <div v-if="!isCollapsed" class="flex items-center justify-between w-full">
        <h2 class="text-xs font-bold uppercase tracking-[0.2em] text-slate-500">System Inspector</h2>
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-700 transition-colors"
        >
          <span class="material-symbols-outlined text-lg transition-transform duration-200">dock_to_right</span>
        </button>
      </div>
      <div v-else class="flex items-center justify-center p-1">
        <button
          @click="togglePanel"
          class="text-slate-400 hover:text-slate-700 transition-colors p-1 rounded hover:bg-white/20"
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
        <div class="flex items-center justify-between mb-3">
          <h3 class="text-xs font-bold text-slate-400 uppercase tracking-widest">Device List</h3>
        </div>

        <div class="space-y-2">
          <div
            v-for="device in displayDevices"
            :key="device.id"
            @click="handleDeviceClick(device.id)"
            class="flex items-center justify-between p-3 rounded-xl bg-white border border-slate-100 hover:bg-slate-50 hover:border-primary/30 transition-all cursor-pointer group shadow-sm"
          >
            <div class="flex items-center gap-3">
              <div class="size-2 rounded-full shadow-sm bg-green-500"></div>
              <span class="text-sm font-medium text-slate-700 group-hover:text-primary transition-colors">
                {{ device.name }}
              </span>
            </div>
            <button
              @click.stop="handleDeleteDevice(device.id)"
              class="text-red-500 hover:text-red-700 transition-colors opacity-0 group-hover:opacity-100"
            >
              <span class="material-symbols-outlined text-sm">delete</span>
            </button>
          </div>
        </div>
      </div>

      <!-- Active Global Rules Section -->
      <div>
        <div class="flex items-center justify-between mb-3">
          <h3 class="text-xs font-bold text-slate-400 uppercase tracking-widest">Active Global Rules</h3>
          <button
            @click="handleAddRule"
            class="text-primary hover:text-primary/70 transition-colors"
          >
            <span class="material-symbols-outlined text-sm">add</span>
          </button>
        </div>

        <div class="space-y-3">
          <div
            v-for="rule in displayRules"
            :key="rule.id"
            :class="[
              'p-3 rounded-xl border relative overflow-hidden shadow-sm',
              rule.color === 'blue'
                ? 'bg-blue-50/50 border-blue-100'
                : 'bg-purple-50/50 border-purple-100'
            ]"
          >
            <!-- Background icon -->
            <div class="absolute right-0 top-0 p-2 opacity-10">
              <span
                class="material-symbols-outlined text-4xl"
                :class="rule.color === 'blue' ? 'text-blue-600' : 'text-purple-600'"
              >
                {{ rule.color === 'blue' ? 'nightlight' : 'thermostat_auto' }}
              </span>
            </div>

            <!-- Rule content -->
            <h4 :class="[
              'text-sm font-bold mb-1',
              rule.color === 'blue' ? 'text-blue-700' : 'text-purple-700'
            ]">
              {{ rule.name }}
            </h4>

            <p class="text-[11px] text-slate-600 leading-tight font-medium mb-2">
              {{ rule.description }}
            </p>

            <div class="flex items-center justify-between">
              <div class="flex items-center gap-2">
                <span :class="[
                  'px-1.5 py-0.5 rounded text-[9px] font-bold uppercase border shadow-sm',
                  rule.color === 'blue'
                    ? 'bg-white text-blue-600 border-blue-200'
                    : 'bg-white text-purple-600 border-purple-200'
                ]">
                  {{ rule.status }}
                </span>

                <!-- Rule toggle switch -->
                <label class="relative inline-flex items-center cursor-pointer">
                  <input
                    type="checkbox"
                    :checked="rule.enabled"
                    @change="rule.id && handleToggleRule(rule.id)"
                    class="sr-only peer"
                  >
                  <div class="w-8 h-4 bg-slate-300 peer-focus:outline-none peer-focus:ring-2 peer-focus:ring-blue-300 rounded-full peer peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:rounded-full after:h-3 after:w-3 after:transition-all peer-checked:bg-blue-500"></div>
                </label>
              </div>

              <button
                @click="rule.id && handleDeleteRule(rule.id)"
                class="text-slate-400 hover:text-red-500 transition-colors p-1 rounded"
                title="Delete rule"
              >
                <span class="material-symbols-outlined text-sm">delete</span>
              </button>
            </div>
          </div>

          <!-- Empty state when no rules -->
          <div v-if="displayRules.length === 0" class="text-center py-8 text-slate-400">
            <span class="material-symbols-outlined text-4xl mb-2 block">rule</span>
            <p class="text-sm">No rules created yet</p>
            <p class="text-xs">Drag IF/THEN blocks from the left panel to create rules</p>
          </div>
        </div>
      </div>

      <!-- Specifications Section -->
      <div>
        <div class="flex items-center justify-between mb-3">
          <h3 class="text-xs font-bold text-slate-400 uppercase tracking-widest">Specifications</h3>
          <span class="text-[10px] bg-slate-100 px-1.5 py-0.5 rounded text-slate-500 font-medium border border-slate-200">
            {{ activeSpecsCount }} Active
          </span>
        </div>

        <div class="space-y-3">
          <div
            v-for="spec in displaySpecs"
            :key="spec.id"
            class="p-3 rounded-xl border relative overflow-hidden shadow-sm bg-red-50/50 border-red-100"
          >
            <!-- Background icon -->
            <div class="absolute right-0 top-0 p-2 opacity-10">
              <span class="material-symbols-outlined text-4xl text-red-600">
                warning
              </span>
            </div>

            <!-- Spec content -->
            <h4 class="text-sm font-bold mb-1 text-red-700">
              {{ spec.name }}
            </h4>

            <p class="text-[11px] text-slate-600 leading-tight font-medium mb-2 font-mono">
              {{ spec.formula }}
            </p>

            <div class="flex items-center justify-between">
              <span class="px-1.5 py-0.5 rounded text-[9px] font-bold uppercase border shadow-sm bg-white text-red-600 border-red-200">
                {{ spec.status }}
              </span>

              <button
                @click="handleDeleteSpec(spec.id)"
                class="text-slate-400 hover:text-red-500 transition-colors p-1 rounded"
                title="Delete specification"
              >
                <span class="material-symbols-outlined text-sm">delete</span>
              </button>
            </div>
          </div>

          <!-- Empty state when no specifications -->
          <div v-if="displaySpecs.length === 0" class="text-center py-8 text-slate-400">
            <span class="material-symbols-outlined text-4xl mb-2 block">description</span>
            <p class="text-sm">No specifications created yet</p>
            <p class="text-xs">Use the Templates panel on the left to create LTL specifications</p>
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
