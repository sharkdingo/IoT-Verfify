<script setup lang="ts">
import { ref, reactive, computed } from 'vue'
import { ElMessage } from 'element-plus'

// Props
interface Props {
  deviceTemplates?: any[]
  nodes?: any[]
  edges?: any[]
  canvasPan?: { x: number; y: number }
  canvasZoom?: number
}

const props = withDefaults(defineProps<Props>(), {
  deviceTemplates: () => [],
  nodes: () => [],
  edges: () => [],
  canvasPan: () => ({ x: 0, y: 0 }),
  canvasZoom: 1
})

// Device form data
const deviceForm = reactive({
  name: '',
  type: 'Sensor',
  id: 'AUTO'
})

// Device types
const deviceTypes = ['Sensor', 'Switch', 'Light']

// Specification form data
  const specForm = reactive({
    templateId: '',
    selectedDevices: [] as Array<{deviceId: string, deviceLabel: string, selectedApis: string[]}>,
    formula: ''
  })



const handleCreateDevice = () => {
  console.log('Available templates:', props.deviceTemplates)
  console.log('Selected type:', deviceForm.type)

  if (!deviceForm.name.trim()) {
    ElMessage.warning('Please enter a device name')
    return
  }

  // Find template by type - try to match by name or type
  let template = props.deviceTemplates.find((tpl: any) => tpl.manifest.Name === deviceForm.type)
  if (!template) {
    // Try to find by lowercase name
    template = props.deviceTemplates.find((tpl: any) =>
      tpl.manifest.Name.toLowerCase() === deviceForm.type.toLowerCase()
    )
  }
  if (!template && props.deviceTemplates.length > 0) {
    // If still not found, use the first available template as fallback
    template = props.deviceTemplates[0]
    console.warn(`Template for type "${deviceForm.type}" not found, using fallback:`, template.manifest.Name)
  }
  if (!template) {
    ElMessage.error(`No device templates available. Loaded ${props.deviceTemplates.length} templates.`)
    return
  }

  // Emit device creation event with template
  emit('create-device', {
    template,
    customName: deviceForm.name
  })

  ElMessage.success('Device node added to canvas')

  // Reset form
  deviceForm.name = ''
}

const emit = defineEmits<{
  'create-device': [data: { template: any, customName: string }]
  'open-rule-builder': []
  'add-spec': [data: { templateId: string, formula: string }]
}>()

// Component mounted


const createDevice = () => {
  handleCreateDevice()
}

const openRuleBuilder = () => {
  emit('open-rule-builder')
}

  const selectLTLOperator = (operator: string) => {
    specForm.formula += operator + ' '
  }

  const addDeviceToSpec = (deviceId: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return

    // 检查是否已添加
    if (specForm.selectedDevices.some(d => d.deviceId === deviceId)) {
      ElMessage.warning('Device already added')
      return
    }

    specForm.selectedDevices.push({
      deviceId,
      deviceLabel: device.label,
      selectedApis: []
    })
  }

  const removeDeviceFromSpec = (deviceId: string) => {
    specForm.selectedDevices = specForm.selectedDevices.filter(d => d.deviceId !== deviceId)
  }

  const toggleDeviceApi = (deviceId: string, apiName: string) => {
    const device = specForm.selectedDevices.find(d => d.deviceId === deviceId)
    if (!device) return

    const index = device.selectedApis.indexOf(apiName)
    if (index > -1) {
      device.selectedApis.splice(index, 1)
    } else {
      device.selectedApis.push(apiName)
    }
  }

  const insertVariableIntoFormula = (deviceId: string, apiName: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return

    // 创建变量引用，如: sensor_temp, light_status 等
    const variableName = `${device.label.toLowerCase().replace(/\s+/g, '_')}_${apiName}`
    specForm.formula += variableName + ' '
  }

  // 获取设备可用API列表
  const getDeviceApis = (deviceId: string) => {
    const device = props.nodes.find(d => d.id === deviceId)
    if (!device) return []

    // 这里可以根据设备模板返回不同的API
    // 暂时返回一些常见的API
    return ['status', 'value', 'active', 'temperature', 'humidity', 'motion']
  }

const createSpecification = () => {
  if (!specForm.templateId) {
    ElMessage.warning('Please select a template')
    return
  }

  if (specForm.selectedDevices.length === 0) {
    ElMessage.warning('Please add at least one device to the specification')
    return
  }

  if (!specForm.formula.trim()) {
    ElMessage.warning('Please enter an LTL formula')
    return
  }

  emit('add-spec', {
    templateId: specForm.templateId,
    devices: specForm.selectedDevices,
    formula: specForm.formula
  })

  // Reset form
  specForm.templateId = ''
  specForm.selectedDevices = []
  specForm.formula = ''
}
</script>

<template>
  <aside class="absolute left-0 top-0 bottom-0 w-72 glass-panel z-40 flex flex-col border-r border-slate-200">
    <div class="flex-1 overflow-y-auto custom-scrollbar bg-white">
      <!-- Add Device Section -->
      <details class="group border-b border-slate-100" open>
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-secondary">add_circle</span>
            <span class="text-sm font-semibold text-slate-700">Add Device</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 space-y-3 bg-slate-50/50 pt-2">
          <!-- Device Name -->
          <div>
            <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Device Name</label>
            <input
              v-model="deviceForm.name"
              class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 placeholder:text-slate-400 transition-all shadow-sm"
              placeholder="e.g. Kitchen Sensor"
              type="text"
            />
          </div>

          <!-- Device Type and ID -->
          <div class="grid grid-cols-2 gap-2">
            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Type</label>
              <select
                v-model="deviceForm.type"
                class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-secondary focus:ring-secondary/20 shadow-sm"
              >
                <option v-for="type in deviceTypes" :key="type" :value="type">{{ type }}</option>
              </select>
            </div>

            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">ID</label>
              <input
                v-model="deviceForm.id"
                class="w-full bg-slate-100 border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-500 focus:border-secondary focus:ring-0"
                disabled
                placeholder="AUTO"
                type="text"
              />
            </div>
          </div>

          <!-- Drop Node Button -->
          <button
            @click="createDevice"
            class="w-full py-2 bg-white hover:bg-secondary/[0.03] text-secondary border border-secondary/20 hover:border-secondary/40 rounded-md text-xs font-bold uppercase tracking-wider transition-all mt-2 shadow-sm"
          >
            + Drop Node
          </button>
        </div>
      </details>

      <!-- Rule Lab Section -->
      <details class="group border-b border-slate-100">
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-primary">function</span>
            <span class="text-sm font-semibold text-slate-700">IFTTT Rule</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 grid grid-cols-1 gap-2">
          <!-- Rule Creation Block -->
          <div
            class="flex items-center gap-2 p-3 rounded bg-white border border-blue-200 cursor-pointer hover:bg-blue-50 transition-colors shadow-sm"
            @click="openRuleBuilder"
          >
            <div class="flex flex-col">
              <span class="text-xs font-bold text-blue-700">Create Rule</span>
              <span class="text-[10px] text-slate-500">IF → THEN logic</span>
            </div>
          </div>
        </div>
      </details>

      <!-- Protocol Hub Section -->
      <details class="group border-b border-slate-100">
        <summary class="flex items-center justify-between p-4 cursor-pointer hover:bg-slate-50 transition-colors list-none select-none">
          <div class="flex items-center gap-3">
            <span class="material-symbols-outlined text-lg text-purple-500">schema</span>
            <span class="text-sm font-semibold text-slate-700">Templates</span>
          </div>
          <span class="material-symbols-outlined text-slate-400 transition-transform group-open:rotate-180 text-sm">expand_more</span>
        </summary>

        <div class="px-4 pb-5 bg-slate-50/50 pt-2 space-y-2">
          <p class="text-[10px] text-slate-400 mb-2 font-medium">Linear Temporal Logic (LTL) - Global Specifications</p>

          <div class="flex gap-2 mb-3">
            <!-- Global Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('G')"
            >
              <span class="block text-lg font-bold text-purple-600">G</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Global</span>
            </div>

            <!-- Future Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('F')"
            >
              <span class="block text-lg font-bold text-purple-600">F</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Future</span>
            </div>

            <!-- Next Operator -->
            <div
              class="flex-1 p-2 bg-white border border-slate-200 rounded text-center hover:border-purple-300 hover:shadow-sm cursor-pointer transition-all"
              @click="selectLTLOperator('X')"
            >
              <span class="block text-lg font-bold text-purple-600">X</span>
              <span class="text-[9px] uppercase text-slate-400 font-medium">Next</span>
            </div>
          </div>

            <!-- Specification Creation -->
            <div class="space-y-3">
              <!-- Device Selection -->
              <div>
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Add Devices</label>
                <select
                  @change="addDeviceToSpec($event.target.value); $event.target.value = ''"
                  class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200"
                >
                  <option value="" disabled hidden>Select Device to Add</option>
                  <option
                    v-for="device in props.nodes"
                    :key="device.id"
                    :value="device.id"
                  >
                    {{ device.label }} ({{ device.id }})
                  </option>
                </select>
              </div>

              <!-- Selected Devices with Variables -->
              <div v-if="specForm.selectedDevices.length > 0">
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Selected Devices & Variables</label>
                <div class="space-y-2 max-h-32 overflow-y-auto">
                  <div
                    v-for="device in specForm.selectedDevices"
                    :key="device.deviceId"
                    class="bg-purple-50/50 border border-purple-200 rounded p-2"
                  >
                    <div class="flex items-center justify-between mb-1">
                      <span class="text-xs font-medium text-purple-700">{{ device.deviceLabel }}</span>
                      <button
                        @click="removeDeviceFromSpec(device.deviceId)"
                        class="text-purple-400 hover:text-red-500 text-xs"
                      >
                        ✕
                      </button>
                    </div>
                    <div class="flex flex-wrap gap-1">
                      <button
                        v-for="api in getDeviceApis(device.deviceId)"
                        :key="api"
                        @click="toggleDeviceApi(device.deviceId, api)"
                        :class="[
                          'px-1.5 py-0.5 text-[9px] rounded border transition-colors',
                          device.selectedApis.includes(api)
                            ? 'bg-purple-600 text-white border-purple-600'
                            : 'bg-white text-purple-600 border-purple-300 hover:bg-purple-50'
                        ]"
                      >
                        {{ api }}
                      </button>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Variable Insertion Buttons -->
              <div v-if="specForm.selectedDevices.length > 0">
                <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Insert Variables</label>
                <div class="flex flex-wrap gap-1">
                  <template v-for="device in specForm.selectedDevices" :key="device.deviceId">
                    <button
                      v-for="api in device.selectedApis"
                      :key="`${device.deviceId}-${api}`"
                      @click="insertVariableIntoFormula(device.deviceId, api)"
                      class="px-2 py-1 text-[9px] bg-blue-50 text-blue-700 border border-blue-200 rounded hover:bg-blue-100 transition-colors"
                    >
                      {{ device.deviceLabel.toLowerCase().replace(/\s+/g, '_') }}_{{ api }}
                    </button>
                  </template>
                </div>
              </div>

            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Template</label>
              <select
                v-model="specForm.templateId"
                class="w-full bg-white border border-slate-200 rounded-md px-2 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200"
              >
                <option value="" disabled hidden>Select Template</option>
                <option value="safety">Safety Property</option>
                <option value="liveness">Liveness Property</option>
                <option value="fairness">Fairness Property</option>
              </select>
            </div>

            <div>
              <label class="block text-[10px] uppercase font-bold text-slate-500 mb-1.5">Formula</label>
              <input
                v-model="specForm.formula"
                class="w-full bg-white border border-slate-200 rounded-md px-3 py-2 text-xs text-slate-700 focus:border-purple-300 focus:ring-purple-200 placeholder:text-slate-400"
                placeholder="e.g. G (sensor_temp > 25)"
                type="text"
              />
            </div>

            <button
              @click="createSpecification"
              class="w-full py-2 bg-purple-600 hover:bg-purple-700 text-white border border-purple-600 hover:border-purple-700 rounded-md text-xs font-bold uppercase tracking-wider transition-all"
            >
              Create Specification
            </button>
          </div>
        </div>
      </details>
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

.text-secondary {
  color: #C026D3;
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
